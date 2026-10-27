import NumlibSurface.CartisGouldToint.Chapter14.Section03Anchored

/-!
# Cartis–Gould–Toint §14.3: Theorem 14.3.9 for TPqp-GC runs with a regularization INNER

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], Theorem 14.3.9 (complexity of
TPqp-GC, Algorithm 14.3.2) when INNER is of regularization type. The theorem is proved for
**every** run whose INNER calls are genuine runs (not only for constructed runs), under the book's
assumptions c.D1pLB.X, f.D1pLB.X and f.B.Fb, with constants chosen before the tolerances `ε₀`,
`ε`, as printed. Two run classes are treated:

* `IsTPqpGCARqpSCRun`: INNER = ARqp-SC on a general `X`, run as ARqpC-SC (Algorithm 14.1.1) with
  `c = 0`, `h = 0`, i.e. ARqp with Step 2 by Algorithm 14.1.2 (the library's realization of
  INNER in §14.3; the book's ARqpC presumes `h ≠ 0`, OCR l. 15581, so for these runs ARqpC-SC
  and ARqp-SC are two analyses of one algorithm). Two rows of (14.2.12) apply to them: the
  ARqpC-SC row `π_j = j + 1` (the entry for `h` nonconvex or `q ≥ 2`; for `q = 1` with `h = 0` and
  `X` convex the ARqpC-SC entry is `(p+1)/p`), and the ARqp-SC row `π_j = j(p+1)/p` ("otherwise").
* `IsTPqpGCARqpUnitRun`: `X = ℝⁿ`, INNER = ARqp of Chapter 12 with Step 2 by Algorithm 12.2.3,
  which keeps unit radii for `q ≤ 2` (Lemma 12.2.9), with the exponents `(p+1)/(p-j+1)`. (Table
  (14.2.12) keys its unit-radius ARqp-SC entry as "`q = 1`, `X` convex"; `ℝⁿ` with `q ≤ 2` is the
  regime of Chapter 12.)

For a nonspecific INNER the printed theorem is vacuous or false (`Chapter14.Section03BadIter`). For
genuine calls, every Phase-2 run satisfies the INNER contract keyed on INNER's own test
(`IsInnerPhaseRunStrong`) with `t`-independent constants: unsuccessful steps do not move, the
number of iterations of a call is bounded by Lemma 14.2.3, every successful step not followed by
a Step-1 termination decreases `μ(·, t_k)` by Lemma 14.2.2 (a call ending at a point failing
INNER's test has no Step-1 termination there), and the returned radii are at least `κ_ρ ε'_j` by
the radius policy of Algorithm 14.1.2, which holds at every iteration of every run (radii `1`
for the unit class). Then `IsTPqpGCPhase2.complexity_of_strong` bounds Phase 2, with the extra
term `O(ε₀^{-1} + max_j (ε₀ ε_j ρ_j^{j-1})^{-1})` for the case-(b) iterations ending at a point
passing INNER's test; `ρ_j ∼ ε₀ ε_j` (radius policy) or `ρ_j = 1` (unit radii).

## Main definitions

* `IsARqpSCCallOut` (with `jetBound`), `IsARqpSCPhase2Calls`, `IsTPqpGCARqpSCRun`: TPqp-GC runs
  whose INNER calls in both phases are ARqp-SC runs (ARqpC-SC with `c = 0`, `h = 0`), the
  Phase-2 calls with their output radii and cut at any iteration by any test of (14.3.32);
* `IsARqpUnitCallOut`, `IsARqpUnitPhase2Calls`, `IsTPqpGCARqpUnitRun`: the same on `X = ℝⁿ` with
  INNER = ARqp of Chapter 12 with unit radii (Step 2 by Algorithm 12.2.3);
* `tpqpOrderF`, `tpqpOrderD`: the printed orders `max[ε₀^{-1}, max_j ε₀^{1-π_j} ε_j^{-π_j}]` and
  `max_j ε₀^{1-π_j} ε_j^{-π_j}`.

## Main results

* `IsARqpSCCallOut.contract`, `IsARqpSCPhase2Calls.isInnerPhaseRunStrong` (exponents `j + 1`),
  `IsARqpSCPhase2Calls.isInnerPhaseRunStrong_arqp` (ARqp-SC exponents),
  `IsARqpUnitCallOut.contract`, `IsARqpUnitPhase2Calls.isInnerPhaseRunStrong` (unit radii): the
  INNER contract for every run;
* `IsTPqpGCPhase2.exists_const_order_of_strong`: from the contract to an order bound for Phase 2;
* `theorem_14_3_9_arqpc`: Theorem 14.3.9 with the exponents `π_j = j + 1` for every run of
  `IsTPqpGCARqpSCRun` and every `1 ≤ q ≤ p`: `O(max[ε₀^{-1}, max_j ε₀^{-j} ε_j^{-(j+1)}])`
  evaluations of `(f, c)` and `O(max_j ε₀^{-j} ε_j^{-(j+1)})` derivative evaluations (the
  bad-iteration term `(ε₀ ε_j)^{-j} ≤ ε₀^{-j} ε_j^{-(j+1)}`, `inv_pow_le_term_succ`). This is the
  printed order of the ARqpC-SC row of (14.2.12) exactly where that row's entry is `j + 1`:
  `q ≥ 2`, or `q = 1` with `X` nonconvex;
* `theorem_14_3_9_arqp`: Theorem 14.3.9 in the printed order for the same runs with the ARqp-SC
  exponents `π_j = j(p+1)/p` when `q = p` (`(ε₀ ε_j)^{-j} ≤ ε₀^{-p} + ε₀^{1-π_j} ε_j^{-π_j}`,
  `inv_pow_le_arqp`); `theorem_14_3_9_arqp_corrected`: for every `q ≤ p`, the bound with the extra
  term `∑_j (ε₀ ε_j)^{-j}`;
* `theorem_14_3_9_arqp_unit`: Theorem 14.3.9 in the printed order on `ℝⁿ` for INNER = ARqp with
  unit radii when `q = p ≤ 2`; `theorem_14_3_9_arqp_unit_corrected`: for every `q ≤ min(2, p)`,
  the bound with the extra term `∑_j (ε₀ ε_j)^{-1}`;
* `exists_tpqpOrderF_lt_arqp`, `exists_tpqpOrderF_lt_arqp_unit`: for `q < p` these extra terms are
  not dominated by the printed order (tolerances `ε₀ = δ`, `ε_1 = δ^a`, `ε_i = 1`;
  `exists_tpqpOrderF_lt`);
* `exists_isTPqpGCARqpSCRun`, `exists_isTPqpGCARqpUnitRun`: both run classes are non-empty
  (`X` closed and `x₀ ∈ X`, resp. `X = ℝⁿ` and `q ≤ 2`, every admissible choice of constants).

## The parameter range

Which rows of (14.2.12) are proved in the printed order, for the runs above:

* ARqpC-SC row, entry `j + 1` (`q ≥ 2`, or `q = 1` with `X` nonconvex): proved for every `q ≤ p`
  (`theorem_14_3_9_arqpc`).
* ARqpC-SC row, entry `(p+1)/p` (`q = 1`, `h = 0`, `X` convex): this is the ARqp-SC exponent of
  order `1`; proved for `p = 1` (`π_1 = 2`, `theorem_14_3_9_arqp` and `theorem_14_3_9_arqpc`), open
  for `p ≥ 2` (the proved bound, `theorem_14_3_9_arqp_corrected`, has the extra term
  `(ε₀ ε_1)^{-1}`, outside the printed order by `exists_tpqpOrderF_lt_arqp`).
* ARqp-SC row, "otherwise" `j(p+1)/p` (every `X`): proved for `q = p` (`theorem_14_3_9_arqp`);
  open for `q < p`.
* ARqp unit radii on `ℝⁿ`, `(p+1)/(p-j+1)`: proved for `q = p ≤ 2`
  (`theorem_14_3_9_arqp_unit`, where the exponents coincide with `j(p+1)/p`); open for
  `q < p`, `q ≤ 2`.

For `q < p` the term of order `1`, `(ε₀ ε_1)^{-1}`, exceeds
`C max[ε₀^{-1}, max_j ε₀^{1-π_j} ε_j^{-π_j}]` for every `C` along `ε_1 = ε₀^a`, `ε_i = 1`
(`i ≥ 2`), with `max(0, max_i π_i - 2) < a < p - 1` (and the same computation with `ε_j = ε₀^a`
applies to the term of every order `j ≤ q`). There the corrected statements
(`theorem_14_3_9_arqp_corrected`, `theorem_14_3_9_arqp_unit_corrected`) are proved; whether
genuine runs attain the printed order is open: the bound counts case-(b) iterations whose target
decreases by `2 (t_k - f(x_{k+1})) ≳ ε₀ ε_j ρ_j^{j-1}`, and neither a sharper lower bound on this
decrease from the ARqp-SC step properties nor a genuine run attaining it was obtained.

## Deviations from the book

* INNER's output radii at a Step-2 termination: the book returns `δ_ε = δ_{s_k}`, which need not
  certify (14.3.19) at `x_k` (the model is minimized at `0`, but `δ_{s_k}` is a radius at `s_k`);
  `IsARqpSCCallOut` admits these radii and also `min(1, ε_j/(4(3 J + σ_k)))` with the jet bound
  `J = jetBound F p x_k`, which certify (14.3.19) and are used for the existence of runs. The
  calls may be cut before INNER terminates (by any test of (14.3.32)); the returned radii are then
  the current radii, or the step radii `δ_{s_e}` when Step 2 is computed at the last iterate.
* The book's `f_up - f_low - 1` is `f_up - f_low + 1`; `max_j` is kept (`tpqpOrderF`,
  `tpqpOrderD`); the constants depend on the data, on `P`, `θ`, `β`, `β₁`, `f_up - f_low` and
  `‖c(x₀)‖` (Lemma 14.3.6 (i)), and are chosen before `ε`. f.B.Fb is on `ℱ_{β_F}` with `ε₀ ≤ β_F`.
* The derivative count acquires the term `ε₀^{-1}` (one successful iteration per outer iteration
  that moves); it is absorbed in the printed `max_j ε₀^{1-π_j} ε_j^{-π_j}` whenever some `π_j ≥ 2`
  (`tpqpOrderF_le_tpqpOrderD`), which holds in every case proved in the printed order.
* Phase 1 with the ARqp-SC exponents uses the additive cost contract (the multiplicative contract
  (14.3.20)–(14.3.21) is false for `π_1 < 2`,
  `exists_algorithm_14_3_1_cost_contract_counterexample`); its extra `κ_C k₁ + 2 k₁`,
  `k₁ ≤ ⌈log(θε₀/‖c(x₀)‖)/log β₁⌉₊`, is `O(ε₀^{-1})` (`ceil_log_div_le`) and fits the printed
  order. With the exponents `j + 1` the multiplicative contract holds (`phase1_cost_le_anchored`).
* `q ≥ 1` is arbitrary (the book takes `q ≤ 3`); `X` need not be closed for the bounds (only for
  the existence of runs). The output properties of Lemma 14.3.5 at termination are
  `IsTPqpGCPhase2.output_spec` and `lemma_14_3_5`, not restated here.

## Not formalized

The trust-region alternative of Theorem 14.3.9 in the printed order (it is proved with corrected
exponents and a logarithmic factor in `Chapter14.Section03TrustRegion`). The printed order in the
open cases listed above.
-/

open Set Metric
open scoped Nat

namespace CartisGouldToint.Chapter14

variable {n m : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

set_option hygiene false in
local notation "ℝᵐ" => EuclideanSpace ℝ (Fin m)

/-! ### One INNER call of Phase 2 realized by ARqp-SC -/

section Call

variable {F : ℝⁿ → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams} {ε : ℕ → ℝ}
  {xi : ℕ → ℝⁿ} {e : ℕ} {succ : ℕ → Prop} {δo : ℕ → ℝ}

/-- The jet bound `max(1, max_{i ∈ [2 : p]} ‖∇^i F(y)‖)` at `y` (computable from the derivatives
that Step 1 of ARqp evaluates at `y`). -/
noncomputable def jetBound (F : ℝⁿ → ℝ) (p : ℕ) (y : ℝⁿ) : ℝ :=
  Chapter12.finMax 1 (fun i => if i < p then ‖iteratedFDeriv ℝ (i + 1) F y‖ else 0) p

/-- One INNER call of Phase 2 of TPqp-GC realized by ARqp-SC, with its output radii: the iterates
`x_{k,0}, …, x_{k,e}` are the first `e + 1` iterates of an ARqpC-SC run (`algorithm_14_1_1` with
`c = 0`, `h = 0`, initial radii `1`; an ARqp-SC run whose Step 2 is Algorithm 14.1.2) on `F`
whose first termination index `k_ε` is at least `e` (the call may be cut before INNER terminates,
by any test of (14.3.32)), the successful iterations are those of the run, and the returned radii
`δo` are those of the run at the last iterate:
* the current radii `δ_e` (Step 1 of Algorithm 14.1.1; at a Step-1 termination these are the
  returned radii);
* or, whenever Step 2 is computed at `e` (`¬ Stop₁ e`; at any cut, not only at a Step-2
  termination), the step radii `δ_{s_e}` (the radii the book returns at a Step-2 termination,
  Algorithm 14.1.1, Step 2);
* or, at a Step-2 termination (`e = k_ε`, `¬ Stop₁ e`), the radii
  `min(1, ε_j/(4(3 J + σ_e)))`, `J = jetBound F p x_e`, which certify (14.3.19) at `x_e` because
  `0` minimizes the model there (`Chapter12.isEpsDeltaApprox_of_isMinOn_zero_of_jet`; the step
  radii `δ_{s_e}` need not). -/
def IsARqpSCCallOut (F : ℝⁿ → ℝ) (X : Set ℝⁿ) (p q : ℕ) (P : ARqpCParams) (ε : ℕ → ℝ)
    (xi : ℕ → ℝⁿ) (e : ℕ) (succ : ℕ → Prop) (δo : ℕ → ℝ) : Prop :=
  ∃ (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → ℝⁿ) (kε : ℕ),
    algorithm_14_1_1 F (zeroCon n) zeroOuter X p q P ε (fun _ => 1) x s σ δ δs d dm ∧
    Optimization.IsFirstHit (arqpcStop F (zeroCon n) zeroOuter p q P ε x s σ δ d) kε ∧
    e ≤ kε ∧ (∀ i ≤ e, xi i = x i) ∧
    (∀ i < e, (succ i ↔ P.η₁ ≤ Optimization.arqpRatio (fun y => F y + zeroOuter (zeroCon n y))
      (fun k => arqpcData F (zeroCon n) zeroOuter p (x k) (σ k)) x s i)) ∧
    ((∀ j ∈ Finset.Icc 1 q, δo j = δ e j) ∨
      (¬ algorithm_14_1_1.Stop₁ F (zeroCon n) zeroOuter p q P ε x σ δ d e ∧
        ∀ j ∈ Finset.Icc 1 q, δo j = δs e j) ∨
      (e = kε ∧ ¬ algorithm_14_1_1.Stop₁ F (zeroCon n) zeroOuter p q P ε x σ δ d e ∧
        ∀ j ∈ Finset.Icc 1 q, δo j = min 1 (ε j / (4 * (3 * jetBound F p (x e) + σ e)))))

/-- A call with output radii is an ARqp-SC call (`IsARqpSCCall`). -/
theorem IsARqpSCCallOut.isARqpSCCall (h : IsARqpSCCallOut F X p q P ε xi e succ δo) :
    IsARqpSCCall F X p q P ε xi e succ := by
  obtain ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he, hxi, hsucc, -⟩ := h
  exact ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he, hxi, hsucc⟩

/-- **The step before the end of a call is not followed by a Step-1 termination** unless the call
ends at a point passing INNER's test (14.3.19) with the returned radii: if `i < e` and either
`i + 1 < e` or the test fails at `x_{k,e}` with the radii `δo`, then the run has not stopped up to
`i` and the Step-1 test fails at `i + 1` (the hypotheses of Lemma 14.2.2). -/
theorem IsARqpSCCallOut.not_stop₁ (h : IsARqpSCCallOut F X p q P ε xi e succ δo) :
    ∃ (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → ℝⁿ) (kε : ℕ),
      algorithm_14_1_1 F (zeroCon n) zeroOuter X p q P ε (fun _ => 1) x s σ δ δs d dm ∧
      Optimization.IsFirstHit (arqpcStop F (zeroCon n) zeroOuter p q P ε x s σ δ d) kε ∧
      e ≤ kε ∧ (∀ i ≤ e, xi i = x i) ∧
      (∀ i < e, (succ i ↔ P.η₁ ≤ Optimization.arqpRatio (fun y => F y + zeroOuter (zeroCon n y))
        (fun k => arqpcData F (zeroCon n) zeroOuter p (x k) (σ k)) x s i)) ∧
      ((∀ j ∈ Finset.Icc 1 q, δo j = δ e j) ∨
        (¬ algorithm_14_1_1.Stop₁ F (zeroCon n) zeroOuter p q P ε x σ δ d e ∧
          ∀ j ∈ Finset.Icc 1 q, δo j = δs e j) ∨
        (e = kε ∧ ¬ algorithm_14_1_1.Stop₁ F (zeroCon n) zeroOuter p q P ε x σ δ d e ∧
          ∀ j ∈ Finset.Icc 1 q, δo j = min 1 (ε j / (4 * (3 * jetBound F p (x e) + σ e))))) ∧
      ∀ i < e, (i + 1 < e ∨ ¬ Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ F (xi e))
          {d | xi e + d ∈ X} q ε δo) →
        ¬ algorithm_14_1_1.Stop₁ F (zeroCon n) zeroOuter p q P ε x σ δ d (i + 1) := by
  obtain ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he, hxi, hsucc, hδo⟩ := h
  refine ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he, hxi, hsucc, hδo, fun i hi hcont h1 => ?_⟩
  by_cases hlt : i + 1 < e
  · exact hhit.2 (i + 1) (lt_of_lt_of_le hlt he) (Or.inl h1)
  · have htest := hcont.resolve_left hlt
    have hie : i + 1 = e := by omega
    rw [hie] at h1
    rcases hδo with hδo | ⟨hn, -⟩ | ⟨-, hn, -⟩
    · refine htest fun j hj => ?_
      have h12 := hr.zero_algorithm_12_2_2_feasible
      have hk12 : ∀ l < e, ¬ Chapter12.arqpStop F P.toARqpParams p q ε x s σ δ d l :=
        fun l hl => zero_arqpcStop_iff.not.1 (hhit.2 l (by omega))
      have h1' : Optimization.arqpStop₁ P.toARqpParams q ε (Chapter12.arqpData F p x σ) δ d e := by
        simpa only [algorithm_14_1_1.Stop₁, zero_arqpcData_eq] using h1
      have happ := Optimization.MeasureTestPasses.isEpsDeltaApprox P.ς_pos (h12.witness e hk12) h1'
      rw [hxi e le_rfl, hδo j hj]
      exact happ j hj
    · exact hn h1
    · exact hn h1

/-- The anchored bounds of `F` on a set `S` containing its sublevel set at the start of the call
give the anchored bounds on the sublevel set of the run's objective at its starting point. -/
private theorem anchored_of_call {X₀ S : Set ℝⁿ} {L : ℕ → ℝ} {x : ℕ → ℝⁿ}
    (hF : AnchoredCompositeBounds F (zeroCon n) X₀ S p L (fun _ => 0)) (hx : xi 0 = x 0)
    (hS : ∀ y ∈ X, F y ≤ F (xi 0) → y ∈ S) :
    AnchoredCompositeBounds F (zeroCon n) X₀
      (compositeSublevel F (zeroCon n) zeroOuter X (x 0)) p L (fun _ => 0) :=
  hF.mono (compositeSublevel_zero_subset (hx ▸ hS))

/-- `jetBound F p y ≤ max(1, max_{i ∈ [1 : p]} L_i)` at a point of the anchor set of anchored
bounds with constants `L` (which bound `‖∇^i F‖` by `L_{i-1}` for `i ∈ [2 : p]`). -/
theorem jetBound_le {X₀ A : Set ℝⁿ} {L : ℕ → ℝ}
    (hF : AnchoredCompositeBounds F (zeroCon n) X₀ A p L (fun _ => 0)) {y : ℝⁿ} (hy : y ∈ A) :
    jetBound F p y ≤ Chapter12.finMax 1 L p := by
  refine Chapter12.finMax_le Chapter12.le_finMax_left fun i hi => ?_
  split_ifs with hip
  · have h2 : i + 1 ∈ Finset.Icc 2 p :=
      Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hi).1; omega, by omega⟩
    have := hF.norm_f (i + 1) h2 y hy
    rw [Nat.add_sub_cancel] at this
    exact this.trans (Chapter12.le_finMax hi)
  · exact zero_le_one.trans Chapter12.le_finMax_left

/-- The radii `min(1, ε_j/(4(3 J + σ_e)))` (`J = jetBound F p x_e`) of a Step-2 termination are at
least `κ_ρ ε_j` (`arqpSCKappaRad`), under anchored bounds on the sublevel set at `x_0`. -/
private theorem jet_radius_ge {X₀ : Set ℝⁿ} {L : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ}
    {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ} {e : ℕ}
    (hr : algorithm_14_1_1 F (zeroCon n) zeroOuter X p q P ε (fun _ => 1) x s σ δ δs d dm)
    (hA : AnchoredCompositeBounds F (zeroCon n) X₀
      (compositeSublevel F (zeroCon n) zeroOuter X (x 0)) p L (fun _ => 0)) (hXX₀ : X ⊆ X₀)
    (hnot : ∀ i < e, ¬ arqpcStop F (zeroCon n) zeroOuter p q P ε x s σ δ d i) :
    ∀ j ∈ Finset.Icc 1 q, arqpSCKappaRad P L p * ε j ≤
      min 1 (ε j / (4 * (3 * jetBound F p (x e) + σ e))) := by
  intro j hj
  obtain ⟨hε0, hε1⟩ := hr.ε_mem j hj
  have hJ := jetBound_le hA (hr.mem_compositeSublevel hnot)
  have hJ1 : 1 ≤ jetBound F p (x e) := Chapter12.le_finMax_left
  have hσ := sigma_le_arqpcSigmaMax_anchored hr hA hXX₀ assumptionHLip_zeroOuter hnot e le_rfl
  have hσ0 : 0 < σ e := hr.run.toIsARRun.sigma_pos hnot e le_rfl
  have hL1 : 1 ≤ Chapter12.finMax 1 L p := Chapter12.one_le_finMax
  have hrad1 : arqpSCKappaRad P L p ≤
      1 / (4 * (3 * Chapter12.finMax 1 L p + arqpcSigmaMax P L (fun _ => 0) 0 p 0)) :=
    min_le_right _ _
  have hK : 0 < 4 * (3 * jetBound F p (x e) + σ e) := by linarith
  have hK' : 4 * (3 * jetBound F p (x e) + σ e) ≤
      4 * (3 * Chapter12.finMax 1 L p + arqpcSigmaMax P L (fun _ => 0) 0 p 0) := by linarith
  have hKm : 0 < 4 * (3 * Chapter12.finMax 1 L p + arqpcSigmaMax P L (fun _ => 0) 0 p 0) := by
    linarith
  refine le_min ?_ ?_
  · calc arqpSCKappaRad P L p * ε j
        ≤ 1 / (4 * (3 * Chapter12.finMax 1 L p + arqpcSigmaMax P L (fun _ => 0) 0 p 0)) * 1 :=
          mul_le_mul hrad1 hε1 hε0.le (div_pos one_pos hKm).le
      _ ≤ 1 := by rw [mul_one, div_le_one hKm]; linarith
  · calc arqpSCKappaRad P L p * ε j
        ≤ 1 / (4 * (3 * Chapter12.finMax 1 L p + arqpcSigmaMax P L (fun _ => 0) 0 p 0)) *
            ε j := mul_le_mul_of_nonneg_right hrad1 hε0.le
      _ ≤ ε j / (4 * (3 * jetBound F p (x e) + σ e)) := by
          rw [one_div_mul_eq_div]
          exact div_le_div_of_nonneg_left hε0.le hK hK'

open Classical in
/-- `|𝒮_e| ≤ |{i < e | succ i}| + 1`: the success set up to `e` (`Optimization.successSet`, which
includes `e`) has at most one more element than the successful iterations before `e`. -/
theorem card_successSet_le (succ : ℕ → Prop) (e : ℕ) :
    ((Optimization.successSet succ e).card : ℝ) ≤ ((Finset.range e).filter succ).card + 1 := by
  have : (Optimization.successSet succ e).card ≤ ((Finset.range e).filter succ).card + 1 := by
    unfold Optimization.successSet
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs
    · exact Finset.card_insert_le _ _
    · exact Nat.le_succ _
  exact_mod_cast this

open Classical in
/-- **The INNER contract of one ARqp-SC call of Phase 2** ([cartis2022evaluation], Lemmas 14.2.2
and 14.2.3 for ARqp-SC, and the radius policy of Algorithm 14.1.2), for every call
`IsARqpSCCallOut` on an objective `F` with anchored bounds (constants `L`, open convex `X₀ ⊇ X`)
on a set containing the sublevel set of `F` at the start of the call, and `θ < ς`:
(stay) unsuccessful iterations do not move;
(count) `e ≤ κ_uns |𝒮| + κ_unc` (14.2.13), `𝒮` the successful iterations of the call;
(decrease) every successful iteration `i < e` that is not the last one, or that is the last one
of a call ending at a point failing INNER's test (14.3.19) with the returned radii, decreases `F`
by at least `κ_decr ε_l^{l+1}` for some `l` (ARqpC-SC row of (14.2.12)), and by at least
`η₁ κ_{Δm} ε_l^{π_l}` with the exponents of the ARqp-SC row in a radii mode `u` (the lower-bound
mode `u = False` for every `q` and `X`, the unit-radii mode when `u` forces `q = 1` and `X`
convex);
(radii) the returned radii are at least `κ_ρ ε_j` (the radius policy (14.1.28) holds at every
iteration of every run, `algorithm_14_1_1.kappaDeltaMin_mul_le_radius_anchored`). -/
theorem IsARqpSCCallOut.contract {X₀ S : Set ℝⁿ} {L : ℕ → ℝ}
    (hF : AnchoredCompositeBounds F (zeroCon n) X₀ S p L (fun _ => 0)) (hXX₀ : X ⊆ X₀)
    (hθς : P.θ < P.ς) (h : IsARqpSCCallOut F X p q P ε xi e succ δo)
    (hS : ∀ y ∈ X, F y ≤ F (xi 0) → y ∈ S) :
    (∀ i < e, ¬ succ i → xi (i + 1) = xi i) ∧
    (e : ℝ) ≤ arqpSCKappaUns P * ((Finset.range e).filter succ).card + arqpSCKappaUnc P L p ∧
    (∀ i < e, succ i → (i + 1 < e ∨ ¬ Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ F (xi e))
        {d | xi e + d ∈ X} q ε δo) →
      ∃ l ∈ Finset.Icc 1 q, arqpSCKappaDecr P L p q * ε l ^ (l + 1) ≤ F (xi i) - F (xi (i + 1))) ∧
    (∀ (u : Prop) [Decidable u], (u → q = 1 ∧ Convex ℝ X) → ∀ i < e, succ i →
      (i + 1 < e ∨ ¬ Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ F (xi e))
        {d | xi e + d ∈ X} q ε δo) →
      ∃ l ∈ Finset.Icc 1 q, arqpRowKappaDecr u P L p q * ε l ^ Chapter12.arqpPiOf u p l ≤
        F (xi i) - F (xi (i + 1))) ∧
    (∀ j ∈ Finset.Icc 1 q, arqpSCKappaRad P L p * ε j ≤ δo j) := by
  obtain ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he, hxi, hsucc, hδo, hns⟩ := h.not_stop₁
  have hA := anchored_of_call hF (hxi 0 (Nat.zero_le _)) hS
  have hnot : ∀ i < e, ¬ arqpcStop F (zeroCon n) zeroOuter p q P ε x s σ δ d i :=
    fun i hi => hhit.2 i (by omega)
  have hq := hr.one_le_q
  have hε := hr.ε_mem
  refine ⟨fun i hi hs => ?_, ?_, fun i hi hs hcont => ?_, fun u _ hu i hi hs hcont => ?_,
    fun j hj => ?_⟩
  · -- unsuccessful iterations do not move
    rw [hxi i hi.le, hxi (i + 1) hi]
    exact hr.run.toIsARRun.eq_of_not_succ (fun l hl => hnot l (by omega))
      (not_le.1 ((hsucc i hi).not.1 hs))
  · -- Lemma 14.2.3
    have h3 := lemma_14_2_3_arqpc_anchored hr hA hXX₀ assumptionHLip_zeroOuter (k := e) hnot
    set ρ := fun i => P.η₁ ≤ Optimization.arqpRatio
      (fun y => F y + zeroOuter (zeroCon n y))
      (fun k => arqpcData F (zeroCon n) zeroOuter p (x k) (σ k)) x s i
    have hS' : (Finset.range e).filter succ = (Finset.range e).filter ρ :=
      Finset.filter_congr fun i hi => hsucc i (Finset.mem_range.1 hi)
    have hcard' := card_successSet_le ρ e
    have hκ := arqpSCKappaUns_nonneg P
    rw [hS']
    unfold arqpSCKappaUnc
    unfold arqpSCKappaUns at hκ ⊢
    nlinarith
  · -- Lemma 14.2.2, ARqpC-SC row
    have hs' := (hsucc i hi).1 hs
    obtain ⟨l, hl, hdec⟩ := lemma_14_2_2_arqpc_anchored hr hθς hA hXX₀
      assumptionHLip_zeroOuter assumptionHS0_zeroOuter (k := i)
      (fun l hl => hnot l (by omega)) hs' (hns i hi hcont)
    refine ⟨l, hl, ?_⟩
    simp only [zeroOuter, Pi.zero_apply, add_zero] at hdec
    rw [hxi i hi.le, hxi (i + 1) hi]
    unfold arqpSCKappaDecr
    rw [mul_assoc]
    exact hdec
  · -- Lemma 14.2.2, ARqp-SC row in radii mode `u`
    have hs' := (hsucc i hi).1 hs
    have hdec := hr.zero_decrease_arqp_anchored hA hXX₀ hθς hu (k := i)
      (fun l hl => hnot l (by omega)) hs' (hns i hi hcont)
    obtain ⟨l, hl, hmin⟩ := Chapter12.exists_finMin_eq hq
      (u := fun j => ε j ^ Chapter12.arqpPiOf u p j) (b := 1) fun j hj =>
        Real.rpow_le_one (hε j hj).1.le (hε j hj).2 (Chapter12.arqpPiOf_nonneg u p j)
    refine ⟨l, hl, ?_⟩
    rw [hmin] at hdec
    rw [hxi i hi.le, hxi (i + 1) hi]
    unfold arqpRowKappaDecr
    rw [mul_assoc]
    exact hdec
  · -- the radius policy
    have hκ : arqpSCKappaRad P L p ≤ kappaDeltaMin P L (fun _ => 0) 0 p 0 := min_le_left _ _
    have hκε := mul_le_mul_of_nonneg_right hκ (hε j hj).1.le
    rcases hδo with hδo | ⟨hn, hδo⟩ | ⟨-, -, hδo⟩
    · rw [hδo j hj]
      exact hκε.trans (hr.zero_radius_ge_anchored hA hXX₀ e hnot j hj)
    · rw [hδo j hj]
      exact hκε.trans (hr.kappaDeltaMin_mul_le_radius_anchored hA hXX₀ assumptionHLip_zeroOuter
        assumptionHS0_zeroOuter hnot hn j hj)
    · rw [hδo j hj]
      exact jet_radius_ge hr hA hXX₀ hnot j hj

end Call

/-! ### Phase 2 with ARqp-SC calls: the INNER contract for every run -/

section Phase2

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams} {θ β : ℝ}
  {ε : ℕ → ℝ} {x₁ : ℝⁿ} {D : TPqpSeq n}

/-- **The INNER calls of Phase 2 of TPqp-GC are ARqp-SC runs** ([cartis2022evaluation],
Algorithm 14.3.2, Step 1: `INNER(μ(·, t_k), X, q, x_k, β ‖r(x_k, t_k)‖ ε)` with INNER = ARqp-SC):
for every outer iteration `k ≥ 1` reached, the iterates, successful iterations and output radii
`δ_{k+1}` of the `k`-th call are those of an ARqp-SC run on `μ(·, t_k)` with tolerances
`β ‖r(x_k, t_k)‖ ε_j` (`IsARqpSCCallOut`), cut at any iteration (by any test of (14.3.32)). -/
def IsARqpSCPhase2Calls (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (p q : ℕ) (P : ARqpCParams)
    (θ β : ℝ) (ε : ℕ → ℝ) (D : TPqpSeq n) : Prop :=
  ∀ k, 1 ≤ k → D.Before f c X q θ ε k →
    IsARqpSCCallOut (Constrained.targetMerit f c (D.t k)) X p q P
      (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) (D.xi k) (D.e k)
      (D.succ k) (D.δ (k + 1))

/-- The sublevel set of `μ(·, t_k)` at the start `x_k` of the `k`-th call lies in
`𝓛_μ(t_k) = {x ∈ X | ‖r(x, t_k)‖ ≤ 1}`, since `‖r(x_k, t_k)‖ ≤ ε₀ ≤ 1`. -/
theorem IsTPqpGCPhase2.call_sublevel (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) :
    ∀ y ∈ X, Constrained.targetMerit f c (D.t k) y ≤
        Constrained.targetMerit f c (D.t k) (D.xi k 0) → y ∈ muSublevel f c X (D.t k) := by
  intro y hy hyk
  rw [h.inner_zero k hk1 hk] at hyk
  exact ⟨hy, (Constrained.targetMerit_le_targetMerit_iff.1 hyk).trans
    (((h.isTargetSequence hk).residual_le h.θ_lt_one.le h.ε₀_pos.le hk1 le_rfl).trans
      (h.ε_le_one 0 (by simp)))⟩

/-- `ρ_j = κ_ρ βθ ε₀ ε_j ≤ κ_ρ β ‖r(x_k, t_k)‖ ε_j` at a case-(b) iteration. -/
private theorem rad_le_of_isKb (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : D.Before f c X q θ ε k) (hb : D.IsKb f c θ ε k) {κ : ℝ} (hκ : 0 ≤ κ) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 q) :
    κ * β * θ * ε 0 * ε j ≤
      κ * (β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) := by
  have hrk : θ * ε 0 ≤ Constrained.targetResidual f c (D.t k) (D.x k) :=
    hb.1.trans (h.resid_succ_le hk1 hk)
  have := h.β_pos
  have := h.ε_pos' hj
  calc κ * β * θ * ε 0 * ε j = κ * (β * (θ * ε 0) * ε j) := by ring
    _ ≤ _ := by gcongr

/-- **Every Phase-2 run of TPqp-GC whose INNER calls are ARqp-SC runs satisfies the INNER contract
keyed on INNER's own test** (`IsInnerPhaseRunStrong`; [cartis2022evaluation], Lemmas 14.2.2–14.2.3,
ARqpC-SC row of (14.2.12), `π_l = l + 1`), with the `t`-independent constants
`κ_decr = arqpSCKappaDecr P L p q`, `κ_uns = arqpSCKappaUns P`, `κ_unc = arqpSCKappaUnc P L p` and
radii `ρ_j = κ_ρ βθ ε₀ ε_j` (`κ_ρ = arqpSCKappaRad P L p`), when every `μ(·, t)` has anchored
bounds with constants `L` on `𝓛_μ(t)` (for an open convex `X₀ ⊇ X`; Lemma 14.3.6 (ii) gives them
under c.D1pLB.X and f.D1pLB.X, `exists_anchoredCompositeBounds_nu_mu`) and `θ < ς`. Unlike
`exists_isTPqpGCPhase2_isInnerPhaseRunStrong`, this holds for every run, with calls cut by any test
of (14.3.32). -/
theorem IsARqpSCPhase2Calls.isInnerPhaseRunStrong (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D)
    (hcalls : IsARqpSCPhase2Calls f c X p q P θ β ε D) {X₀ : Set ℝⁿ} {L : ℕ → ℝ}
    (hμ : ∀ t, AnchoredCompositeBounds (Constrained.targetMerit f c t) (zeroCon n) X₀
      (muSublevel f c X t) p L (fun _ => 0)) (hXX₀ : X ⊆ X₀) (hθς : P.θ < P.ς) :
    IsInnerPhaseRunStrong f c X q θ β ε D (arqpSCKappaDecr P L p q) (arqpSCKappaUns P)
      (arqpSCKappaUnc P L p) (fun l => (l : ℝ) + 1)
      (fun j => arqpSCKappaRad P L p * β * θ * ε 0 * ε j) := by
  have hC := fun k (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) =>
    (hcalls k hk1 hk).contract (hμ (D.t k)) hXX₀ hθς (h.call_sublevel hk1 hk)
  refine ⟨fun k hk1 hk => (hC k hk1 hk).2.1, fun k hk1 hk => (hC k hk1 hk).1,
    fun k hk1 hk i hi hs hcont _ => ?_, fun k hk1 hk hb _ j hj => ?_⟩
  · have hcont' : i + 1 < D.e k ∨ ¬ Optimization.IsEpsDeltaApprox
        (ftaylorSeries ℝ (Constrained.targetMerit f c (D.t k)) (D.xi k (D.e k)))
        {d | D.xi k (D.e k) + d ∈ X} q
        (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) (D.δ (k + 1)) := by
      rw [h.inner_end k hk1 hk]
      exact hcont
    obtain ⟨l, hl, hdec⟩ := (hC k hk1 hk).2.2.1 i hi hs hcont'
    refine ⟨l, hl, ?_⟩
    have e : ((l : ℝ) + 1) = ((l + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e, Real.rpow_natCast]
    exact hdec
  · exact (rad_le_of_isKb h hk1 hk hb (arqpSCKappaRad_pos P L p).le hj).trans
      ((hC k hk1 hk).2.2.2.2 j hj)

/-- **Every Phase-2 run of TPqp-GC whose INNER calls are ARqp-SC runs satisfies the INNER contract
keyed on INNER's own test with the exponents of the ARqp-SC row of (14.2.12)**
([cartis2022evaluation], Lemmas 14.2.2–14.2.3, ARqp-SC row): as
`IsARqpSCPhase2Calls.isInnerPhaseRunStrong`, with `κ_decr = arqpRowKappaDecr u P L p q` and
`π_l = Chapter12.arqpPiOf u p l` in a radii mode `u` (the lower-bound mode `u = False`, exponents
`j(p+1)/p`, for every `q` and `X`; the unit-radii mode when `u` forces `q = 1` and `X` convex). -/
theorem IsARqpSCPhase2Calls.isInnerPhaseRunStrong_arqp (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D)
    (hcalls : IsARqpSCPhase2Calls f c X p q P θ β ε D) {X₀ : Set ℝⁿ} {L : ℕ → ℝ}
    (hμ : ∀ t, AnchoredCompositeBounds (Constrained.targetMerit f c t) (zeroCon n) X₀
      (muSublevel f c X t) p L (fun _ => 0)) (hXX₀ : X ⊆ X₀) (hθς : P.θ < P.ς)
    {u : Prop} [Decidable u] (hu : u → q = 1 ∧ Convex ℝ X) :
    IsInnerPhaseRunStrong f c X q θ β ε D (arqpRowKappaDecr u P L p q) (arqpSCKappaUns P)
      (arqpSCKappaUnc P L p) (Chapter12.arqpPiOf u p)
      (fun j => arqpSCKappaRad P L p * β * θ * ε 0 * ε j) := by
  have hC := fun k (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) =>
    (hcalls k hk1 hk).contract (hμ (D.t k)) hXX₀ hθς (h.call_sublevel hk1 hk)
  refine ⟨fun k hk1 hk => (hC k hk1 hk).2.1, fun k hk1 hk => (hC k hk1 hk).1,
    fun k hk1 hk i hi hs hcont _ => ?_, fun k hk1 hk hb _ j hj => ?_⟩
  · have hcont' : i + 1 < D.e k ∨ ¬ Optimization.IsEpsDeltaApprox
        (ftaylorSeries ℝ (Constrained.targetMerit f c (D.t k)) (D.xi k (D.e k)))
        {d | D.xi k (D.e k) + d ∈ X} q
        (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) (D.δ (k + 1)) := by
      rw [h.inner_end k hk1 hk]
      exact hcont
    exact (hC k hk1 hk).2.2.2.1 u hu i hi hs hcont'
  · exact (rad_le_of_isKb h hk1 hk hb (arqpSCKappaRad_pos P L p).le hj).trans
      ((hC k hk1 hk).2.2.2.2 j hj)

end Phase2

/-! ### The orders of Theorem 14.3.9 -/

section Order

/-- **The order of the number of evaluations of `(f, c)` in Theorem 14.3.9** of
[cartis2022evaluation]: `max[ε₀^{-1}, max_{j ∈ [1 : q]} ε₀^{1-π_j} ε_j^{-π_j}]`. -/
noncomputable def tpqpOrderF (π : ℕ → ℝ) (q : ℕ) (ε : ℕ → ℝ) : ℝ :=
  Chapter12.finMax (ε 0)⁻¹ (fun j => ε 0 ^ (1 - π j) * ε j ^ (-π j)) q

/-- **The order of the number of derivative evaluations in Theorem 14.3.9** of
[cartis2022evaluation]: `max_{j ∈ [1 : q]} ε₀^{1-π_j} ε_j^{-π_j}` (`0` for `q = 0`). -/
noncomputable def tpqpOrderD (π : ℕ → ℝ) (q : ℕ) (ε : ℕ → ℝ) : ℝ :=
  Chapter12.finMax 0 (fun j => ε 0 ^ (1 - π j) * ε j ^ (-π j)) q

variable {π : ℕ → ℝ} {q : ℕ} {ε : ℕ → ℝ}

/-- `ε₀^{-1} ≤ max[ε₀^{-1}, …]`. -/
theorem inv_le_tpqpOrderF : (ε 0)⁻¹ ≤ tpqpOrderF π q ε := Chapter12.le_finMax_left

/-- Each term `ε₀^{1-π_j} ε_j^{-π_j}` is at most the function-evaluation order. -/
theorem term_le_tpqpOrderF {j : ℕ} (hj : j ∈ Finset.Icc 1 q) :
    ε 0 ^ (1 - π j) * ε j ^ (-π j) ≤ tpqpOrderF π q ε :=
  Chapter12.le_finMax (u := fun j => ε 0 ^ (1 - π j) * ε j ^ (-π j)) hj

/-- Each term `ε₀^{1-π_j} ε_j^{-π_j}` is at most the derivative-evaluation order. -/
theorem term_le_tpqpOrderD {j : ℕ} (hj : j ∈ Finset.Icc 1 q) :
    ε 0 ^ (1 - π j) * ε j ^ (-π j) ≤ tpqpOrderD π q ε :=
  Chapter12.le_finMax (u := fun j => ε 0 ^ (1 - π j) * ε j ^ (-π j)) hj

/-- `1 ≤ ε₀^{-1} ≤ max[ε₀^{-1}, …]` for `ε₀ ∈ (0, 1]`. -/
theorem one_le_tpqpOrderF (h0 : 0 < ε 0) (h1 : ε 0 ≤ 1) : 1 ≤ tpqpOrderF π q ε :=
  ((one_le_inv₀ h0).2 h1).trans inv_le_tpqpOrderF

/-- **The two orders agree when some `π_j ≥ 2`**: then `ε₀^{-1} ≤ ε₀^{1-π_j} ε_j^{-π_j}` for
tolerances in `(0, 1]`, so the term `ε₀^{-1}` of the function-evaluation order is absorbed (this
holds for the ARqpC-SC exponents `j + 1`, and for the ARqp-SC exponents when `q = p`). -/
theorem tpqpOrderF_le_tpqpOrderD (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 q) (hπj : 2 ≤ π j) : tpqpOrderF π q ε ≤ tpqpOrderD π q ε := by
  have hε₀ := hε 0 (by simp)
  have hεj := hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  refine Chapter12.finMax_le ?_ fun l hl => term_le_tpqpOrderD hl
  refine le_trans ?_ (term_le_tpqpOrderD hj)
  have h1 : (ε 0)⁻¹ ≤ ε 0 ^ (1 - π j) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hε₀.1 hε₀.2 (by linarith)
  have h2 : 1 ≤ ε j ^ (-π j) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hεj.1 hεj.2 (by linarith)
  have h3 : 0 ≤ ε 0 ^ (1 - π j) := Real.rpow_nonneg hε₀.1.le _
  nlinarith

/-- The bad-iteration term of the ARqpC-SC exponents: `(ε₀ ε_j)^{-j} ≤ ε₀^{1-π_j} ε_j^{-π_j}`
for `π_j = j + 1` and `ε₀, ε_j ∈ (0, 1]`. -/
theorem inv_pow_le_term_succ {ε₀ εj : ℝ} (h0 : 0 < ε₀) (hj0 : 0 < εj) (hj1 : εj ≤ 1) (j : ℕ) :
    ((ε₀ * εj) ^ j)⁻¹ ≤ ε₀ ^ (1 - ((j : ℝ) + 1)) * εj ^ (-((j : ℝ) + 1)) := by
  have e1 : ε₀ ^ (1 - ((j : ℝ) + 1)) = (ε₀ ^ j)⁻¹ := by
    rw [show 1 - ((j : ℝ) + 1) = -(j : ℝ) by ring, Real.rpow_neg h0.le, Real.rpow_natCast]
  have e2 : εj ^ (-((j : ℝ) + 1)) = (εj ^ j)⁻¹ * εj⁻¹ := by
    rw [Real.rpow_neg hj0.le, show ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_succ, mul_inv]
  rw [e1, e2, mul_pow, mul_inv]
  have : 1 ≤ εj⁻¹ := (one_le_inv₀ hj0).2 hj1
  have : 0 ≤ (ε₀ ^ j)⁻¹ * (εj ^ j)⁻¹ := by positivity
  nlinarith

end Order

/-! ### Phase 2: from the INNER contract to the order of Theorem 14.3.9 -/

section Phase2Order

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {q : ℕ} {θ β : ℝ}

/-- The contract `IsInnerPhaseRunStrong` with radii `ρ` gives it with any smaller radii. -/
theorem IsInnerPhaseRunStrong.mono_radius {ε : ℕ → ℝ} {D : TPqpSeq n} {κdecr κuns κunc : ℝ}
    {π ρ ρ' : ℕ → ℝ} (h : IsInnerPhaseRunStrong f c X q θ β ε D κdecr κuns κunc π ρ)
    (hρ : ∀ j ∈ Finset.Icc 1 q, ρ' j ≤ ρ j) :
    IsInnerPhaseRunStrong f c X q θ β ε D κdecr κuns κunc π ρ' :=
  ⟨h.count, h.stay, h.decrease, fun k hk1 hk hb ht j hj =>
    (hρ j hj).trans (h.radius_ge k hk1 hk hb ht j hj)⟩

open Classical in
/-- **Phase 2 of TPqp-GC within an order bound, for every run satisfying the INNER contract keyed
on INNER's own test** (`IsInnerPhaseRunStrong`, [cartis2022evaluation], Theorem 14.3.9, Phase 2).
For constants `κ_decr > 0`, `κ_uns, κ_unc ≥ 0`, `κ_ρ > 0`, `π_max`, `B_f > 0`, `A ≥ 0`, `b ≥ 0`
and `θ ∈ (0, 1)`, `β > 0`, there are constants `C_F`, `C_D` such that for all tolerances `ε` and
every Phase-2 run satisfying `IsInnerPhaseRunStrong` with these constants, exponents
`0 ≤ π_l ≤ π_max` and radii `ρ_j = κ_ρ ρ'_j` (`ρ'_j > 0`), under f.B.Fb on `ℱ_{β_F}` (`ε₀ ≤ β_F`,
`f_up - f_low + 1 ≤ A`), `f`, `c` of class `C^q` near `X` with `‖∇^i f‖ ≤ B_f` on
`{x ∈ X | ‖c(x)‖ ≤ ε₀}`, and for every `O` with `ε₀^{-1} ≤ O`, `ε₀^{1-π_l} ε_l^{-π_l} ≤ O` and
`(ε₀ ε_j ρ'_j^{j-1})^{-1} ≤ b O` (the order of the bad outer iterations; `ρ'_j = ε₀ ε_j` for the
ARqp-SC radius policy, `ρ'_j = 1` for unit radii), Phase 2 terminates at some `k_ε`
using at most `C_F O` evaluations of `(f, c)` and `C_D O` derivative evaluations
(`IsTPqpGCPhase2.complexity_of_strong_on`). -/
theorem IsTPqpGCPhase2.exists_const_order_of_strong (hq : 1 ≤ q)
    {κdecr κuns κunc κρ πmax Bf A b : ℝ}
    (hκ : 0 < κdecr) (hκuns : 0 ≤ κuns) (hκunc : 0 ≤ κunc) (hκρ : 0 < κρ) (hBf0 : 0 < Bf)
    (hA : 0 ≤ A) (hb : 0 ≤ b) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) :
    ∃ CF CD : ℝ, 0 ≤ CF ∧ 0 ≤ CD ∧
      ∀ {ε : ℕ → ℝ} {x₁ : ℝⁿ} {D : TPqpSeq n} {π ρ' : ℕ → ℝ} {βF flow fup O : ℝ},
      IsTPqpGCPhase2 f c X q θ β ε x₁ D →
      IsInnerPhaseRunStrong f c X q θ β ε D κdecr κuns κunc π (fun j => κρ * ρ' j) →
      (∀ j ∈ Finset.Icc 1 q, 0 < ρ' j) →
      (∀ l ∈ Finset.Icc 1 q, 0 ≤ π l ∧ π l ≤ πmax) →
      Chapter07.AssumptionBFb f c X βF flow fup → ε 0 ≤ βF → fup - flow + 1 ≤ A →
      (∀ y ∈ X, ContDiffAt ℝ q f y) → (∀ y ∈ X, ContDiffAt ℝ q c y) →
      (∀ y ∈ X, ‖c y‖ ≤ ε 0 → ∀ i ∈ Finset.Icc 1 q, ‖iteratedFDeriv ℝ i f y‖ ≤ Bf) →
      (ε 0)⁻¹ ≤ O → (∀ l ∈ Finset.Icc 1 q, ε 0 ^ (1 - π l) * ε l ^ (-π l) ≤ O) →
      (∀ j ∈ Finset.Icc 1 q, (ε 0 * ε j * ρ' j ^ (j - 1))⁻¹ ≤ b * O) →
      ∃ kε, D.IsEnd f c X q θ ε kε ∧ (D.funEvals kε : ℝ) ≤ CF * O ∧
        (D.derivEvals kε : ℝ) ≤ CD * O := by
  obtain ⟨a, ha_def⟩ : ∃ a, a = A / (1 - θ) := ⟨_, rfl⟩
  obtain ⟨g, hg_def⟩ : ∃ g, g = κdecr⁻¹ * (β * θ) ^ (-πmax) * (1 - θ) := ⟨_, rfl⟩
  obtain ⟨cj, hcj⟩ : ∃ cj : ℕ → ℝ,
      cj = fun j => 2 * Bf * j ! * (1 + θ) / (θ * (1 - θ) * κρ ^ (j - 1)) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = ∑ j ∈ Finset.Icc 1 q, cj j := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = a * g * q + a + g * q + 1 + (a + 1) + A * (1 + b * C) := ⟨_, rfl⟩
  have h1θ : 0 < 1 - θ := by linarith
  have ha : 0 ≤ a := ha_def ▸ div_nonneg hA h1θ.le
  have hg : 0 ≤ g := by
    have := Real.rpow_nonneg (mul_pos hβ0 hθ0).le (-πmax)
    rw [hg_def]
    positivity
  have hcj0 : ∀ j, 0 ≤ cj j := fun j => by rw [hcj]; positivity
  have hC0 : 0 ≤ C := hC ▸ Finset.sum_nonneg fun j _ => hcj0 j
  have hK0 : 0 ≤ K := by
    rw [hK]
    have := mul_nonneg hb hC0
    positivity
  have hagq : 0 ≤ a * g * q := by positivity
  have hgq0 : 0 ≤ g * q := by positivity
  refine ⟨1 + κuns * (a * g * q + g * q + K) + κunc * K, 1 + a * g * q + g * q + K,
    by positivity, by positivity,
    fun {ε x₁ D π ρ' βF flow fup O} h2 hin hρ' hπ hB hεβ hAf hf hc hBf hO0 hOT hOB => ?_⟩
  have hε₀ := h2.ε₀_pos
  have hε₀1 : ε 0 ≤ 1 := h2.ε_le_one 0 (by simp)
  have hO1 : 1 ≤ O := ((one_le_inv₀ hε₀).2 hε₀1).trans hO0
  have hOnn : 0 ≤ O := zero_le_one.trans hO1
  -- the constant `M` of Lemma 14.3.8
  obtain ⟨M, hM_def⟩ : ∃ M, M = ∑ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - π l) * ε l ^ (-π l) :=
    ⟨_, rfl⟩
  have hterm : ∀ l ∈ Finset.Icc 1 q, 0 < ε 0 ^ (2 - π l) * ε l ^ (-π l) := fun l hl =>
    mul_pos (Real.rpow_pos_of_pos hε₀ _) (Real.rpow_pos_of_pos (h2.ε_pos' hl) _)
  have hM0 : 0 < M := hM_def ▸ Finset.sum_pos hterm ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hq⟩⟩
  have hM : ∀ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - π l) * ε l ^ (-π l) ≤ M := fun l hl =>
    hM_def ▸ Finset.single_le_sum (f := fun l => ε 0 ^ (2 - π l) * ε l ^ (-π l))
      (fun i hi => (hterm i hi).le) hl
  have hMO : M ≤ q * (ε 0 * O) := by
    have : ∀ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - π l) * ε l ^ (-π l) ≤ ε 0 * O := fun l hl => by
      rw [show 2 - π l = 1 + (1 - π l) by ring, Real.rpow_add hε₀, Real.rpow_one, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hOT l hl) hε₀.le
    have := Finset.sum_le_card_nsmul _ _ _ this
    rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at this
    rw [hM_def]
    exact this
  -- the target decrease `τ`
  obtain ⟨τj, hτj⟩ : ∃ τj : ℕ → ℝ,
      τj = fun j => kbMargin θ (ε 0) * ε j * (κρ * ρ' j) ^ (j - 1) / (2 * Bf * j !) :=
    ⟨_, rfl⟩
  obtain ⟨τ, hτ_def⟩ : ∃ τ, τ = Chapter12.finMin 1 τj q := ⟨_, rfl⟩
  have hη : 0 < kbMargin θ (ε 0) := by unfold kbMargin; positivity
  have hτj0 : ∀ j ∈ Finset.Icc 1 q, 0 < τj j := fun j hj => by
    have := h2.ε_pos' hj
    have := hρ' j hj
    rw [hτj]
    positivity
  have hτ0 : 0 < τ := hτ_def ▸ Chapter12.finMin_pos one_pos hτj0
  have hτ : ∀ j ∈ Finset.Icc 1 q,
      2 * Bf * τ ≤ kbMargin θ (ε 0) * ε j * (κρ * ρ' j) ^ (j - 1) / j ! := fun j hj => by
    have h1 : τ ≤ τj j := hτ_def ▸ Chapter12.finMin_le (b := 1) hj (u := τj)
    have hfac : (0 : ℝ) < j ! := by positivity
    calc 2 * Bf * τ ≤ 2 * Bf * τj j := by gcongr
      _ = _ := by rw [hτj]; field_simp
  have hτinv : ∀ j ∈ Finset.Icc 1 q, (τj j)⁻¹ = cj j * (ε 0 * ε j * ρ' j ^ (j - 1))⁻¹ :=
    fun j hj => by
      have := h2.ε_pos' hj
      have := hρ' j hj
      rw [hτj, hcj]
      simp only [kbMargin]
      rw [mul_pow]
      field_simp
  have hAτ : (fup - flow + 1) / τ ≤ A * (1 + b * C) * O := by
    have h1 : (fup - flow + 1) / τ ≤ A * τ⁻¹ := by
      rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right hAf (inv_pos.2 hτ0).le
    have hsum : ∑ j ∈ Finset.Icc 1 q, (τj j)⁻¹ ≤ C * (b * O) := by
      rw [hC, Finset.sum_mul]
      exact Finset.sum_le_sum fun j hj => by
        rw [hτinv j hj]; exact mul_le_mul_of_nonneg_left (hOB j hj) (hcj0 j)
    have h2' : τ⁻¹ ≤ (1 + b * C) * O := by
      have := hτ_def ▸ Chapter12.inv_finMin_one_le hτj0
      have hbC : 0 ≤ b * C := mul_nonneg hb hC0
      calc τ⁻¹ ≤ 1 + C * (b * O) := this.trans (by linarith)
        _ ≤ O + b * C * O := by nlinarith
        _ = (1 + b * C) * O := by ring
    calc (fup - flow + 1) / τ ≤ A * τ⁻¹ := h1
      _ ≤ A * ((1 + b * C) * O) := mul_le_mul_of_nonneg_left h2' hA
      _ = A * (1 + b * C) * O := by ring
  obtain ⟨-, kε, hend, hkε, hD, hF⟩ := h2.complexity_of_strong_on hin hκ hκuns hπ hM0 hM hB hεβ
    (fun j hj => by have := hρ' j hj; positivity) hf hc hBf hτ0 (hτ_def ▸ hτ)
  -- the bounds
  obtain ⟨Na, hNa_def⟩ : ∃ Na, Na = (fup - flow + 1) / ((1 - θ) * ε 0) := ⟨_, rfl⟩
  obtain ⟨G, hG_def⟩ : ∃ G, G = goodBound κdecr β θ πmax M := ⟨_, rfl⟩
  rw [← hNa_def, ← hG_def] at hkε hD hF
  have hGg : G = g * M := by rw [hG_def, hg_def, goodBound]
  have hG0 : 0 ≤ G := by rw [hGg]; exact mul_nonneg hg hM0.le
  have hNa : Na ≤ a * (ε 0)⁻¹ := by
    calc Na ≤ A / ((1 - θ) * ε 0) := hNa_def ▸ div_le_div_of_nonneg_right hAf (by positivity)
      _ = a * (ε 0)⁻¹ := by rw [ha_def]; field_simp
  have hNaO : Na ≤ a * O := hNa.trans (mul_le_mul_of_nonneg_left hO0 ha)
  have hGO : G ≤ g * q * (ε 0 * O) := by
    rw [hGg, mul_assoc]; exact mul_le_mul_of_nonneg_left hMO hg
  have hgq : 0 ≤ g * q := mul_nonneg hg (Nat.cast_nonneg q)
  have hεO : ε 0 * O ≤ O := mul_le_of_le_one_left hOnn hε₀1
  have hG1 : G ≤ g * q * O := hGO.trans (mul_le_mul_of_nonneg_left hεO hgq)
  have hGNa : G * (Na + 1) ≤ (a * g * q + g * q) * O := by
    have h1 : G * (Na + 1) ≤ G * (a * (ε 0)⁻¹ + 1) := by gcongr
    have h2' : G * (a * (ε 0)⁻¹) ≤ a * g * q * O := by
      calc G * (a * (ε 0)⁻¹) ≤ g * q * (ε 0 * O) * (a * (ε 0)⁻¹) :=
            mul_le_mul_of_nonneg_right hGO (mul_nonneg ha (inv_pos.2 hε₀).le)
        _ = a * g * q * O * (ε 0 * (ε 0)⁻¹) := by ring
        _ = a * g * q * O := by rw [mul_inv_cancel₀ hε₀.ne', mul_one]
    calc G * (Na + 1) ≤ G * (a * (ε 0)⁻¹ + 1) := h1
      _ = G * (a * (ε 0)⁻¹) + G := by ring
      _ ≤ a * g * q * O + g * q * O := add_le_add h2' hG1
      _ = (a * g * q + g * q) * O := by ring
  have hkK : (kε : ℝ) ≤ K * O := by
    have h1 : (Na + 1) * (G + 1) ≤ (a * g * q + a + g * q + 1) * O := by
      calc (Na + 1) * (G + 1) = G * (Na + 1) + Na + 1 := by ring
        _ ≤ (a * g * q + g * q) * O + a * O + O := by linarith
        _ = (a * g * q + a + g * q + 1) * O := by ring
    calc (kε : ℝ) ≤ (Na + 1) * (G + 1) + (Na + 1 + (fup - flow + 1) / τ) := hkε
      _ ≤ (a * g * q + a + g * q + 1) * O + (a * O + O + A * (1 + b * C) * O) := by
          linarith
      _ = K * O := by rw [hK]; ring
  refine ⟨kε, hend, ?_, ?_⟩
  · calc (D.funEvals kε : ℝ) ≤ 1 + κuns * (G * (Na + 1) + kε) + κunc * kε := hF
      _ ≤ O + κuns * ((a * g * q + g * q) * O + K * O) + κunc * (K * O) := by gcongr
      _ = _ := by ring
  · calc (D.derivEvals kε : ℝ) ≤ 1 + G * (Na + 1) + kε := hD
      _ ≤ O + (a * g * q + g * q) * O + K * O := by gcongr
      _ = _ := by ring

end Phase2Order

/-! ### TPqp-GC runs with INNER = ARqp-SC in both phases -/

section Run

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams} {θ β₁ β : ℝ}
  {ε : ℕ → ℝ} {x₀ : ℝⁿ} {xP : ℕ → ℝⁿ} {δP : ℕ → ℕ → ℝ} {k₁ : ℕ} {D : TPqpSeq n}
  {nF₁ nD₁ : ℕ → ℕ}

/-- **A run of TPqp-GC with INNER = ARqp-SC in both phases** ([cartis2022evaluation],
Algorithm 14.3.2 with INNER of regularization type, ARqp-SC run as ARqpC-SC with `c = 0`,
`h = 0`): a run (`algorithm_14_3_2`) whose Phase-1 INNER calls (14.3.23)
`x_k = INNER(ν, X, q, x_{k-1}, β₁ ‖c(x_{k-1})‖ (θε₀, ε_1, …, ε_q))` are ARqp-SC runs on `ν` that
use `nF₁ k` evaluations of `c` and `nD₁ k` of its derivatives (`IsARqpSCOutputCost`), and whose
Phase-2 INNER calls (if Phase 2 is entered) are ARqp-SC runs on `μ(·, t_k)` with their output
radii, cut at any iteration (`IsARqpSCPhase2Calls`). -/
structure IsTPqpGCARqpSCRun (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (p q : ℕ)
    (P : ARqpCParams) (θ β₁ β : ℝ) (ε : ℕ → ℝ) (x₀ : ℝⁿ) (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ)
    (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ) : Prop where
  /-- The TPqp-GC run. -/
  run : algorithm_14_3_2 f c X q θ β₁ β ε x₀ xP δP k₁ D
  /-- The Phase-1 INNER calls are ARqp-SC runs with their evaluation counts. -/
  phase1 : ∀ k, 1 ≤ k → k ≤ k₁ → IsARqpSCOutputCost (phi2 c) X p q P
    (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) (xP (k - 1)) (xP k) (δP k) (nF₁ k)
      (nD₁ k)
  /-- The Phase-2 INNER calls are ARqp-SC runs with their output radii. -/
  phase2 : ‖c (xP k₁)‖ ≤ θ * ε 0 → IsARqpSCPhase2Calls f c X p q P θ β ε D

/-- `κ_unc ≥ 0`. -/
theorem arqpSCKappaUnc_nonneg (P : ARqpCParams) (L : ℕ → ℝ) (p : ℕ) :
    0 ≤ arqpSCKappaUnc P L p := by
  unfold arqpSCKappaUnc
  have := arqpSCKappaUns_nonneg P
  have := P.log_γ₂_pos
  have : 0 ≤ Real.log (arqpcSigmaMax P L (fun _ => 0) 0 p 0 / P.σ₀) :=
    Real.log_nonneg ((one_le_div P.σ₀_pos).2 (Optimization.σ₀_le_arSigmaMax _ _))
  positivity

/-- The Phase-1 bound of Lemma 14.3.7 is within the order of Theorem 14.3.9:
`½ κ ‖c(x₀)‖ ∑_j β₁^{1-2π_j}/(β₁^{1-π_j} - 1) θ^{1-π_j} ε₀^{1-π_j} ε_j^{-π_j} ≤
½ κ ‖c(x₀)‖ W O` with `W = ∑_j |β₁^{1-2π_j}/(β₁^{1-π_j} - 1) θ^{1-π_j}|`, for `κ ≥ 0` and every
`O ≥ ε₀^{1-π_j} ε_j^{-π_j}`. -/
theorem phase1Bound_le {κ r β₁ θ O : ℝ} {π : ℕ → ℝ} (hκ : 0 ≤ κ) (hr : 0 ≤ r)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j)
    (hO : ∀ j ∈ Finset.Icc 1 q, ε 0 ^ (1 - π j) * ε j ^ (-π j) ≤ O) :
    1 / 2 * κ * r * ∑ j ∈ Finset.Icc 1 q, β₁ ^ (1 - 2 * π j) / (β₁ ^ (1 - π j) - 1) *
        θ ^ (1 - π j) * ε 0 ^ (1 - π j) * ε j ^ (-π j) ≤
      1 / 2 * κ * r * (∑ j ∈ Finset.Icc 1 q,
        |β₁ ^ (1 - 2 * π j) / (β₁ ^ (1 - π j) - 1) * θ ^ (1 - π j)|) * O := by
  rw [mul_assoc (1 / 2 * κ * r), Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) (by positivity)
  have h0 : 0 ≤ ε 0 ^ (1 - π j) * ε j ^ (-π j) := by
    have := hε 0 (by simp)
    have := hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
    positivity
  rw [mul_assoc _ (ε 0 ^ (1 - π j))]
  calc _ ≤ |β₁ ^ (1 - 2 * π j) / (β₁ ^ (1 - π j) - 1) * θ ^ (1 - π j)| *
        (ε 0 ^ (1 - π j) * ε j ^ (-π j)) := mul_le_mul_of_nonneg_right (le_abs_self _) h0
    _ ≤ _ := mul_le_mul_of_nonneg_left (hO j hj) (abs_nonneg _)

end Run

/-! ### Theorem 14.3.9 with INNER = ARqpC-SC (exponents `j + 1`) -/

section Theorem1439

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {p q : ℕ}

/-- **Theorem 14.3.9** of [cartis2022evaluation] (complexity of TPqp-GC) **with the exponents
`π_j = j + 1`, for every run with INNER = ARqpC-SC with `c = 0`, `h = 0`** (ARqp-SC with Step 2
by Algorithm 14.1.2), under the book's assumptions c.D1pLB.X and f.D1pLB.X (on an open convex
`X₀ ⊇ X`) and f.B.Fb on `ℱ_{β_F}`, with `1 ≤ q ≤ p`. This is the printed order of the ARqpC-SC
row of (14.2.12) exactly where that row's entry is `j + 1`: `q ≥ 2`, or `q = 1` with `X`
nonconvex; for `q = 1` with `X` convex the entry is `(p+1)/p` (`h = 0` is convex), which is
proved only for `p = 1` (`theorem_14_3_9_arqp`) and is otherwise open. For ARqpC constants with
`θ < ς`, `θ ∈ (0, 1)`, `β > 0` (the runs have `β ≤ θ`, the book's `β = θ` included), `β₁` and a
starting point `x₀`, there are constants `κ_F`, `κ_D` such that for all tolerances
`ε ∈ (0, 1]^{q+1}` with `ε₀ ≤ β_F` and every TPqp-GC run whose INNER calls are ARqp-SC runs
(ARqpC-SC with `c = 0`, `h = 0`, `IsTPqpGCARqpSCRun`; Phase-2 calls may be cut by any test of
(14.3.32); such runs exist, `exists_isTPqpGCARqpSCRun`):
* if Phase 1 ends with `‖c(x₁)‖ > θε₀`, it uses at most `κ_F O_F` evaluations of `c` and
  `κ_D O_D` derivative evaluations;
* otherwise Phase 2 terminates at some `k_ε`, and both phases together use at most `κ_F O_F`
  evaluations of `(f, c)` and `κ_D O_D` derivative evaluations,

where `π_j = j + 1` (the ARqpC-SC row of (14.2.12)), `O_F = max[ε₀^{-1}, max_j ε₀^{1-π_j}
ε_j^{-π_j}]` (`tpqpOrderF`) and `O_D = max_j ε₀^{1-π_j} ε_j^{-π_j}` (`tpqpOrderD`), i.e. the
printed orders `O(max[ε₀^{-1}, max_j ε₀^{-j} ε_j^{-(j+1)}])` and `O(max_j ε₀^{-j} ε_j^{-(j+1)})`.
The constants depend only on the data (through Lemma 14.3.6), on `P`, `θ`, `β`, `β₁`, `f_up - f_low`
and `‖c(x₀)‖`. The proof: every such run satisfies the INNER contract keyed on INNER's own test
with `t`-independent constants (`IsARqpSCPhase2Calls.isInnerPhaseRunStrong`) and the Phase-1 cost
contract (`phase1_cost_le_anchored`); the bad-iteration term `(ε₀ ε_j)^{-j}` of
`IsTPqpGCPhase2.complexity_of_strong` is at most `ε₀^{-j} ε_j^{-(j+1)}` (`inv_pow_le_term_succ`),
and since `π_1 = 2` the term `ε₀^{-1}` is absorbed in `O_D` (`tpqpOrderF_le_tpqpOrderD`). -/
theorem theorem_14_3_9_arqpc (hq : 1 ≤ q) (hqp : q ≤ p) {X₀ : Set ℝⁿ} {Lc Bc Lf Bf : ℕ → ℝ}
    (hc : AssumptionCD1pLBX c X X₀ p Lc Bc) (hf : AssumptionD1pLBX f X X₀ p Lf Bf)
    {βF flow fup : ℝ} (hB : Chapter07.AssumptionBFb f c X βF flow fup)
    (P : ARqpCParams) (hθς : P.θ < P.ς) {θ β β₁ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hβ0 : 0 < β) (x₀ : ℝⁿ) :
    ∃ κF κD : ℝ, ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ βF →
      ∀ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCARqpSCRun f c X p q P θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ →
        (θ * ε 0 < ‖c (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤ κF * tpqpOrderF (fun j => (j : ℝ) + 1) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ κD * tpqpOrderD (fun j => (j : ℝ) + 1) q ε) ∧
        (‖c (xP k₁)‖ ≤ θ * ε 0 → ∃ kε, D.IsEnd f c X q θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤
            κF * tpqpOrderF (fun j => (j : ℝ) + 1) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤
            κD * tpqpOrderD (fun j => (j : ℝ) + 1) q ε) := by
  obtain ⟨LA, LB, BA, BB, Lμ, Bμ, h1, hνA, hμA⟩ :=
    exists_anchoredCompositeBounds_nu_mu (hq.trans hqp) hc hf
  set Lν := nuAnchoredConst LA LB BA BB ‖c x₀‖ with hLν
  set L := anchoredConst Lμ Bμ with hL
  have hLp : 1 ≤ L p := (hμA 0).one_le
  have hκ : 0 < arqpSCKappaDecr P L p q := arqpSCKappaDecr_pos_of hLp hθς
  have hκρ : 0 < arqpSCKappaRad P L p * β * θ := by
    have := arqpSCKappaRad_pos P L p
    positivity
  obtain ⟨CF, CD, hCF, hCD, hord⟩ := IsTPqpGCPhase2.exists_const_order_of_strong (f := f) (c := c)
    (X := X) (θ := θ) (β := β) hq (πmax := (q : ℝ) + 1) hκ (arqpSCKappaUns_nonneg P)
    (arqpSCKappaUnc_nonneg P L p) hκρ (finMax_one_pos (B := Bf)) (abs_nonneg (fup - flow + 1))
    zero_le_one hθ0 hθ1 hβ0
  -- the Phase-1 constants
  have hνκ : 0 < arqpSCKappaDecr P Lν p q := arqpSCKappaDecr_pos_of (hνA x₀).one_le hθς
  have hκF : 0 ≤ arqpSCKappaF P Lν p q := by
    unfold arqpSCKappaF
    have := arqpSCKappaUns_nonneg P
    have := arqpSCKappaC_nonneg P Lν p
    positivity
  have hκD : 0 ≤ arqpSCKappaD P Lν p q := by
    unfold arqpSCKappaD
    positivity
  set W := ∑ j ∈ Finset.Icc 1 q, |β₁ ^ (1 - 2 * ((j : ℝ) + 1)) / (β₁ ^ (1 - ((j : ℝ) + 1)) - 1) *
    θ ^ (1 - ((j : ℝ) + 1))| with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hP1F : 0 ≤ 1 / 2 * arqpSCKappaF P Lν p q * ‖c x₀‖ * W := by positivity
  have hP1D : 0 ≤ 1 / 2 * arqpSCKappaD P Lν p q * ‖c x₀‖ * W := by positivity
  refine ⟨1 / 2 * arqpSCKappaF P Lν p q * ‖c x₀‖ * W + CF,
    1 / 2 * arqpSCKappaD P Lν p q * ‖c x₀‖ * W + CD,
    fun ε hε hεβ xP δP k₁ D nF₁ nD₁ hR => ?_⟩
  have h := hR.run
  set π : ℕ → ℝ := fun j => (j : ℝ) + 1 with hπ_def
  have hεI : ∀ l ∈ Finset.Icc 1 q, 0 < ε l ∧ ε l ≤ 1 := fun l hl =>
    hε l (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hl).2))
  have hε₀ := hε 0 (by simp)
  have hOT : ∀ j ∈ Finset.Icc 1 q, ε 0 ^ (1 - π j) * ε j ^ (-π j) ≤ tpqpOrderF π q ε :=
    fun j hj => term_le_tpqpOrderF hj
  have hO1 : 1 ≤ tpqpOrderF π q ε := one_le_tpqpOrderF hε₀.1 hε₀.2
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
  have hFD : tpqpOrderF π q ε ≤ tpqpOrderD π q ε :=
    tpqpOrderF_le_tpqpOrderD hε h1q (by simp only [hπ_def]; norm_num)
  -- Phase 1
  have hπ1 : ∀ l ∈ Finset.Icc 1 q, 1 < π l := fun l hl => by
    have : (1 : ℝ) ≤ l := by exact_mod_cast (Finset.mem_Icc.1 hl).1
    simp only [hπ_def]
    linarith
  have hcost := phase1_cost_le_anchored h hq (hνA x₀) hc.subset hθς hε hR.phase1
  have hF1 := (lemma_14_3_7 h hθ0 hπ1 hκF fun k hk => (hcost k hk).1).2
  have hD1 := (lemma_14_3_7 h hθ0 hπ1 hκD fun k hk => (hcost k hk).2).2
  have hF1' := hF1.trans (phase1Bound_le hκF (norm_nonneg _) (fun j hj => (hε j hj).1) hOT)
  have hD1' := hD1.trans (phase1Bound_le hκD (norm_nonneg _) (fun j hj => (hε j hj).1) hOT)
  rw [← hW] at hF1' hD1'
  have hOnn : 0 ≤ tpqpOrderF π q ε := zero_le_one.trans hO1
  refine ⟨fun _ => ⟨?_, ?_⟩, fun hc1 => ?_⟩
  · calc _ ≤ 1 / 2 * arqpSCKappaF P Lν p q * ‖c x₀‖ * W * tpqpOrderF π q ε := hF1'
      _ ≤ _ := by nlinarith
  · calc _ ≤ 1 / 2 * arqpSCKappaD P Lν p q * ‖c x₀‖ * W * tpqpOrderF π q ε := hD1'
      _ ≤ 1 / 2 * arqpSCKappaD P Lν p q * ‖c x₀‖ * W * tpqpOrderD π q ε :=
          mul_le_mul_of_nonneg_left hFD hP1D
      _ ≤ _ := by nlinarith
  -- Phase 2
  have h2 := h.phase2 hc1
  have hin := ((hR.phase2 hc1).isInnerPhaseRunStrong h2 hμA hc.subset hθς).mono_radius
    (ρ' := fun j => arqpSCKappaRad P L p * β * θ * (ε 0 * ε j)) fun j _ => le_of_eq (by ring)
  obtain ⟨kε, hend, hF2, hD2⟩ := hord h2 hin (fun j hj => mul_pos hε₀.1 (hεI j hj).1)
    (fun l hl => by
      have : (l : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.1 hl).2
      exact ⟨by positivity, by linarith⟩) hB hεβ (le_abs_self _)
    (fun _ hy => hf.contDiffAt_of_le hqp hy) (fun _ hy => hc.contDiffAt_of_le hqp hy)
    (fun _ hy _ => hf.norm_iteratedFDeriv_le_finMax hqp (hf.subset hy)) inv_le_tpqpOrderF hOT
    (fun j hj => by
      rw [one_mul, mul_pow_sub_one (by have := (Finset.mem_Icc.1 hj).1; omega) _]
      exact (inv_pow_le_term_succ hε₀.1 (hεI j hj).1 (hεI j hj).2 j).trans (hOT j hj))
  refine ⟨kε, hend, ?_, ?_⟩
  · calc _ ≤ 1 / 2 * arqpSCKappaF P Lν p q * ‖c x₀‖ * W * tpqpOrderF π q ε +
          CF * tpqpOrderF π q ε := add_le_add hF1' hF2
      _ = _ := by ring
  · calc _ ≤ 1 / 2 * arqpSCKappaD P Lν p q * ‖c x₀‖ * W * tpqpOrderF π q ε +
          CD * tpqpOrderF π q ε := add_le_add hD1' hD2
      _ ≤ 1 / 2 * arqpSCKappaD P Lν p q * ‖c x₀‖ * W * tpqpOrderD π q ε +
          CD * tpqpOrderD π q ε := by gcongr
      _ = _ := by ring

end Theorem1439

/-! ### Theorem 14.3.9 with INNER = ARqp-SC (exponents `j(p+1)/p`) -/

section Theorem1439ARqp

/-- The ARqp-SC exponents of the lower-bound radii mode: `1 < j(p+1)/p ≤ q(p+1)/p` for
`j ∈ [1 : q]`. -/
theorem arqpPiOf_false_mem {p q j : ℕ} (hp : 1 ≤ p) (hj : j ∈ Finset.Icc 1 q) :
    1 < Chapter12.arqpPiOf False p j ∧
      Chapter12.arqpPiOf False p j ≤ Chapter12.arqpPiOf False p q := by
  rw [Chapter12.arqpPiOf_of_neg not_false, Chapter12.arqpPiOf_of_neg not_false]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
  have hjq : (j : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.1 hj).2
  refine ⟨by rw [lt_div_iff₀ hp0]; nlinarith, by gcongr⟩

/-- The ARqp-SC exponent of order `p` is `p(p+1)/p = p + 1`. -/
theorem arqpPiOf_false_self {p : ℕ} (hp : 1 ≤ p) :
    Chapter12.arqpPiOf False p p = (p : ℝ) + 1 := by
  rw [Chapter12.arqpPiOf_of_neg not_false]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 (by omega))

/-- **The bad-iteration term against the ARqp-SC order** (exponents `π_j = j(p+1)/p`): for
`ε₀, ε_j ∈ (0, 1]`, `(ε₀ ε_j)^{-j} ≤ ε₀^{-p} + ε₀^{1-π_j} ε_j^{-π_j}` (weighted AM–GM:
`(ε₀ ε_j)^{-j}` is the geometric mean of `ε₀^{-p}` and `ε₀^{1-π_j} ε_j^{-π_j}` with weights
`1/(p+1)`, `p/(p+1)`). With `q = p`, `ε₀^{-p} ≤ ε₀^{1-π_p} ε_p^{-π_p}` (`π_p = p + 1`), so the
term is within the printed order. -/
theorem inv_pow_le_arqp {ε₀ εj : ℝ} (h0 : 0 < ε₀) (hj0 : 0 < εj) {p j : ℕ} (hp : 1 ≤ p) :
    ((ε₀ * εj) ^ j)⁻¹ ≤ (ε₀ ^ p)⁻¹ +
      ε₀ ^ (1 - Chapter12.arqpPiOf False p j) * εj ^ (-Chapter12.arqpPiOf False p j) := by
  rw [Chapter12.arqpPiOf_of_neg not_false]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  set π : ℝ := (j : ℝ) * (p + 1) / p with hπ
  set w₁ : ℝ := 1 / (p + 1) with hw₁
  set w₂ : ℝ := p / (p + 1) with hw₂
  have hw : w₁ + w₂ = 1 := by rw [hw₁, hw₂]; field_simp; ring
  have hA : 0 ≤ (ε₀ ^ p)⁻¹ := by positivity
  have hB : 0 ≤ ε₀ ^ (1 - π) * εj ^ (-π) := by positivity
  have hgm := Real.geom_mean_le_arith_mean2_weighted (w₁ := w₁) (w₂ := w₂) (by positivity)
    (by positivity) hA hB hw
  have e1 : ((ε₀ ^ p)⁻¹) ^ w₁ = ε₀ ^ (-(p : ℝ) * w₁) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg h0.le, ← Real.rpow_mul h0.le]
  have e2 : (ε₀ ^ (1 - π) * εj ^ (-π)) ^ w₂ = ε₀ ^ ((1 - π) * w₂) * εj ^ (-π * w₂) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul h0.le,
      ← Real.rpow_mul hj0.le]
  have e3 : ((ε₀ * εj) ^ j)⁻¹ = ε₀ ^ (-(p : ℝ) * w₁ + (1 - π) * w₂) * εj ^ (-π * w₂) := by
    have x1 : -(p : ℝ) * w₁ + (1 - π) * w₂ = -(j : ℝ) := by
      rw [hw₁, hw₂, hπ]; field_simp; ring
    have x2 : -π * w₂ = -(j : ℝ) := by rw [hw₂, hπ]; field_simp
    rw [x1, x2, Real.rpow_neg h0.le, Real.rpow_neg hj0.le, Real.rpow_natCast, Real.rpow_natCast,
      mul_pow, mul_inv]
  rw [e3, Real.rpow_add h0, mul_assoc, ← e2, ← e1]
  have h1 : w₁ ≤ 1 := by rw [hw₁, div_le_one (by positivity)]; linarith
  have h2 : w₂ ≤ 1 := by rw [hw₂, div_le_one (by positivity)]; linarith
  calc _ ≤ w₁ * (ε₀ ^ p)⁻¹ + w₂ * (ε₀ ^ (1 - π) * εj ^ (-π)) := hgm
    _ ≤ _ := add_le_add (mul_le_of_le_one_left hA h1) (mul_le_of_le_one_left hB h2)

/-- The iteration bound of Theorem 14.3.3 is `O(ε₀^{-1})`:
`⌈log(a/r)/log β₁⌉₊ ≤ 1 + r/(a |log β₁|)` for `a > 0`, `r ≥ 0`, `β₁ ∈ (0, 1)`. -/
theorem ceil_log_div_le {a r β₁ : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (hβ₁0 : 0 < β₁) (hβ₁1 : β₁ < 1) :
    (⌈Real.log (a / r) / Real.log β₁⌉₊ : ℝ) ≤ 1 + r / (a * |Real.log β₁|) := by
  have hl : Real.log β₁ < 0 := Real.log_neg hβ₁0 hβ₁1
  have habs : |Real.log β₁| = -Real.log β₁ := abs_of_neg hl
  have hkey : -Real.log (a / r) ≤ r / a := by
    rcases hr.eq_or_lt with rfl | hr0
    · simp
    · rw [← Real.log_inv, inv_div]
      have := Real.log_le_sub_one_of_pos (div_pos hr0 ha)
      linarith
  have hx : Real.log (a / r) / Real.log β₁ ≤ r / (a * |Real.log β₁|) :=
    calc Real.log (a / r) / Real.log β₁ = -Real.log (a / r) / -Real.log β₁ :=
          (neg_div_neg_eq _ _).symm
      _ ≤ r / a / -Real.log β₁ := div_le_div_of_nonneg_right hkey (by linarith)
      _ = r / (a * |Real.log β₁|) := by rw [habs, div_div]
  have hnn : 0 ≤ r / (a * |Real.log β₁|) := by positivity
  by_cases hx0 : 0 ≤ Real.log (a / r) / Real.log β₁
  · have := Nat.ceil_lt_add_one hx0
    linarith
  · rw [Nat.ceil_eq_zero.2 (not_le.1 hx0).le]
    push_cast
    linarith

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {p q : ℕ}

/-- **Theorem 14.3.9 with INNER = ARqp-SC and the exponents `π_j = j(p+1)/p`, relative to an
order `O`** (the core of `theorem_14_3_9_arqp` and `theorem_14_3_9_arqp_corrected`). Under the
assumptions of `theorem_14_3_9_arqpc`, there are constants `κ_F, κ_D ≥ 0` such that for all
tolerances and every TPqp-GC run with INNER = ARqp-SC (`IsTPqpGCARqpSCRun`), and for every `O`
with `ε₀^{-1} ≤ O`, `ε₀^{1-π_l} ε_l^{-π_l} ≤ O` and `(ε₀ ε_j)^{-j} ≤ O` for `l, j ∈ [1 : q]`
(`π_l = Chapter12.arqpPiOf False p l`, the "otherwise" entries of (14.2.12)), the evaluation
counts of both phases are at most `κ_F O` and `κ_D O`, Phase 2 (if entered) terminating. The
Phase-1 contract is used in its additive form (`IsARqpSCOutputCost.cost_le_arqp_add_anchored`,
`lemma_14_3_7_add`): the extra `κ_C k₁ + 2 k₁` with `k₁ ≤ ⌈log(θε₀/‖c(x₀)‖)/log β₁⌉₊` is
`O(ε₀^{-1})` (`ceil_log_div_le`). -/
theorem exists_const_order_arqp (hq : 1 ≤ q) (hqp : q ≤ p) {X₀ : Set ℝⁿ}
    {Lc Bc Lf Bf : ℕ → ℝ} (hc : AssumptionCD1pLBX c X X₀ p Lc Bc)
    (hf : AssumptionD1pLBX f X X₀ p Lf Bf) {βF flow fup : ℝ}
    (hB : Chapter07.AssumptionBFb f c X βF flow fup) (P : ARqpCParams) (hθς : P.θ < P.ς)
    {θ β β₁ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (x₀ : ℝⁿ) :
    ∃ κF κD : ℝ, 0 ≤ κF ∧ 0 ≤ κD ∧
      ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ βF →
      ∀ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCARqpSCRun f c X p q P θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ → ∀ O : ℝ,
        (ε 0)⁻¹ ≤ O →
        (∀ l ∈ Finset.Icc 1 q, ε 0 ^ (1 - Chapter12.arqpPiOf False p l) *
          ε l ^ (-Chapter12.arqpPiOf False p l) ≤ O) →
        (∀ j ∈ Finset.Icc 1 q, ((ε 0 * ε j) ^ j)⁻¹ ≤ O) →
        (θ * ε 0 < ‖c (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤ κF * O ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ κD * O) ∧
        (‖c (xP k₁)‖ ≤ θ * ε 0 → ∃ kε, D.IsEnd f c X q θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤ κF * O ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤ κD * O) := by
  have hp : 1 ≤ p := hq.trans hqp
  obtain ⟨LA, LB, BA, BB, Lμ, Bμ, h1, hνA, hμA⟩ := exists_anchoredCompositeBounds_nu_mu hp hc hf
  set Lν := nuAnchoredConst LA LB BA BB ‖c x₀‖ with hLν
  set L := anchoredConst Lμ Bμ with hL
  have hLp : 1 ≤ L p := (hμA 0).one_le
  have hκ : 0 < arqpRowKappaDecr False P L p q :=
    mul_pos P.η₁_pos (Chapter12.arqpKappaDmOf_pos False P.σmin_pos hθς hLp)
  have hκρ : 0 < arqpSCKappaRad P L p * β * θ := by
    have := arqpSCKappaRad_pos P L p
    positivity
  obtain ⟨CF, CD, hCF, hCD, hord⟩ := IsTPqpGCPhase2.exists_const_order_of_strong (f := f) (c := c)
    (X := X) (θ := θ) (β := β) hq (πmax := Chapter12.arqpPiOf False p q) hκ
    (arqpSCKappaUns_nonneg P) (arqpSCKappaUnc_nonneg P L p) hκρ (finMax_one_pos (B := Bf))
    (abs_nonneg (fup - flow + 1)) zero_le_one hθ0 hθ1 hβ0
  -- the Phase-1 constants
  have hνκ : 0 < arqpRowKappaDecr False P Lν p q :=
    mul_pos P.η₁_pos (Chapter12.arqpKappaDmOf_pos False P.σmin_pos hθς (hνA x₀).one_le)
  set κF₁ := arqpSCKappaUns P / arqpRowKappaDecr False P Lν p q with hκF₁
  set κD₁ := 1 / arqpRowKappaDecr False P Lν p q with hκD₁
  have hκF : 0 ≤ κF₁ := div_nonneg (arqpSCKappaUns_nonneg P) hνκ.le
  have hκD : 0 ≤ κD₁ := div_nonneg zero_le_one hνκ.le
  have hκC := arqpSCKappaC_nonneg P Lν p
  set W := ∑ j ∈ Finset.Icc 1 q, |β₁ ^ (1 - 2 * Chapter12.arqpPiOf False p j) /
    (β₁ ^ (1 - Chapter12.arqpPiOf False p j) - 1) * θ ^ (1 - Chapter12.arqpPiOf False p j)| with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set c₁ := 1 + ‖c x₀‖ / (θ * |Real.log β₁|) with hc₁
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  refine ⟨1 / 2 * κF₁ * ‖c x₀‖ * W + arqpSCKappaC P Lν p * c₁ + CF,
    1 / 2 * κD₁ * ‖c x₀‖ * W + 2 * c₁ + CD, by positivity, by positivity,
    fun ε hε hεβ xP δP k₁ D nF₁ nD₁ hR O hO0 hOT hOB => ?_⟩
  have h := hR.run
  have hε₀ := hε 0 (by simp)
  have hO1 : 1 ≤ O := ((one_le_inv₀ hε₀.1).2 hε₀.2).trans hO0
  have hOnn : 0 ≤ O := zero_le_one.trans hO1
  have hβ₁0 := h.phase1.β_pos
  have hβ₁1 := h.phase1.β_lt_one
  -- Phase 1: the number of iterations and the additive cost contract
  have hk₁ : (k₁ : ℝ) ≤ c₁ * O := by
    obtain ⟨⟨kmax, hhit, hkmax, -⟩, -⟩ := theorem_14_3_3 h.phase1
    rw [hhit.unique h.phase1_end, phase1Tol_zero, h.start] at hkmax
    have h1 : (k₁ : ℝ) ≤ 1 + ‖c x₀‖ / (θ * ε 0 * |Real.log β₁|) :=
      (Nat.cast_le.2 hkmax).trans (ceil_log_div_le (mul_pos hθ0 hε₀.1) (norm_nonneg _) hβ₁0 hβ₁1)
    have h2 : ‖c x₀‖ / (θ * ε 0 * |Real.log β₁|) = ‖c x₀‖ / (θ * |Real.log β₁|) * (ε 0)⁻¹ := by
      field_simp
    have h3 : 0 ≤ ‖c x₀‖ / (θ * |Real.log β₁|) := by positivity
    calc (k₁ : ℝ) ≤ 1 + ‖c x₀‖ / (θ * |Real.log β₁|) * (ε 0)⁻¹ := h2 ▸ h1
      _ ≤ O + ‖c x₀‖ / (θ * |Real.log β₁|) * O := by gcongr
      _ = c₁ * O := by rw [hc₁]; ring
  have hcost : ∀ k ∈ Finset.Icc 1 k₁,
      (nF₁ k : ℝ) ≤ innerEvalBound κF₁ (Chapter12.arqpPiOf False p) q (phi2 c (xP (k - 1)))
        (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) + arqpSCKappaC P Lν p ∧
      (nD₁ k : ℝ) ≤ innerEvalBound κD₁ (Chapter12.arqpPiOf False p) q (phi2 c (xP (k - 1)))
        (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) + 2 := by
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
    exact (hR.phase1 k hk1 hkk).cost_le_arqp_add_anchored (hνA x₀) hc.subset
      (fun y _ => by rw [phi2_apply]; positivity) hθς (u := False) (fun h => h.elim) hmem
      (fun y hy hyk => ⟨hy, (norm_le_of_phi2_le hyk).trans hck⟩)
  have hπ1 : ∀ l ∈ Finset.Icc 1 q, 1 < Chapter12.arqpPiOf False p l := fun l hl =>
    (arqpPiOf_false_mem hp hl).1
  have hF1 := (lemma_14_3_7_add h hθ0 hπ1 hκF fun k hk => (hcost k hk).1).trans
    (add_le_add (phase1Bound_le hκF (norm_nonneg _) (fun j hj => (hε j hj).1) hOT) le_rfl)
  have hD1 := (lemma_14_3_7_add h hθ0 hπ1 hκD fun k hk => (hcost k hk).2).trans
    (add_le_add (phase1Bound_le hκD (norm_nonneg _) (fun j hj => (hε j hj).1) hOT) le_rfl)
  rw [← hW] at hF1 hD1
  have hF1' : ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤
      (1 / 2 * κF₁ * ‖c x₀‖ * W + arqpSCKappaC P Lν p * c₁) * O := by
    calc _ ≤ 1 / 2 * κF₁ * ‖c x₀‖ * W * O + k₁ * arqpSCKappaC P Lν p := hF1
      _ ≤ 1 / 2 * κF₁ * ‖c x₀‖ * W * O + c₁ * O * arqpSCKappaC P Lν p := by gcongr
      _ = _ := by ring
  have hD1' : ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ (1 / 2 * κD₁ * ‖c x₀‖ * W + 2 * c₁) * O := by
    calc _ ≤ 1 / 2 * κD₁ * ‖c x₀‖ * W * O + k₁ * 2 := hD1
      _ ≤ 1 / 2 * κD₁ * ‖c x₀‖ * W * O + c₁ * O * 2 := by gcongr
      _ = _ := by ring
  refine ⟨fun _ => ⟨hF1'.trans (by nlinarith), hD1'.trans (by nlinarith)⟩, fun hc1 => ?_⟩
  -- Phase 2
  have h2 := h.phase2 hc1
  have hin := ((hR.phase2 hc1).isInnerPhaseRunStrong_arqp h2 hμA hc.subset hθς (u := False)
    (fun h => h.elim)).mono_radius
    (ρ' := fun j => arqpSCKappaRad P L p * β * θ * (ε 0 * ε j)) fun j _ => le_of_eq (by ring)
  have hεI : ∀ l ∈ Finset.Icc 1 q, 0 < ε l ∧ ε l ≤ 1 := fun l hl =>
    hε l (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hl).2))
  obtain ⟨kε, hend, hF2, hD2⟩ := hord h2 hin (fun j hj => mul_pos hε₀.1 (hεI j hj).1)
    (fun l hl =>
      ⟨Chapter12.arqpPiOf_nonneg False p l, (arqpPiOf_false_mem hp hl).2⟩) hB hεβ
    (le_abs_self _) (fun _ hy => hf.contDiffAt_of_le hqp hy)
    (fun _ hy => hc.contDiffAt_of_le hqp hy)
    (fun _ hy _ => hf.norm_iteratedFDeriv_le_finMax hqp (hf.subset hy)) hO0 hOT
    (fun j hj => by
      rw [one_mul, mul_pow_sub_one (by have := (Finset.mem_Icc.1 hj).1; omega) _]
      exact hOB j hj)
  refine ⟨kε, hend, ?_, ?_⟩
  · calc _ ≤ (1 / 2 * κF₁ * ‖c x₀‖ * W + arqpSCKappaC P Lν p * c₁) * O + CF * O :=
          add_le_add hF1' hF2
      _ = _ := by ring
  · calc _ ≤ (1 / 2 * κD₁ * ‖c x₀‖ * W + 2 * c₁) * O + CD * O := add_le_add hD1' hD2
      _ = _ := by ring

/-- **Theorem 14.3.9** of [cartis2022evaluation] **for every run with INNER = ARqp-SC and the
exponents `π_j = j(p+1)/p` of (14.2.12) ("otherwise" entries, the radius bound (12.2.51)), with
the bad-iteration term**: under the assumptions of `theorem_14_3_9_arqpc`, there are constants
`κ_F`, `κ_D` such that for all tolerances `ε ∈ (0, 1]^{q+1}` with `ε₀ ≤ β_F` and every TPqp-GC run
with INNER = ARqp-SC in both phases (`IsTPqpGCARqpSCRun`), the evaluation counts are at most
`κ_F (O_F + ∑_j (ε₀ ε_j)^{-j})` and `κ_D (O_F + ∑_j (ε₀ ε_j)^{-j})` (Phase 2, if entered,
terminating), with `O_F = tpqpOrderF π q ε` the printed order of the function evaluations. The
extra term comes from the case-(b) iterations whose INNER call ends at a point passing INNER's test
(`IsTPqpGCPhase2.complexity_of_strong`, radii `ρ_j ∼ ε₀ ε_j`): for `q = p` it is within the printed
order (`theorem_14_3_9_arqp`); for `q < p` it is not dominated by `O_F` (for `j = 1`, `ε_j = 1` for
`j ≥ 2` and `ε_1 = ε₀^s` with `max(0, q(p+1)/p - 2) < s < p - 1`). -/
theorem theorem_14_3_9_arqp_corrected (hq : 1 ≤ q) (hqp : q ≤ p) {X₀ : Set ℝⁿ}
    {Lc Bc Lf Bf : ℕ → ℝ} (hc : AssumptionCD1pLBX c X X₀ p Lc Bc)
    (hf : AssumptionD1pLBX f X X₀ p Lf Bf) {βF flow fup : ℝ}
    (hB : Chapter07.AssumptionBFb f c X βF flow fup) (P : ARqpCParams) (hθς : P.θ < P.ς)
    {θ β β₁ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (x₀ : ℝⁿ) :
    ∃ κF κD : ℝ, ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ βF →
      ∀ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCARqpSCRun f c X p q P θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ →
        let O := tpqpOrderF (Chapter12.arqpPiOf False p) q ε +
          ∑ j ∈ Finset.Icc 1 q, ((ε 0 * ε j) ^ j)⁻¹
        (θ * ε 0 < ‖c (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤ κF * O ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ κD * O) ∧
        (‖c (xP k₁)‖ ≤ θ * ε 0 → ∃ kε, D.IsEnd f c X q θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤ κF * O ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤ κD * O) := by
  obtain ⟨κF, κD, -, -, hmain⟩ :=
    exists_const_order_arqp hq hqp hc hf hB P hθς hθ0 hθ1 hβ0 (β₁ := β₁) x₀
  refine ⟨κF, κD, fun ε hε hεβ xP δP k₁ D nF₁ nD₁ hR => ?_⟩
  intro O
  have hB0 : 0 ≤ ∑ j ∈ Finset.Icc 1 q, ((ε 0 * ε j) ^ j)⁻¹ := Finset.sum_nonneg fun j hj => by
    have := (hε 0 (by simp)).1
    have := (hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))).1
    positivity
  have hO0 : 0 ≤ tpqpOrderF (Chapter12.arqpPiOf False p) q ε :=
    zero_le_one.trans (one_le_tpqpOrderF (hε 0 (by simp)).1 (hε 0 (by simp)).2)
  have hnn : ∀ i ∈ Finset.Icc 1 q, 0 ≤ ((ε 0 * ε i) ^ i)⁻¹ := fun i hi => by
    have := (hε 0 (by simp)).1
    have := (hε i (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hi).2))).1
    positivity
  exact hmain ε hε hεβ xP δP k₁ D nF₁ nD₁ hR O
    (inv_le_tpqpOrderF.trans (le_add_of_nonneg_right hB0))
    (fun l hl => (term_le_tpqpOrderF hl).trans (le_add_of_nonneg_right hB0))
    fun j hj => (Finset.single_le_sum hnn hj).trans (le_add_of_nonneg_left hO0)

/-- **Theorem 14.3.9** of [cartis2022evaluation] **for every run with INNER = ARqp-SC, in the
printed order, when `q = p`** (exponents `π_j = j(p+1)/p` of (14.2.12), `π_p = p + 1`): under the
assumptions of `theorem_14_3_9_arqpc` with `p = q`, there are constants `κ_F`, `κ_D` such that for
all tolerances `ε ∈ (0, 1]^{q+1}` with `ε₀ ≤ β_F` and every TPqp-GC run with INNER = ARqp-SC in both
phases (`IsTPqpGCARqpSCRun`), Phase 1 alone (if it ends with `‖c(x₁)‖ > θε₀`), resp. both phases
(Phase 2 terminating), use at most `κ_F O_F` evaluations of `(f, c)` and `κ_D O_D` derivative
evaluations, `O_F = max[ε₀^{-1}, max_j ε₀^{1-π_j} ε_j^{-π_j}]` (`tpqpOrderF`) and
`O_D = max_j ε₀^{1-π_j} ε_j^{-π_j}` (`tpqpOrderD`), the orders printed in Theorem 14.3.9. The
bad-iteration term `(ε₀ ε_j)^{-j}` is at most `ε₀^{-p} + ε₀^{1-π_j} ε_j^{-π_j}`
(`inv_pow_le_arqp`) and `ε₀^{-p} ≤ ε₀^{1-π_p} ε_p^{-π_p}`; for `q < p` see
`theorem_14_3_9_arqp_corrected`. -/
theorem theorem_14_3_9_arqp (hq : 1 ≤ q) {X₀ : Set ℝⁿ} {Lc Bc Lf Bf : ℕ → ℝ}
    (hc : AssumptionCD1pLBX c X X₀ q Lc Bc) (hf : AssumptionD1pLBX f X X₀ q Lf Bf)
    {βF flow fup : ℝ} (hB : Chapter07.AssumptionBFb f c X βF flow fup) (P : ARqpCParams)
    (hθς : P.θ < P.ς) {θ β β₁ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (x₀ : ℝⁿ) :
    ∃ κF κD : ℝ, ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ βF →
      ∀ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCARqpSCRun f c X q q P θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ →
        (θ * ε 0 < ‖c (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤
            κF * tpqpOrderF (Chapter12.arqpPiOf False q) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤
            κD * tpqpOrderD (Chapter12.arqpPiOf False q) q ε) ∧
        (‖c (xP k₁)‖ ≤ θ * ε 0 → ∃ kε, D.IsEnd f c X q θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤
            κF * tpqpOrderF (Chapter12.arqpPiOf False q) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤
            κD * tpqpOrderD (Chapter12.arqpPiOf False q) q ε) := by
  obtain ⟨κF, κD, hκF, hκD, hmain⟩ :=
    exists_const_order_arqp hq le_rfl hc hf hB P hθς hθ0 hθ1 hβ0 (β₁ := β₁) x₀
  refine ⟨2 * κF, 2 * κD, fun ε hε hεβ xP δP k₁ D nF₁ nD₁ hR => ?_⟩
  set π := Chapter12.arqpPiOf False q with hπ
  set OF := tpqpOrderF π q ε with hOF
  have hε₀ := hε 0 (by simp)
  have hq1 : q ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨hq, le_rfl⟩
  have hπq : π q = (q : ℝ) + 1 := arqpPiOf_false_self hq
  have hFD : OF ≤ tpqpOrderD π q ε :=
    tpqpOrderF_le_tpqpOrderD hε hq1 (by rw [hπq]; have : (1 : ℝ) ≤ q := by exact_mod_cast hq
                                        linarith)
  have hO0 : 0 ≤ OF := zero_le_one.trans (one_le_tpqpOrderF hε₀.1 hε₀.2)
  -- the bad-iteration term is within twice the printed order
  have hp_le : ((ε 0) ^ q)⁻¹ ≤ OF := by
    refine le_trans ?_ (term_le_tpqpOrderF hq1)
    have hεq := hε q (Finset.mem_range.2 (Nat.lt_succ_self q))
    have e1 : ε 0 ^ (1 - π q) = ((ε 0) ^ q)⁻¹ := by
      rw [hπq, show 1 - ((q : ℝ) + 1) = -(q : ℝ) by ring, Real.rpow_neg hε₀.1.le,
        Real.rpow_natCast]
    rw [e1]
    have : 1 ≤ ε q ^ (-π q) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hεq.1 hεq.2
        (by rw [hπq]; linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)])
    have : 0 ≤ ((ε 0) ^ q)⁻¹ := by have := hε₀.1; positivity
    nlinarith
  have hmain' := hmain ε hε hεβ xP δP k₁ D nF₁ nD₁ hR (2 * OF)
    (inv_le_tpqpOrderF.trans (by linarith))
    (fun l hl => (term_le_tpqpOrderF hl).trans (by linarith)) fun j hj => by
      have hεj := hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
      have := inv_pow_le_arqp hε₀.1 hεj.1 (j := j) hq
      have := term_le_tpqpOrderF (π := π) (ε := ε) hj
      linarith
  obtain ⟨hP1, hP2⟩ := hmain'
  have hD : ∀ x : ℝ, x ≤ κD * (2 * OF) → x ≤ 2 * κD * tpqpOrderD π q ε := fun x hx => by
    nlinarith
  refine ⟨fun hc1 => ⟨by linarith [(hP1 hc1).1], hD _ (hP1 hc1).2⟩, fun hc1 => ?_⟩
  obtain ⟨kε, hend, hF, hDD⟩ := hP2 hc1
  exact ⟨kε, hend, by linarith, hD _ hDD⟩

end Theorem1439ARqp

/-! ### Existence of TPqp-GC runs with INNER = ARqp-SC -/

section Existence

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams} {ε : ℕ → ℝ}
  {θ β : ℝ}

open Classical in
/-- **One INNER call of Phase 2 with its output radii exists** from every `(x, t)` with `x ∈ X`
and `θε₀ ≤ ‖r(x, t)‖ ≤ ε₀`: ARqp-SC on `μ(·, t)` with tolerances `β ‖r(x, t)‖ ε` (an ARqpC-SC run
with `c = 0`, `h = 0`, which terminates by Theorem 14.2.4), stopped at its termination or as soon
as `‖r(·, t)‖ < θε₀`, returning the current radii, or the radii `min(1, ε_j/(4(3 J + σ)))` at a
Step-2 termination; its output satisfies (14.3.32) (the first or the third test). -/
theorem exists_callData {t : ℝ} {L : ℕ → ℝ} {X₀ : Set ℝⁿ}
    (hμ : AnchoredCompositeBounds (Constrained.targetMerit f c t) (zeroCon n) X₀
      (muSublevel f c X t) p L (fun _ => 0)) (hXX₀ : X ⊆ X₀) (P : ARqpCParams)
    (hθς : P.θ < P.ς) (hq : 1 ≤ q) (hqp : q ≤ p) (hX : IsClosed X) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hβ0 : 0 < β) (hβθ : β ≤ θ)
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
      IsARqpSCCallOut (Constrained.targetMerit f c t) X p q P
        (fun j => β * Constrained.targetResidual f c t x * ε j) o.xi o.e o.succ o.δ := by
  set F := Constrained.targetMerit f c t with hFdef
  set ρ := Constrained.targetResidual f c t x with hρ
  have hεI : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 := fun j hj =>
    hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  have hε₀ := hε 0 (by simp)
  have hρ0 : 0 < ρ := lt_of_lt_of_le (mul_pos hθ0 hε₀.1) hlo
  have hε' : ∀ j ∈ Finset.Icc 1 q, 0 < β * ρ * ε j ∧ β * ρ * ε j ≤ 1 := by
    intro j hj
    obtain ⟨h1, h2⟩ := hεI j hj
    refine ⟨by positivity, ?_⟩
    have : β * ρ ≤ 1 := by nlinarith
    nlinarith
  have hS : ∀ y ∈ X, F y ≤ F x → y ∈ muSublevel f c X t := fun y hy hyx =>
    ⟨hy, (Constrained.targetMerit_le_targetMerit_iff.1 hyx).trans (hhi.trans hε₀.2)⟩
  obtain ⟨xr, s, σ, δ, δs, d, dm, hx0, hr⟩ := exists_isARqpCRun_of_hLip
    (f := F) (c := zeroCon n) assumptionHLip_zeroOuter assumptionHS0_zeroOuter P hq hqp hε'
    (fun _ _ => ⟨one_pos, le_rfl⟩) hX hx
  have hA : AnchoredCompositeBounds F (zeroCon n) X₀
      (compositeSublevel F (zeroCon n) zeroOuter X (xr 0)) p L (fun _ => 0) :=
    hμ.mono (compositeSublevel_zero_subset (hx0 ▸ hS))
  have hmε : ∀ j ∈ Finset.Icc 1 q, (β * ρ * ε j) ^ (j + 1) ≤ 1 := fun j hj =>
    pow_le_one₀ (hε' j hj).1.le (hε' j hj).2
  obtain ⟨j₀, hj₀, hmin⟩ := Chapter12.exists_finMin_eq hq hmε
  obtain ⟨kε, hhit, -, -, -, -⟩ := theorem_14_2_4_arqpc_anchored hr hθς hA hXX₀
    assumptionHLip_zeroOuter assumptionHS0_zeroOuter (wlow := 0)
    (fun y _ => by simpa using (Constrained.targetMerit_nonneg : 0 ≤ F y))
    (mε := Chapter12.finMin 1 (fun j => (β * ρ * ε j) ^ (j + 1)) q)
    (by rw [hmin]; exact pow_pos (hε' j₀ hj₀).1 _) (fun j hj => Chapter12.finMin_le hj)
  have hmono := hr.zero_antitone hhit
  have hmem : ∀ i ≤ kε, xr i ∈ X := fun i hi => hr.mem fun l hl => hhit.2 l (hl.trans_le hi)
  have hex : ∃ i, i = kε ∨ Constrained.targetResidual f c t (xr i) < θ * ε 0 :=
    ⟨kε, Or.inl rfl⟩
  set e := Nat.find hex with he
  have he_le : e ≤ kε := Nat.find_min' hex (Or.inl rfl)
  have hres : ∀ i ≤ kε, Constrained.targetResidual f c t (xr i) ≤ ρ := fun i hi => by
    have := hmono 0 i (Nat.zero_le _) hi
    rw [hx0] at this
    exact Constrained.targetMerit_le_targetMerit_iff.1 this
  have hnot : ∀ i < e, ¬ arqpcStop F (zeroCon n) zeroOuter p q P (fun j => β * ρ * ε j) xr s σ δ d
      i := fun i hi => hhit.2 i (by omega)
  have h12 := hr.zero_algorithm_12_2_2_feasible
  have hk12 : ∀ l < e, ¬ Chapter12.arqpStop F P.toARqpParams p q (fun j => β * ρ * ε j) xr s σ δ d
      l := fun l hl => zero_arqpcStop_iff.not.1 (hnot l hl)
  -- the certificate gives the third test of (14.3.32) at a point with residual at least `θε₀`
  have hcrit : ∀ δo : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δo j) →
      Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ F (xr e)) {d | xr e + d ∈ X} q
        (fun j => β * ρ * ε j) δo →
      θ * ε 0 ≤ Constrained.targetResidual f c t (xr e) → meritCrit f c X q ε t (xr e) δo := by
    intro δo hδo happ hge j hj
    refine (happ j hj).trans ?_
    have hδ := hδo j hj
    have hεj := (hεI j hj).1
    have : β * ρ ≤ Constrained.targetResidual f c t (xr e) := by nlinarith
    have : β * ρ * ε j ≤ ε j * Constrained.targetResidual f c t (xr e) := by nlinarith
    change β * ρ * ε j * δo j ^ j / (j ! : ℝ) ≤
      ε j * Constrained.targetResidual f c t (xr e) * δo j ^ j / (j ! : ℝ)
    gcongr
  have hsucc : ∀ i < e, ((fun i => P.η₁ ≤ Optimization.arqpRatio
      (fun y => F y + zeroOuter (zeroCon n y))
      (fun k => arqpcData F (zeroCon n) zeroOuter p (xr k) (σ k)) xr s i) i ↔
        P.η₁ ≤ Optimization.arqpRatio (fun y => F y + zeroOuter (zeroCon n y))
          (fun k => arqpcData F (zeroCon n) zeroOuter p (xr k) (σ k)) xr s i) :=
    fun _ _ => Iff.rfl
  have hlow : ∀ i < e, θ * ε 0 ≤ Constrained.targetResidual f c t (xr i) := fun i hi => by
    have := Nat.find_min hex hi
    push Not at this
    exact this.2
  have hmono' : ∀ i < e, F (xr (i + 1)) ≤ F (xr i) := fun i hi =>
    hmono i (i + 1) (by omega) (by omega)
  by_cases hcase : e < kε ∨
      algorithm_14_1_1.Stop₁ F (zeroCon n) zeroOuter p q P (fun j => β * ρ * ε j) xr σ δ d e
  · -- the current radii
    refine ⟨⟨xr, e, fun i => P.η₁ ≤ Optimization.arqpRatio
      (fun y => F y + zeroOuter (zeroCon n y))
      (fun k => arqpcData F (zeroCon n) zeroOuter p (xr k) (σ k)) xr s i, δ e⟩, hx0,
      hmem e he_le, fun j hj => h12.delta_mem (fun _ _ => ⟨one_pos, le_rfl⟩) e hk12 j hj, ?_,
      hmono', hlow, hres e he_le,
      ⟨xr, s, σ, δ, δs, d, dm, kε, hr, hhit, he_le, fun _ _ => rfl, hsucc,
        Or.inl fun _ _ => rfl⟩⟩
    by_cases hlt : Constrained.targetResidual f c t (xr e) < θ * ε 0
    · exact Or.inl hlt
    · refine Or.inr (hcrit (δ e) (fun j hj =>
        (h12.delta_mem (fun _ _ => ⟨one_pos, le_rfl⟩) e hk12 j hj).1) ?_ (not_lt.1 hlt))
      rcases hcase with hlt' | h1
      · rcases Nat.find_spec hex with hek | hlt''
        · exact absurd hek (by omega)
        · exact absurd hlt'' hlt
      · have h1' : Optimization.arqpStop₁ P.toARqpParams q (fun j => β * ρ * ε j)
            (Chapter12.arqpData F p xr σ) δ d e := by
          simpa only [algorithm_14_1_1.Stop₁, zero_arqpcData_eq] using h1
        exact Optimization.MeasureTestPasses.isEpsDeltaApprox P.ς_pos (h12.witness e hk12) h1'
  · -- a Step-2 termination: the radii certified by the minimality of the model at `0`
    push Not at hcase
    obtain ⟨hke, h1⟩ := hcase
    have hek : e = kε := le_antisymm he_le hke
    have hstop : Chapter12.arqpStop F P.toARqpParams p q (fun j => β * ρ * ε j) xr s σ δ d e :=
      zero_arqpcStop_iff.1 (hek ▸ hhit.1)
    have h1' : ¬ Optimization.arqpStop₁ P.toARqpParams q (fun j => β * ρ * ε j)
        (Chapter12.arqpData F p xr σ) δ d e := by
      simpa only [algorithm_14_1_1.Stop₁, zero_arqpcData_eq] using h1
    have hstep := h12.step hk12 h1'
    have h2 : Optimization.arqpStop₂ (Chapter12.arqpData F p xr σ) s e := hstop.resolve_left h1'
    have hxA := hr.mem_compositeSublevel hnot
    have hσ0 : 0 < σ e := h12.toIsARRun.sigma_pos hk12 e le_rfl
    obtain ⟨hδ, hcert⟩ := Chapter12.isEpsDeltaApprox_of_isMinOn_zero_of_jet (h12.mem e hk12)
      (hA.contDiffAt_f (hA.subset hxA))
      (L := fun i => if i < p then ‖iteratedFDeriv ℝ (i + 1) F (xr e)‖ else 0)
      (fun i hi => by
        have hi' : i - 1 ∈ Finset.Icc 1 p := Finset.mem_Icc.2
          ⟨by have := (Finset.mem_Icc.1 hi).1; omega, by have := (Finset.mem_Icc.1 hi).2; omega⟩
        refine le_trans (le_of_eq ?_) (Chapter12.le_finMax hi')
        have hi2 := (Finset.mem_Icc.1 hi).1
        have hip := (Finset.mem_Icc.1 hi).2
        have hlt : i - 1 < p := by omega
        simp only [hlt, ite_true]
        rw [Nat.sub_add_cancel (by omega : 1 ≤ i)])
      hqp (fun j hj => ⟨(hε' j hj).1, (hε' j hj).2⟩) hσ0 (hstep.isMinOn_of_eq h2)
    refine ⟨⟨xr, e, fun i => P.η₁ ≤ Optimization.arqpRatio
      (fun y => F y + zeroOuter (zeroCon n y))
      (fun k => arqpcData F (zeroCon n) zeroOuter p (xr k) (σ k)) xr s i,
      fun j => min 1 (β * ρ * ε j / (4 * (3 * jetBound F p (xr e) + σ e)))⟩, hx0,
      hmem e he_le, fun j hj => hδ j hj, ?_, hmono', hlow, hres e he_le,
      ⟨xr, s, σ, δ, δs, d, dm, kε, hr, hhit, he_le, fun _ _ => rfl, hsucc,
        Or.inr (Or.inr ⟨hek, h1, fun _ _ => rfl⟩)⟩⟩
    by_cases hlt : Constrained.targetResidual f c t (xr e) < θ * ε 0
    · exact Or.inl hlt
    · exact Or.inr (hcrit _ (fun j hj => (hδ j hj).1) hcert (not_lt.1 hlt))

/-- **TPqp-GC runs with INNER = ARqp-SC in both phases exist** (so the class
`IsTPqpGCARqpSCRun` of `theorem_14_3_9_arqpc`, `theorem_14_3_9_arqp` and
`theorem_14_3_9_arqp_corrected` is not empty) under the book's assumptions X.CNe (`X` closed),
c.D1pLB.X and f.D1pLB.X (on an open convex `X₀ ⊇ X`), for all ARqpC constants with `θ < ς`, every
`θ ∈ (0, 1)`, `β ∈ (0, θ]`, `ε ∈ (0, 1]^{q+1}`, `β₁ ∈ (0, 1)` with `β₁ ‖c(x₀)‖ < 1` and `x₀ ∈ X`:
Phase 1 by LENq-SC with ARqp-SC calls (`exists_algorithm_14_3_2_of_phase2_anchored`), Phase 2 with
the calls of `exists_callData`. -/
theorem exists_isTPqpGCARqpSCRun (hX : IsClosed X) (hq : 1 ≤ q) (hqp : q ≤ p) {X₀ : Set ℝⁿ}
    {Lc Bc Lf Bf : ℕ → ℝ} (hc : AssumptionCD1pLBX c X X₀ p Lc Bc)
    (hf : AssumptionD1pLBX f X X₀ p Lf Bf) (P : ARqpCParams) (hθς : P.θ < P.ς) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hβ0 : 0 < β) (hβθ : β ≤ θ)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {β₁ : ℝ} (hβ₁0 : 0 < β₁)
    (hβ₁1 : β₁ < 1) {x₀ : ℝⁿ} (hx₀ : x₀ ∈ X) (hβ₁c : β₁ * ‖c x₀‖ < 1) :
    ∃ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
      IsTPqpGCARqpSCRun f c X p q P θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ := by
  obtain ⟨LA, LB, BA, BB, Lμ, Bμ, -, hνA, hμA⟩ :=
    exists_anchoredCompositeBounds_nu_mu (hq.trans hqp) hc hf
  obtain ⟨xP, δP, k₁, D, nF, nD, h, hcalls, hQ⟩ := exists_algorithm_14_3_2_of_phase2_anchored hX
    hq hqp (hνA x₀) hc.subset P hθς hθ0 hθ1 hε hβ₁0 hβ₁1 hx₀ hβ₁c (β := β)
    (Q := IsARqpSCPhase2Calls f c X p q P θ β ε) fun x₁ hx₁ hc₁ => by
      obtain ⟨D, hD, hcallsD⟩ := phase2_core_of hθ0 hθ1 hβ0 hβθ hε hx₁ hc₁
        (fun x t o => IsARqpSCCallOut (Constrained.targetMerit f c t) X p q P
          (fun j => β * Constrained.targetResidual f c t x * ε j) o.xi o.e o.succ o.δ)
        (fun x t hx hlo hhi _ => exists_callData (hμA t) hc.subset P hθς hq hqp hX hθ0 hθ1 hβ0
          hβθ hε hx hlo hhi)
      exact ⟨D, hD, fun k hk1 hk => (hcallsD k hk1 hk).2⟩
  exact ⟨xP, δP, k₁, D, nF, nD, ⟨h, hcalls, hQ⟩⟩

end Existence

/-! ### Theorem 14.3.9 on `ℝⁿ` with INNER = ARqp with unit radii (`q ≤ 2`) -/

section Unit

variable {F : ℝⁿ → ℝ} {p q : ℕ} {P : ARqpCParams} {ε : ℕ → ℝ} {xi : ℕ → ℝⁿ} {e : ℕ}
  {succ : ℕ → Prop} {δo : ℕ → ℝ}

/-- One INNER call of Phase 2 of TPqp-GC on `X = ℝⁿ` realized by ARqp with unit radii (the
Chapter 12 regime `X = ℝⁿ`, `q ≤ 2`, of the unit-radius exponents; table (14.2.12) keys that
ARqp-SC entry as "`q = 1`, `X` convex"), with its output radii: an `IsARqpUnitCall` (a prefix
of an ARqp run of Chapter 12 whose Step 2, Algorithm 12.2.3, keeps the radii `1` at the orders
`j ≤ 2`) returning the radii `1`, those of the run. -/
def IsARqpUnitCallOut (F : ℝⁿ → ℝ) (p q : ℕ) (P : ARqpCParams) (ε : ℕ → ℝ) (xi : ℕ → ℝⁿ)
    (e : ℕ) (succ : ℕ → Prop) (δo : ℕ → ℝ) : Prop :=
  IsARqpUnitCall F p q P ε xi e succ ∧ ∀ j ∈ Finset.Icc 1 q, δo j = 1

open Classical in
/-- **The INNER contract of one ARqp call with unit radii** ([cartis2022evaluation],
Lemmas 12.2.13 and 14.2.3 with unit radii), for every call `IsARqpUnitCallOut` on an objective `F`
with anchored bounds (constants `L`, `X₀ = ℝⁿ`) on a set containing the sublevel set of `F` at
the start of the call, `θ < ς` and `1 ≤ q ≤ p`: unsuccessful iterations do not move,
`e ≤ κ_uns |𝒮| + κ_unc` (`κ_unc = arqpUnitKappaUnc P L p`), and, for tolerances in `(0, 1]`,
every successful iteration that is not the last one, or the last one of a call ending at a point
failing INNER's test with radii `1`, decreases `F` by at least `η₁ κ_{Δm} ε_l^{π_l}` with the
unit-radius exponents `π_l = (p+1)/(p-l+1)`. -/
theorem IsARqpUnitCallOut.contract {S : Set ℝⁿ} {L : ℕ → ℝ}
    (hF : AnchoredCompositeBounds F (zeroCon n) univ S p L (fun _ => 0)) (hθς : P.θ < P.ς)
    (hq : 1 ≤ q) (hqp : q ≤ p) (h : IsARqpUnitCallOut F p q P ε xi e succ δo)
    (hS : ∀ y, F y ≤ F (xi 0) → y ∈ S) :
    (∀ i < e, ¬ succ i → xi (i + 1) = xi i) ∧
    (e : ℝ) ≤ arqpSCKappaUns P * ((Finset.range e).filter succ).card + arqpUnitKappaUnc P L p ∧
    ((∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) → ∀ i < e, succ i →
      (i + 1 < e ∨ ¬ Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ F (xi e))
        {d | xi e + d ∈ (univ : Set ℝⁿ)} q ε δo) →
      ∃ l ∈ Finset.Icc 1 q, arqpRowKappaDecr True P L p q * ε l ^ Chapter12.arqpPiOf True p l ≤
        F (xi i) - F (xi (i + 1))) := by
  obtain ⟨⟨x, s, σ, δr, δs, d, dm, kε, hr, hδs, hhit, he, hxi, hsucc⟩, hδo⟩ := h
  have hAμ : ∀ y ∈ (univ : Set ℝⁿ), F y ≤ F (x 0) → y ∈ S := fun y _ hy =>
    hS y (by rwa [hxi 0 (Nat.zero_le _)])
  have hone := Chapter12.arqp_delta_eq_one hr (fun _ _ => rfl) hδs
  have hnot : ∀ i < e, ¬ Chapter12.arqpStop F P.toARqpParams p q ε x s σ δr d i :=
    fun i hi => hhit.2 i (lt_of_lt_of_le hi he)
  refine ⟨fun i hi hs => ?_, ?_, fun hε i hi hs hcont => ?_⟩
  · rw [hxi i hi.le, hxi (i + 1) hi]
    exact hr.toIsARRun.eq_of_not_succ (fun l hl => hnot l (lt_of_le_of_lt hl hi))
      (not_le.1 ((hsucc i hi).not.1 hs))
  · -- Lemma 14.2.3
    have h3 := hr.toIsARRun.le_succ_count (k := e) hnot
      (Chapter12.arqp_sigma_le_anchored hF.toTop (subset_univ _) hAμ hr e hnot).2
    set ρ := fun i => P.η₁ ≤ Chapter12.arqpRho F p x s σ i
    have hS' : (Finset.range e).filter succ = (Finset.range e).filter ρ :=
      Finset.filter_congr fun i hi => hsucc i (Finset.mem_range.1 hi)
    have hcard' := card_successSet_le ρ e
    have hκ := arqpSCKappaUns_nonneg P
    rw [hS']
    unfold arqpUnitKappaUnc
    unfold arqpSCKappaUns at hκ ⊢
    nlinarith
  · -- Lemma 12.2.13 with unit radii
    have h1 : ¬ Optimization.arqpStop₁ P.toARqpParams q ε (Chapter12.arqpData F p x σ) δr d
        (i + 1) := by
      intro h1
      by_cases hlt : i + 1 < e
      · exact hnot (i + 1) hlt (Or.inl h1)
      · have hie : i + 1 = e := by omega
        rw [hie] at h1
        refine (hcont.resolve_left hlt) fun j hj => ?_
        have happ := Optimization.MeasureTestPasses.isEpsDeltaApprox P.ς_pos (hr.witness e hnot) h1
        rw [hxi e le_rfl, hδo j hj, ← hone e hnot j hj]
        exact happ j hj
    have hdec := (Chapter12.lemma_12_2_13_anchored hF.toTop (subset_univ _) hAμ hq hqp hθς hε hr
      (k := i) (fun l hl => hnot l (by omega)) ((hsucc i hi).1 hs) h1 (u := True)
      ⟨fun _ => hone (i + 1) (fun l hl => hnot l (by omega)), fun h' => absurd trivial h'⟩).2
    obtain ⟨l, hl, hmin⟩ := Chapter12.exists_finMin_eq hq
      (u := fun j => ε j ^ Chapter12.arqpPiOf True p j) (b := 1) fun j hj =>
        Real.rpow_le_one (hε j hj).1.le (hε j hj).2 (Chapter12.arqpPiOf_nonneg True p j)
    refine ⟨l, hl, ?_⟩
    rw [hmin] at hdec
    rw [hxi i hi.le, hxi (i + 1) hi]
    unfold arqpRowKappaDecr
    rw [mul_assoc]
    exact hdec

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {θ β : ℝ} {x₁ : ℝⁿ} {D : TPqpSeq n}

/-- **The INNER calls of Phase 2 of TPqp-GC on `X = ℝⁿ` are ARqp runs with unit radii**: for every
outer iteration `k ≥ 1` reached, the `k`-th call is an `IsARqpUnitCallOut` on `μ(·, t_k)` with
tolerances `β ‖r(x_k, t_k)‖ ε_j`, cut at any iteration. -/
def IsARqpUnitPhase2Calls (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (p q : ℕ) (P : ARqpCParams) (θ β : ℝ)
    (ε : ℕ → ℝ) (D : TPqpSeq n) : Prop :=
  ∀ k, 1 ≤ k → D.Before f c univ q θ ε k →
    IsARqpUnitCallOut (Constrained.targetMerit f c (D.t k)) p q P
      (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) (D.xi k) (D.e k)
      (D.succ k) (D.δ (k + 1))

/-- **Every Phase-2 run of TPqp-GC on `ℝⁿ` whose INNER calls are ARqp runs with unit radii
satisfies the INNER contract keyed on INNER's own test** (`IsInnerPhaseRunStrong`,
[cartis2022evaluation], Lemmas 12.2.13 and 14.2.3 with unit radii), with the unit-radius exponents
`π_l = (p+1)/(p-l+1)`, the `t`-independent constants `κ_decr = arqpRowKappaDecr True P L p q`,
`κ_uns = arqpSCKappaUns P`, `κ_unc = arqpUnitKappaUnc P L p` and radii `ρ_j = 1`, when every
`μ(·, t)` has anchored bounds with constants `L` on `𝓛_μ(t)` (`X₀ = ℝⁿ`), `θ < ς` and
`1 ≤ q ≤ p`. -/
theorem IsARqpUnitPhase2Calls.isInnerPhaseRunStrong (h : IsTPqpGCPhase2 f c univ q θ β ε x₁ D)
    (hcalls : IsARqpUnitPhase2Calls f c p q P θ β ε D) {L : ℕ → ℝ}
    (hμ : ∀ t, AnchoredCompositeBounds (Constrained.targetMerit f c t) (zeroCon n) univ
      (muSublevel f c univ t) p L (fun _ => 0)) (hθς : P.θ < P.ς) (hq : 1 ≤ q) (hqp : q ≤ p) :
    IsInnerPhaseRunStrong f c univ q θ β ε D (arqpRowKappaDecr True P L p q) (arqpSCKappaUns P)
      (arqpUnitKappaUnc P L p) (Chapter12.arqpPiOf True p) (fun _ => 1) := by
  have hC := fun k (hk1 : 1 ≤ k) (hk : D.Before f c univ q θ ε k) =>
    (hcalls k hk1 hk).contract (hμ (D.t k)) hθς hq hqp
      (fun y hy => h.call_sublevel hk1 hk y (mem_univ y) hy)
  refine ⟨fun k hk1 hk => (hC k hk1 hk).2.1, fun k hk1 hk => (hC k hk1 hk).1,
    fun k hk1 hk i hi hs hcont _ => ?_, fun k hk1 hk _ _ j hj => ((hcalls k hk1 hk).2 j hj).ge⟩
  have hcont' : i + 1 < D.e k ∨ ¬ Optimization.IsEpsDeltaApprox
      (ftaylorSeries ℝ (Constrained.targetMerit f c (D.t k)) (D.xi k (D.e k)))
      {d | D.xi k (D.e k) + d ∈ (univ : Set ℝⁿ)} q
      (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) (D.δ (k + 1)) := by
    rw [h.inner_end k hk1 hk]
    exact hcont
  -- the tolerances of the call lie in `(0, 1]`
  have hrk : θ * ε 0 ≤ Constrained.targetResidual f c (D.t k) (D.x k) := by
    have := h.inner_residual_ge k hk1 hk 0 (by omega)
    rwa [h.inner_zero k hk1 hk] at this
  have hrk1 : Constrained.targetResidual f c (D.t k) (D.x k) ≤ 1 :=
    ((h.isTargetSequence hk).residual_le h.θ_lt_one.le h.ε₀_pos.le hk1 le_rfl).trans
      (h.ε_le_one 0 (by simp))
  have hε' : ∀ j ∈ Finset.Icc 1 q,
      β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j ∈ Ioc 0 1 := fun j hj => by
    have hεj := h.ε_pos' hj
    have hεj1 := h.ε_le_one j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
    have hβ1 : β ≤ 1 := h.β_le_θ.trans h.θ_lt_one.le
    have hr0 : 0 < Constrained.targetResidual f c (D.t k) (D.x k) :=
      lt_of_lt_of_le (mul_pos h.θ_pos h.ε₀_pos) hrk
    refine ⟨by have := h.β_pos; positivity, ?_⟩
    calc β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j ≤ 1 * 1 * 1 := by
          gcongr
      _ = 1 := by ring
  exact (hC k hk1 hk).2.2 hε' i hi hs hcont'

end Unit

/-! ### The unit-radius theorem -/

section UnitTheorem

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {p q : ℕ}

/-- **A run of TPqp-GC on `X = ℝⁿ` with INNER = ARqp with unit radii in both phases**
([cartis2022evaluation], Algorithm 14.3.2 with `X = ℝⁿ`, `q ≤ 2`, INNER = ARqp of Chapter 12 with
Step 2 by Algorithm 12.2.3): a run (`algorithm_14_3_2`) whose Phase-1 INNER calls are ARqp runs
with unit radii on `ν` using `nF₁ k` evaluations of `c` and `nD₁ k` of its derivatives
(`IsARqpUnitOutputCost`), and whose Phase-2 INNER calls are ARqp runs with unit radii on
`μ(·, t_k)`, cut at any iteration (`IsARqpUnitPhase2Calls`). -/
structure IsTPqpGCARqpUnitRun (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (p q : ℕ) (P : ARqpCParams)
    (θ β₁ β : ℝ) (ε : ℕ → ℝ) (x₀ : ℝⁿ) (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ)
    (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ) : Prop where
  /-- The TPqp-GC run on `ℝⁿ`. -/
  run : algorithm_14_3_2 f c univ q θ β₁ β ε x₀ xP δP k₁ D
  /-- The Phase-1 INNER calls are ARqp runs with unit radii with their evaluation counts. -/
  phase1 : ∀ k, 1 ≤ k → k ≤ k₁ → IsARqpUnitOutputCost (phi2 c) p q P
    (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) (xP (k - 1)) (xP k) (δP k) (nF₁ k)
      (nD₁ k)
  /-- The Phase-2 INNER calls are ARqp runs with unit radii. -/
  phase2 : ‖c (xP k₁)‖ ≤ θ * ε 0 → IsARqpUnitPhase2Calls f c p q P θ β ε D

variable {θ β : ℝ} {ε : ℕ → ℝ} {P : ARqpCParams}

open Classical in
/-- **One INNER call of Phase 2 on `ℝⁿ` by ARqp with unit radii exists** (`1 ≤ q ≤ min(2, p)`)
from every `(x, t)` with `θε₀ ≤ ‖r(x, t)‖ ≤ ε₀`: the ARqp run of `unit_core_anchored` on `μ(·, t)`
with tolerances `β ‖r(x, t)‖ ε` (Step 2 by Algorithm 12.2.3, radii `1`), stopped at its termination
or as soon as `‖r(·, t)‖ < θε₀`, returning the radii `1`; its output satisfies (14.3.32). -/
theorem exists_unitCallOut {t : ℝ} {L : ℕ → ℝ}
    (hμ : AnchoredCompositeBounds (Constrained.targetMerit f c t) (zeroCon n) univ
      (muSublevel f c univ t) p L (fun _ => 0)) (P : ARqpCParams) (hθς : P.θ < P.ς)
    (hq : 1 ≤ q) (hq2 : q ≤ 2) (hqp : q ≤ p) (hθ0 : 0 < θ) (hβ0 : 0 < β) (hβθ : β ≤ θ)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {x : ℝⁿ}
    (hlo : θ * ε 0 ≤ Constrained.targetResidual f c t x)
    (hhi : Constrained.targetResidual f c t x ≤ ε 0) :
    ∃ o : CallOut n, o.xi 0 = x ∧ o.xi o.e ∈ (univ : Set ℝⁿ) ∧
      (∀ j ∈ Finset.Icc 1 q, 0 < o.δ j ∧ o.δ j ≤ 1) ∧
      (Constrained.targetResidual f c t (o.xi o.e) < θ * ε 0 ∨
        meritCrit f c univ q ε t (o.xi o.e) o.δ) ∧
      (∀ i < o.e, Constrained.targetMerit f c t (o.xi (i + 1)) ≤
        Constrained.targetMerit f c t (o.xi i)) ∧
      (∀ i < o.e, θ * ε 0 ≤ Constrained.targetResidual f c t (o.xi i)) ∧
      Constrained.targetResidual f c t (o.xi o.e) ≤ Constrained.targetResidual f c t x ∧
      IsARqpUnitCallOut (Constrained.targetMerit f c t) p q P
        (fun j => β * Constrained.targetResidual f c t x * ε j) o.xi o.e o.succ o.δ := by
  set ρ := Constrained.targetResidual f c t x with hρ
  have hεI : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 := fun j hj =>
    hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  have hε₀ := hε 0 (by simp)
  have hρ0 : 0 < ρ := lt_of_lt_of_le (mul_pos hθ0 hε₀.1) hlo
  have hε' : ∀ j ∈ Finset.Icc 1 q, 0 < β * ρ * ε j ∧ β * ρ * ε j ≤ 1 := by
    intro j hj
    obtain ⟨h1, h2⟩ := hεI j hj
    refine ⟨by positivity, ?_⟩
    have : β * ρ ≤ 1 := by nlinarith
    nlinarith
  have hS : ∀ y, Constrained.targetMerit f c t y ≤ Constrained.targetMerit f c t x →
      y ∈ muSublevel f c univ t := fun y hyx =>
    ⟨mem_univ y, (Constrained.targetMerit_le_targetMerit_iff.1 hyx).trans (hhi.trans hε₀.2)⟩
  obtain ⟨xr, s, σ, δr, δs, d, dm, kε, hr, hδs, hhit, hx0, hmono, hcert⟩ :=
    unit_core_anchored hμ (flow := 0) (fun _ => Constrained.targetMerit_nonneg) P hθς hq hq2 hqp x
      hS hε'
  have hex : ∃ i, i = kε ∨ Constrained.targetResidual f c t (xr i) < θ * ε 0 := ⟨kε, Or.inl rfl⟩
  set e := Nat.find hex with he
  have he_le : e ≤ kε := Nat.find_min' hex (Or.inl rfl)
  have hres : ∀ i ≤ kε, Constrained.targetResidual f c t (xr i) ≤ ρ := fun i hi => by
    have := hmono 0 i (Nat.zero_le _) hi
    rw [hx0] at this
    exact Constrained.targetMerit_le_targetMerit_iff.1 this
  refine ⟨⟨xr, e, fun i => P.η₁ ≤ Chapter12.arqpRho (Constrained.targetMerit f c t) p xr s σ i,
    fun _ => 1⟩, hx0, mem_univ _, fun _ _ => ⟨one_pos, le_rfl⟩, ?_,
    fun i (hi : i < e) => hmono i (i + 1) (by omega) (by omega), fun i (hi : i < e) => ?_,
    hres e he_le, ⟨⟨xr, s, σ, δr, δs, d, dm, kε, hr, hδs, hhit, he_le, fun _ _ => rfl,
      fun _ _ => Iff.rfl⟩, fun _ _ => rfl⟩⟩
  · rcases Nat.find_spec hex with hek | hlt
    · by_cases hlt : Constrained.targetResidual f c t (xr e) < θ * ε 0
      · exact Or.inl hlt
      · refine Or.inr fun j hj => ?_
        have h1 := hcert j hj
        rw [← hek] at h1
        refine h1.trans ?_
        have hεj := (hεI j hj).1
        have : β * ρ ≤ Constrained.targetResidual f c t (xr e) := by nlinarith
        have : β * ρ * ε j ≤ ε j * Constrained.targetResidual f c t (xr e) := by nlinarith
        change β * ρ * ε j * 1 ^ j / (j ! : ℝ) ≤
          ε j * Constrained.targetResidual f c t (xr e) * 1 ^ j / (j ! : ℝ)
        gcongr
    · exact Or.inl hlt
  · have := Nat.find_min hex hi
    push Not at this
    exact this.2

/-- **TPqp-GC runs on `ℝⁿ` with INNER = ARqp with unit radii in both phases exist** for
`1 ≤ q ≤ min(2, p)` (so the class `IsTPqpGCARqpUnitRun` of `theorem_14_3_9_arqp_unit` and
`theorem_14_3_9_arqp_unit_corrected` is not empty there), under c.D1pLB.X and f.D1pLB.X on
`X = X₀ = ℝⁿ`, for all ARqpC constants with `θ < ς`, every `θ ∈ (0, 1)`, `β ∈ (0, θ]`,
`ε ∈ (0, 1]^{q+1}`, `β₁ ∈ (0, 1)` with `β₁ ‖c(x₀)‖ < 1`: Phase 1 by LENq-SC with unit-radius ARqp
calls (`exists_algorithm_14_3_1_complexity_unit_anchored`), Phase 2 with the calls of
`exists_unitCallOut` (`phase2_core_of`). -/
theorem exists_isTPqpGCARqpUnitRun (hq : 1 ≤ q) (hq2 : q ≤ 2) (hqp : q ≤ p)
    {Lc Bc Lf Bf : ℕ → ℝ} (hc : AssumptionCD1pLBX c univ univ p Lc Bc)
    (hf : AssumptionD1pLBX f univ univ p Lf Bf) (P : ARqpCParams) (hθς : P.θ < P.ς)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (hβθ : β ≤ θ)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {β₁ : ℝ} (hβ₁0 : 0 < β₁)
    (hβ₁1 : β₁ < 1) (x₀ : ℝⁿ) (hβ₁c : β₁ * ‖c x₀‖ < 1) :
    ∃ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
      IsTPqpGCARqpUnitRun f c p q P θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ := by
  obtain ⟨LA, LB, BA, BB, Lμ, Bμ, -, hνA, hμA⟩ :=
    exists_anchoredCompositeBounds_nu_mu (hq.trans hqp) hc hf
  have hε₁ : ∀ j ∈ Finset.range (q + 1), 0 < phase1Tol θ ε j ∧ phase1Tol θ ε j ≤ 1 := by
    intro j hj
    by_cases h0 : j = 0
    · subst h0
      obtain ⟨h1, h2⟩ := hε 0 hj
      simp only [phase1Tol_zero]
      exact ⟨mul_pos hθ0 h1, by nlinarith⟩
    · rw [phase1Tol_of_ne θ ε h0]
      exact hε j hj
  obtain ⟨xP, δP, nF₁, nD₁, k₁, hxP0, hrun, hhit, -, hcalls, -, -⟩ :=
    exists_algorithm_14_3_1_complexity_unit_anchored hq hq2 hqp (hνA x₀) P hθς hε₁ hβ₁0 hβ₁1 x₀
      (fun y hy => ⟨mem_univ y, hy⟩) hβ₁c
  by_cases hc1 : ‖c (xP k₁)‖ ≤ θ * ε 0
  · obtain ⟨D, hD, hcallsD⟩ := phase2_core_of (X := univ) hθ0 hθ1 hβ0 hβθ hε (mem_univ (xP k₁))
      hc1 (fun x t o => IsARqpUnitCallOut (Constrained.targetMerit f c t) p q P
        (fun j => β * Constrained.targetResidual f c t x * ε j) o.xi o.e o.succ o.δ)
      (fun x t _ hlo hhi _ => exists_unitCallOut (hμA t) P hθς hq hq2 hqp hθ0 hβ0 hβθ hε hlo hhi)
    exact ⟨xP, δP, k₁, D, nF₁, nD₁, ⟨⟨hxP0, hrun, hhit, fun _ => hD⟩, hcalls,
      fun _ k hk1 hk => (hcallsD k hk1 hk).2⟩⟩
  · exact ⟨xP, δP, k₁, ⟨fun _ => x₀, fun _ => 0, fun _ _ => 0, fun _ _ => x₀, fun _ => 0,
      fun _ _ => False⟩, nF₁, nD₁, ⟨⟨hxP0, hrun, hhit, fun h => absurd h hc1⟩, hcalls,
      fun h => absurd h hc1⟩⟩

/-- The unit-radius exponents: `1 < (p+1)/(p-j+1) ≤ (p+1)/(p-q+1)` for `j ∈ [1 : q]`,
`q ≤ p`. -/
theorem arqpPiOf_true_mem_Icc {p q j : ℕ} (hqp : q ≤ p) (hj : j ∈ Finset.Icc 1 q) :
    1 < Chapter12.arqpPiOf True p j ∧
      Chapter12.arqpPiOf True p j ≤ Chapter12.arqpPiOf True p q := by
  rw [Chapter12.arqpPiOf_of_pos trivial, Chapter12.arqpPiOf_of_pos trivial]
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have h0 : (0 : ℝ) < ((p - j + 1 : ℕ) : ℝ) := by positivity
  have h0' : (0 : ℝ) < ((p - q + 1 : ℕ) : ℝ) := by positivity
  have h1 : ((p - j + 1 : ℕ) : ℝ) < ((p + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have h2 : ((p - q + 1 : ℕ) : ℝ) ≤ ((p - j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  exact ⟨(one_lt_div h0).2 h1, div_le_div_of_nonneg_left (by positivity) h0' h2⟩

/-- For `q = p ≤ 2` the unit-radius exponents `(p+1)/(p-j+1)` are the "otherwise" exponents
`j(p+1)/p` of (14.2.12). -/
theorem arqpPiOf_true_eq_false {q j : ℕ} (hq2 : q ≤ 2) (hj : j ∈ Finset.Icc 1 q) :
    Chapter12.arqpPiOf True q j = Chapter12.arqpPiOf False q j := by
  rw [Chapter12.arqpPiOf_of_pos trivial, Chapter12.arqpPiOf_of_neg not_false]
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  interval_cases q <;> interval_cases j <;> norm_num

/-- `κ_C = (|log γ₁| + log(σ_max/σ₀))/log γ₂ + 2 ≥ 0` (Theorem 12.2.14). -/
theorem kappaCARqp_nonneg (P : ARqpCParams) (L : ℕ → ℝ) (p : ℕ) :
    0 ≤ Chapter12.kappaCARqp P.toARqpParams L p := by
  unfold Chapter12.kappaCARqp
  have := P.log_γ₂_pos
  have : 0 ≤ Real.log (Optimization.arSigmaMax P.toARParams (L p) / P.σ₀) :=
    Real.log_nonneg ((one_le_div P.σ₀_pos).2 (Optimization.σ₀_le_arSigmaMax _ _))
  positivity

/-- `κ_unc ≥ 0` (Lemma 14.2.3 for ARqp runs). -/
theorem arqpUnitKappaUnc_nonneg (P : ARqpCParams) (L : ℕ → ℝ) (p : ℕ) :
    0 ≤ arqpUnitKappaUnc P L p := by
  unfold arqpUnitKappaUnc
  have := arqpSCKappaUns_nonneg P
  have := P.log_γ₂_pos
  have : 0 ≤ Real.log (Optimization.arSigmaMax P.toARParams (L p) / P.σ₀) :=
    Real.log_nonneg ((one_le_div P.σ₀_pos).2 (Optimization.σ₀_le_arSigmaMax _ _))
  positivity

/-- **Theorem 14.3.9 on `ℝⁿ` with INNER = ARqp with unit radii, relative to an order `O`** (the
core of `theorem_14_3_9_arqp_unit` and `theorem_14_3_9_arqp_unit_corrected`). Under c.D1pLB.X and
f.D1pLB.X on `X = X₀ = ℝⁿ`, f.B.Fb, `1 ≤ q ≤ p` (the class is non-empty for `q ≤ 2`,
`exists_isTPqpGCARqpUnitRun`; for `q > 2` it may be empty, since Algorithm 12.2.3 may halve the
radii of order `j ≥ 3`) and the constants of `theorem_14_3_9_arqpc`, there are constants
`κ_F, κ_D ≥ 0` such that for all tolerances and every TPqp-GC run with INNER = ARqp with unit
radii (`IsTPqpGCARqpUnitRun`), and every `O` with
`ε₀^{-1} ≤ O`, `ε₀^{1-π_l} ε_l^{-π_l} ≤ O` (`π_l = (p+1)/(p-l+1)`) and `(ε₀ ε_j)^{-1} ≤ O`, the
evaluation counts of both phases are at most `κ_F O` and `κ_D O`, Phase 2 (if entered)
terminating. -/
theorem exists_const_order_arqp_unit (hq : 1 ≤ q) (hqp : q ≤ p)
    {Lc Bc Lf Bf : ℕ → ℝ} (hc : AssumptionCD1pLBX c univ univ p Lc Bc)
    (hf : AssumptionD1pLBX f univ univ p Lf Bf) {βF flow fup : ℝ}
    (hB : Chapter07.AssumptionBFb f c univ βF flow fup) (P : ARqpCParams) (hθς : P.θ < P.ς)
    {θ β β₁ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (x₀ : ℝⁿ) :
    ∃ κF κD : ℝ, 0 ≤ κF ∧ 0 ≤ κD ∧
      ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ βF →
      ∀ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCARqpUnitRun f c p q P θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ → ∀ O : ℝ,
        (ε 0)⁻¹ ≤ O →
        (∀ l ∈ Finset.Icc 1 q, ε 0 ^ (1 - Chapter12.arqpPiOf True p l) *
          ε l ^ (-Chapter12.arqpPiOf True p l) ≤ O) →
        (∀ j ∈ Finset.Icc 1 q, (ε 0 * ε j)⁻¹ ≤ O) →
        (θ * ε 0 < ‖c (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤ κF * O ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ κD * O) ∧
        (‖c (xP k₁)‖ ≤ θ * ε 0 → ∃ kε, D.IsEnd f c univ q θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤ κF * O ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤ κD * O) := by
  have hp : 1 ≤ p := hq.trans hqp
  obtain ⟨LA, LB, BA, BB, Lμ, Bμ, h1, hνA, hμA⟩ := exists_anchoredCompositeBounds_nu_mu hp hc hf
  set Lν := nuAnchoredConst LA LB BA BB ‖c x₀‖ with hLν
  set L := anchoredConst Lμ Bμ with hL
  have hLp : 1 ≤ L p := (hμA 0).one_le
  have hκ : 0 < arqpRowKappaDecr True P L p q :=
    mul_pos P.η₁_pos (Chapter12.arqpKappaDmOf_pos True P.σmin_pos hθς hLp)
  obtain ⟨CF, CD, hCF, hCD, hord⟩ := IsTPqpGCPhase2.exists_const_order_of_strong (f := f) (c := c)
    (X := univ) (θ := θ) (β := β) hq (πmax := Chapter12.arqpPiOf True p q) hκ
    (arqpSCKappaUns_nonneg P) (arqpUnitKappaUnc_nonneg P L p) one_pos (finMax_one_pos (B := Bf))
    (abs_nonneg (fup - flow + 1)) zero_le_one hθ0 hθ1 hβ0
  -- the Phase-1 constants
  have hLνp : 1 ≤ Lν p := (hνA x₀).one_le
  set κF₁ := Chapter12.kappaAARqpOf True P.toARqpParams Lν p q with hκF₁
  set κD₁ := Chapter12.kappaSARqpOf True P.toARqpParams Lν p q with hκD₁
  have hκD : 0 < κD₁ := Chapter12.kappaSARqpOf_pos True P.σmin_pos hθς hLνp
  have hκF : 0 ≤ κF₁ := by
    rw [hκF₁]
    unfold Chapter12.kappaAARqpOf
    have := P.log_γ₂_pos
    have := hκD.le
    positivity
  have hκC := kappaCARqp_nonneg P Lν p
  set W := ∑ j ∈ Finset.Icc 1 q, |β₁ ^ (1 - 2 * Chapter12.arqpPiOf True p j) /
    (β₁ ^ (1 - Chapter12.arqpPiOf True p j) - 1) * θ ^ (1 - Chapter12.arqpPiOf True p j)| with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set c₁ := 1 + ‖c x₀‖ / (θ * |Real.log β₁|) with hc₁
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  refine ⟨1 / 2 * κF₁ * ‖c x₀‖ * W + Chapter12.kappaCARqp P.toARqpParams Lν p * c₁ + CF,
    1 / 2 * κD₁ * ‖c x₀‖ * W + 2 * c₁ + CD, by positivity, by positivity,
    fun ε hε hεβ xP δP k₁ D nF₁ nD₁ hR O hO0 hOT hOB => ?_⟩
  have h := hR.run
  have hε₀ := hε 0 (by simp)
  have hO1 : 1 ≤ O := ((one_le_inv₀ hε₀.1).2 hε₀.2).trans hO0
  have hOnn : 0 ≤ O := zero_le_one.trans hO1
  have hβ₁0 := h.phase1.β_pos
  have hβ₁1 := h.phase1.β_lt_one
  have hεI : ∀ l ∈ Finset.Icc 1 q, 0 < ε l ∧ ε l ≤ 1 := fun l hl =>
    hε l (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hl).2))
  -- Phase 1: the number of iterations and the additive cost contract
  have hk₁ : (k₁ : ℝ) ≤ c₁ * O := by
    obtain ⟨⟨kmax, hhit, hkmax, -⟩, -⟩ := theorem_14_3_3 h.phase1
    rw [hhit.unique h.phase1_end, phase1Tol_zero, h.start] at hkmax
    have h1 : (k₁ : ℝ) ≤ 1 + ‖c x₀‖ / (θ * ε 0 * |Real.log β₁|) :=
      (Nat.cast_le.2 hkmax).trans (ceil_log_div_le (mul_pos hθ0 hε₀.1) (norm_nonneg _) hβ₁0 hβ₁1)
    have h2 : ‖c x₀‖ / (θ * ε 0 * |Real.log β₁|) = ‖c x₀‖ / (θ * |Real.log β₁|) * (ε 0)⁻¹ := by
      field_simp
    have h3 : 0 ≤ ‖c x₀‖ / (θ * |Real.log β₁|) := by positivity
    calc (k₁ : ℝ) ≤ 1 + ‖c x₀‖ / (θ * |Real.log β₁|) * (ε 0)⁻¹ := h2 ▸ h1
      _ ≤ O + ‖c x₀‖ / (θ * |Real.log β₁|) * O := by gcongr
      _ = c₁ * O := by rw [hc₁]; ring
  have hcost : ∀ k ∈ Finset.Icc 1 k₁,
      (nF₁ k : ℝ) ≤ innerEvalBound κF₁ (Chapter12.arqpPiOf True p) q (phi2 c (xP (k - 1)))
        (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) +
          Chapter12.kappaCARqp P.toARqpParams Lν p ∧
      (nD₁ k : ℝ) ≤ innerEvalBound κD₁ (Chapter12.arqpPiOf True p) q (phi2 c (xP (k - 1)))
        (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) + 2 := by
    intro k hk
    obtain ⟨hk1, hkk⟩ := Finset.mem_Icc.1 hk
    have hck : ‖c (xP (k - 1))‖ ≤ ‖c x₀‖ := by
      have := h.phase1.norm_le_pow_mul (Nat.zero_le (k - 1)) fun l hl =>
        h.phase1_end.2 l (by omega)
      rw [h.start] at this
      exact this.trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hβ₁0.le hβ₁1.le))
    have hcpos : θ * ε 0 < ‖c (xP (k - 1))‖ := by
      have hns := h.phase1_end.2 (k - 1) (by omega)
      exact not_le.1 fun h' => hns (Or.inl (by rw [phase1Tol_zero]; exact h'))
    have hβc : β₁ * ‖c x₀‖ < 1 := by have := h.phase1.β_mul_lt_one; rwa [h.start] at this
    have hε' : ∀ j ∈ Finset.Icc 1 q, 0 < β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j ∧
        β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j ≤ 1 := fun j hj => by
      rw [phase1Tol_of_ne θ ε (by have := (Finset.mem_Icc.1 hj).1; omega)]
      have hcp : 0 < ‖c (xP (k - 1))‖ := lt_of_le_of_lt (mul_pos hθ0 hε₀.1).le hcpos
      obtain ⟨hej0, hej1⟩ := hεI j hj
      refine ⟨by positivity, ?_⟩
      have : β₁ * ‖c (xP (k - 1))‖ ≤ 1 := by nlinarith
      calc β₁ * ‖c (xP (k - 1))‖ * ε j ≤ 1 * 1 := by gcongr
        _ = 1 := one_mul 1
    exact (hR.phase1 k hk1 hkk).cost_le_add_anchored (hνA x₀)
      (fun y => by rw [phi2_apply]; positivity) hθς hq hqp hε'
      (fun y hyk => ⟨mem_univ y, (norm_le_of_phi2_le hyk).trans hck⟩)
  have hπ1 : ∀ l ∈ Finset.Icc 1 q, 1 < Chapter12.arqpPiOf True p l := fun l hl =>
    (arqpPiOf_true_mem_Icc hqp hl).1
  have hF1 := (lemma_14_3_7_add h hθ0 hπ1 hκF fun k hk => (hcost k hk).1).trans
    (add_le_add (phase1Bound_le hκF (norm_nonneg _) (fun j hj => (hε j hj).1) hOT) le_rfl)
  have hD1 := (lemma_14_3_7_add h hθ0 hπ1 hκD.le fun k hk => (hcost k hk).2).trans
    (add_le_add (phase1Bound_le hκD.le (norm_nonneg _) (fun j hj => (hε j hj).1) hOT) le_rfl)
  rw [← hW] at hF1 hD1
  have hF1' : ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤
      (1 / 2 * κF₁ * ‖c x₀‖ * W + Chapter12.kappaCARqp P.toARqpParams Lν p * c₁) * O := by
    calc _ ≤ 1 / 2 * κF₁ * ‖c x₀‖ * W * O + k₁ * Chapter12.kappaCARqp P.toARqpParams Lν p := hF1
      _ ≤ 1 / 2 * κF₁ * ‖c x₀‖ * W * O + c₁ * O * Chapter12.kappaCARqp P.toARqpParams Lν p := by
          gcongr
      _ = _ := by ring
  have hD1' : ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ (1 / 2 * κD₁ * ‖c x₀‖ * W + 2 * c₁) * O := by
    calc _ ≤ 1 / 2 * κD₁ * ‖c x₀‖ * W * O + k₁ * 2 := hD1
      _ ≤ 1 / 2 * κD₁ * ‖c x₀‖ * W * O + c₁ * O * 2 := by gcongr
      _ = _ := by ring
  refine ⟨fun _ => ⟨hF1'.trans (by nlinarith), hD1'.trans (by nlinarith)⟩, fun hc1 => ?_⟩
  -- Phase 2
  have h2 := h.phase2 hc1
  have hin := ((hR.phase2 hc1).isInnerPhaseRunStrong h2 hμA hθς hq hqp).mono_radius
    (ρ' := fun _ => 1 * 1) fun j _ => le_of_eq (one_mul 1)
  obtain ⟨kε, hend, hF2, hD2⟩ := hord h2 hin (fun _ _ => one_pos) (fun l hl =>
      ⟨Chapter12.arqpPiOf_nonneg True p l, (arqpPiOf_true_mem_Icc hqp hl).2⟩) hB hεβ
    (le_abs_self _) (fun _ _ => hf.contDiffAt_of_le hqp (mem_univ _))
    (fun _ _ => hc.contDiffAt_of_le hqp (mem_univ _))
    (fun _ hy _ => hf.norm_iteratedFDeriv_le_finMax hqp (hf.subset hy)) hO0 hOT
    (fun j hj => by rw [one_pow, mul_one, one_mul]; exact hOB j hj)
  refine ⟨kε, hend, ?_, ?_⟩
  · calc _ ≤ (1 / 2 * κF₁ * ‖c x₀‖ * W + Chapter12.kappaCARqp P.toARqpParams Lν p * c₁) * O +
          CF * O := add_le_add hF1' hF2
      _ = _ := by ring
  · calc _ ≤ (1 / 2 * κD₁ * ‖c x₀‖ * W + 2 * c₁) * O + CD * O := add_le_add hD1' hD2
      _ = _ := by ring

/-- **Theorem 14.3.9** of [cartis2022evaluation] **on `ℝⁿ` for every run with INNER = ARqp with
unit radii (`q ≤ 2`), with the bad-iteration term**: under c.D1pLB.X and f.D1pLB.X on
`X = X₀ = ℝⁿ`, f.B.Fb and `1 ≤ q ≤ p` (the class is non-empty for `q ≤ 2`,
`exists_isTPqpGCARqpUnitRun`, where Algorithm 12.2.3 keeps the radii `1`; for `q > 2` it may be
empty), with the constants of `theorem_14_3_9_arqpc`, there are constants `κ_F`, `κ_D` such
that for all tolerances `ε ∈ (0, 1]^{q+1}` with `ε₀ ≤ β_F` and every run `IsTPqpGCARqpUnitRun`, the
evaluation counts are at most `κ_F (O_F + ∑_j (ε₀ ε_j)^{-1})` and `κ_D (O_F + ∑_j (ε₀ ε_j)^{-1})`
(Phase 2, if entered, terminating), with the unit-radius exponents `π_j = (p+1)/(p-j+1)` of
(14.2.12) in `O_F = tpqpOrderF π q ε`. The extra term (case-(b) iterations ending at a point
passing INNER's test, radii `1`) is within the printed order for `q = p`
(`theorem_14_3_9_arqp_unit`); for `q < p` it is not dominated by `O_F`
(`exists_tpqpOrderF_lt_arqp_unit`). -/
theorem theorem_14_3_9_arqp_unit_corrected (hq : 1 ≤ q) (hqp : q ≤ p)
    {Lc Bc Lf Bf : ℕ → ℝ} (hc : AssumptionCD1pLBX c univ univ p Lc Bc)
    (hf : AssumptionD1pLBX f univ univ p Lf Bf) {βF flow fup : ℝ}
    (hB : Chapter07.AssumptionBFb f c univ βF flow fup) (P : ARqpCParams) (hθς : P.θ < P.ς)
    {θ β β₁ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (x₀ : ℝⁿ) :
    ∃ κF κD : ℝ, ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ βF →
      ∀ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCARqpUnitRun f c p q P θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ →
        let O := tpqpOrderF (Chapter12.arqpPiOf True p) q ε +
          ∑ j ∈ Finset.Icc 1 q, (ε 0 * ε j)⁻¹
        (θ * ε 0 < ‖c (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤ κF * O ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ κD * O) ∧
        (‖c (xP k₁)‖ ≤ θ * ε 0 → ∃ kε, D.IsEnd f c univ q θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤ κF * O ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤ κD * O) := by
  obtain ⟨κF, κD, -, -, hmain⟩ :=
    exists_const_order_arqp_unit hq hqp hc hf hB P hθς hθ0 hθ1 hβ0 (β₁ := β₁) x₀
  refine ⟨κF, κD, fun ε hε hεβ xP δP k₁ D nF₁ nD₁ hR => ?_⟩
  intro O
  have hnn : ∀ i ∈ Finset.Icc 1 q, 0 ≤ (ε 0 * ε i)⁻¹ := fun i hi => by
    have := (hε 0 (by simp)).1
    have := (hε i (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hi).2))).1
    positivity
  have hB0 : 0 ≤ ∑ j ∈ Finset.Icc 1 q, (ε 0 * ε j)⁻¹ := Finset.sum_nonneg hnn
  have hO0 : 0 ≤ tpqpOrderF (Chapter12.arqpPiOf True p) q ε :=
    zero_le_one.trans (one_le_tpqpOrderF (hε 0 (by simp)).1 (hε 0 (by simp)).2)
  exact hmain ε hε hεβ xP δP k₁ D nF₁ nD₁ hR O
    (inv_le_tpqpOrderF.trans (le_add_of_nonneg_right hB0))
    (fun l hl => (term_le_tpqpOrderF hl).trans (le_add_of_nonneg_right hB0))
    fun j hj => (Finset.single_le_sum hnn hj).trans (le_add_of_nonneg_left hO0)

/-- **Theorem 14.3.9** of [cartis2022evaluation] **on `ℝⁿ` for every run with INNER = ARqp with
unit radii, in the printed order, when `q = p ≤ 2`** (unit-radius exponents
`π_j = (p+1)/(p-j+1)`, which for `p = q ≤ 2` are the exponents `j(p+1)/p`, `π_p = p + 1`): under
the assumptions of `theorem_14_3_9_arqp_unit_corrected` with `p = q`, there are constants `κ_F`,
`κ_D` such that for all tolerances `ε ∈ (0, 1]^{q+1}` with `ε₀ ≤ β_F` and every run
`IsTPqpGCARqpUnitRun`, Phase 1 alone (if it ends with `‖c(x₁)‖ > θε₀`), resp. both phases (Phase 2
terminating), use at most `κ_F O_F` evaluations of `(f, c)` and `κ_D O_D` derivative evaluations,
`O_F = tpqpOrderF π q ε`, `O_D = tpqpOrderD π q ε`. -/
theorem theorem_14_3_9_arqp_unit (hq : 1 ≤ q) (hq2 : q ≤ 2) {Lc Bc Lf Bf : ℕ → ℝ}
    (hc : AssumptionCD1pLBX c univ univ q Lc Bc) (hf : AssumptionD1pLBX f univ univ q Lf Bf)
    {βF flow fup : ℝ} (hB : Chapter07.AssumptionBFb f c univ βF flow fup) (P : ARqpCParams)
    (hθς : P.θ < P.ς) {θ β β₁ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (x₀ : ℝⁿ) :
    ∃ κF κD : ℝ, ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ βF →
      ∀ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCARqpUnitRun f c q q P θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ →
        (θ * ε 0 < ‖c (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤
            κF * tpqpOrderF (Chapter12.arqpPiOf True q) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤
            κD * tpqpOrderD (Chapter12.arqpPiOf True q) q ε) ∧
        (‖c (xP k₁)‖ ≤ θ * ε 0 → ∃ kε, D.IsEnd f c univ q θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤
            κF * tpqpOrderF (Chapter12.arqpPiOf True q) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤
            κD * tpqpOrderD (Chapter12.arqpPiOf True q) q ε) := by
  obtain ⟨κF, κD, hκF, hκD, hmain⟩ :=
    exists_const_order_arqp_unit hq le_rfl hc hf hB P hθς hθ0 hθ1 hβ0 (β₁ := β₁) x₀
  refine ⟨2 * κF, 2 * κD, fun ε hε hεβ xP δP k₁ D nF₁ nD₁ hR => ?_⟩
  set π := Chapter12.arqpPiOf True q with hπ
  set OF := tpqpOrderF π q ε with hOF
  have hε₀ := hε 0 (by simp)
  have hq1 : q ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨hq, le_rfl⟩
  have hπq : π q = (q : ℝ) + 1 := by
    rw [hπ, Chapter12.arqpPiOf_of_pos trivial, Nat.sub_self]
    push_cast
    ring
  have hFD : OF ≤ tpqpOrderD π q ε :=
    tpqpOrderF_le_tpqpOrderD hε hq1 (by rw [hπq]; have : (1 : ℝ) ≤ q := by exact_mod_cast hq
                                        linarith)
  have hO0 : 0 ≤ OF := zero_le_one.trans (one_le_tpqpOrderF hε₀.1 hε₀.2)
  have hp_le : ((ε 0) ^ q)⁻¹ ≤ OF := by
    refine le_trans ?_ (term_le_tpqpOrderF hq1)
    have hεq := hε q (Finset.mem_range.2 (Nat.lt_succ_self q))
    have e1 : ε 0 ^ (1 - π q) = ((ε 0) ^ q)⁻¹ := by
      rw [hπq, show 1 - ((q : ℝ) + 1) = -(q : ℝ) by ring, Real.rpow_neg hε₀.1.le,
        Real.rpow_natCast]
    rw [e1]
    have : 1 ≤ ε q ^ (-π q) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hεq.1 hεq.2
        (by rw [hπq]; linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)])
    have : 0 ≤ ((ε 0) ^ q)⁻¹ := by have := hε₀.1; positivity
    nlinarith
  have hmain' := hmain ε hε hεβ xP δP k₁ D nF₁ nD₁ hR (2 * OF)
    (inv_le_tpqpOrderF.trans (by linarith))
    (fun l hl => (term_le_tpqpOrderF hl).trans (by linarith)) fun j hj => by
      have hεj := hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
      have hj1 := (Finset.mem_Icc.1 hj).1
      have hx0 : 0 < ε 0 * ε j := mul_pos hε₀.1 hεj.1
      have hx1 : ε 0 * ε j ≤ 1 := by nlinarith
      have h1 : (ε 0 * ε j)⁻¹ ≤ ((ε 0 * ε j) ^ j)⁻¹ := by
        refine inv_anti₀ (by positivity) ?_
        calc (ε 0 * ε j) ^ j ≤ (ε 0 * ε j) ^ 1 := pow_le_pow_of_le_one hx0.le hx1 hj1
          _ = ε 0 * ε j := pow_one _
      have h2 := inv_pow_le_arqp hε₀.1 hεj.1 (j := j) hq
      rw [← arqpPiOf_true_eq_false hq2 hj] at h2
      have := term_le_tpqpOrderF (π := π) (ε := ε) hj
      linarith
  obtain ⟨hP1, hP2⟩ := hmain'
  have hD : ∀ x : ℝ, x ≤ κD * (2 * OF) → x ≤ 2 * κD * tpqpOrderD π q ε := fun x hx => by
    nlinarith
  refine ⟨fun hc1 => ⟨by linarith [(hP1 hc1).1], hD _ (hP1 hc1).2⟩, fun hc1 => ?_⟩
  obtain ⟨kε, hend, hF, hDD⟩ := hP2 hc1
  exact ⟨kε, hend, by linarith, hD _ hDD⟩

end UnitTheorem

/-! ### For `q < p` the bad-iteration term exceeds the printed order -/

section NotDominated

/-- **The term `(ε₀ ε_1)^{-1}` is not dominated by the printed order** when `1 < π_1 < 2` and
`π_i - 2 < (2 - π_1)/(π_1 - 1)` for every `i ∈ [1 : q]`: for every `C` there are tolerances
`ε ∈ (0, 1]^{q+1}` (`ε₀ = δ`, `ε_1 = δ^a`, `ε_i = 1` for `i ≥ 2`, `δ` small) with
`C max[ε₀^{-1}, max_j ε₀^{1-π_j} ε_j^{-π_j}] < (ε₀ ε_1)^{-1}`. -/
theorem exists_tpqpOrderF_lt {π : ℕ → ℝ} {q : ℕ} (hπ1 : 1 < π 1) (hπ2 : π 1 < 2)
    (hπ : ∀ i ∈ Finset.Icc 1 q, π i - 2 < (2 - π 1) / (π 1 - 1)) (C : ℝ) :
    ∃ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) ∧
      C * tpqpOrderF π q ε < (ε 0 * ε 1)⁻¹ := by
  obtain ⟨b, hb_def⟩ : ∃ b, b = (2 - π 1) / (π 1 - 1) := ⟨_, rfl⟩
  have hb : 0 < b := hb_def ▸ div_pos (by linarith) (by linarith)
  obtain ⟨mm, hmm⟩ : ∃ mm, mm = Chapter12.finMax 0 (fun i => π i - 2) q := ⟨_, rfl⟩
  have hm0 : 0 ≤ mm := hmm ▸ Chapter12.le_finMax_left
  have hmb : mm < b := hmm ▸ Chapter12.finMax_lt hb (hb_def ▸ hπ)
  obtain ⟨a, ha_def⟩ : ∃ a, a = (mm + b) / 2 := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have hab : a < b := by rw [ha_def]; linarith
  have hma : ∀ i ∈ Finset.Icc 1 q, π i - 2 < a := fun i hi =>
    lt_of_le_of_lt (hmm ▸ Chapter12.le_finMax (u := fun i => π i - 2) hi) (by rw [ha_def]; linarith)
  -- the exponents of `δ^{-1}` in the order
  set γ := Chapter12.finMax 1 (fun i => if i = 1 then π 1 - 1 + a * π 1 else π i - 1) q with hγ
  have hγ1 : 1 ≤ γ := Chapter12.le_finMax_left
  have hγa : γ < 1 + a := by
    refine Chapter12.finMax_lt (by linarith) fun i hi => ?_
    split_ifs with h
    · have : a * (π 1 - 1) < 2 - π 1 := by
        rw [hb_def, lt_div_iff₀ (by linarith)] at hab; linarith
      nlinarith
    · linarith [hma i hi]
  set g := 1 + a - γ with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  set δ := min (1 / 2) ((|C| + 1) ^ (-g⁻¹)) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (Real.rpow_pos_of_pos (by positivity) _)
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hδC : |C| + 1 ≤ δ ^ (-g) := by
    have h1 : δ ≤ (|C| + 1) ^ (-g⁻¹) := min_le_right _ _
    have h2 := Real.rpow_le_rpow_of_nonpos hδ0 h1 (by linarith : -g ≤ 0)
    rwa [← Real.rpow_mul (by positivity), show -g⁻¹ * -g = 1 by field_simp, Real.rpow_one] at h2
  set ε : ℕ → ℝ := fun i => if i = 0 then δ else if i = 1 then δ ^ a else 1 with hε
  have hε0 : ε 0 = δ := by simp [hε]
  have hε1 : ε 1 = δ ^ a := by simp [hε]
  have hεi : ∀ i, 2 ≤ i → ε i = 1 := fun i hi => by
    have h0 : i ≠ 0 := by omega
    have h1 : i ≠ 1 := by omega
    simp [hε, h0, h1]
  refine ⟨ε, fun j _ => ?_, ?_⟩
  · simp only [hε]
    split_ifs
    · exact ⟨hδ0, hδ1⟩
    · exact ⟨Real.rpow_pos_of_pos hδ0 _, Real.rpow_le_one hδ0.le hδ1 ha0.le⟩
    · exact ⟨one_pos, le_rfl⟩
  -- every term of the order is at most `δ^{-γ}`
  have hpow : ∀ e : ℝ, e ≤ γ → δ ^ (-e) ≤ δ ^ (-γ) := fun e he =>
    Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
  have hO : tpqpOrderF π q ε ≤ δ ^ (-γ) := by
    refine Chapter12.finMax_le ?_ fun i hi => ?_
    · rw [hε0, ← Real.rpow_neg_one]; exact hpow 1 hγ1
    · have hγi : (if i = 1 then π 1 - 1 + a * π 1 else π i - 1) ≤ γ :=
        Chapter12.le_finMax (u := fun i => if i = 1 then π 1 - 1 + a * π 1 else π i - 1) hi
      by_cases h1 : i = 1
      · subst h1
        simp only [ite_true] at hγi
        rw [hε0, hε1, ← Real.rpow_mul hδ0.le, ← Real.rpow_add hδ0]
        refine le_of_eq_of_le (by ring_nf) (hpow _ hγi)
      · simp only [h1, ite_false] at hγi
        rw [hε0, hεi i (by have := (Finset.mem_Icc.1 hi).1; omega), Real.one_rpow, mul_one]
        exact le_of_eq_of_le (by ring_nf) (hpow _ hγi)
  have hL : (ε 0 * ε 1)⁻¹ = δ ^ (-γ) * δ ^ (-g) := by
    rw [hε0, hε1, ← Real.rpow_add hδ0, ← Real.rpow_one_add' hδ0.le (by linarith),
      ← Real.rpow_neg hδ0.le]
    congr 1
    rw [hg]; ring
  rw [hL]
  have hγpos : 0 < δ ^ (-γ) := Real.rpow_pos_of_pos hδ0 _
  calc C * tpqpOrderF π q ε ≤ |C| * δ ^ (-γ) := by
        have hO0 : 0 ≤ tpqpOrderF π q ε :=
          (inv_pos.2 (by rw [hε0]; exact hδ0)).le.trans inv_le_tpqpOrderF
        calc C * tpqpOrderF π q ε ≤ |C| * tpqpOrderF π q ε :=
              mul_le_mul_of_nonneg_right (le_abs_self C) hO0
          _ ≤ |C| * δ ^ (-γ) := mul_le_mul_of_nonneg_left hO (abs_nonneg C)
    _ < (|C| + 1) * δ ^ (-γ) := by nlinarith
    _ ≤ δ ^ (-g) * δ ^ (-γ) := mul_le_mul_of_nonneg_right hδC hγpos.le
    _ = δ ^ (-γ) * δ ^ (-g) := mul_comm _ _

/-- **For `q < p` the bound of `theorem_14_3_9_arqp_corrected` is not within the printed order**
(ARqp-SC exponents `π_j = j(p+1)/p`): for every `C` there are tolerances with
`C O_F < (ε₀ ε_1)^{-1}`, a lower bound for its extra term `∑_j (ε₀ ε_j)^{-j}`
(`exists_tpqpOrderF_lt` with `π_1 = (p+1)/p`, `(2 - π_1)/(π_1 - 1) = p - 1 > q(p+1)/p - 2`). -/
theorem exists_tpqpOrderF_lt_arqp {p q : ℕ} (hq : 1 ≤ q) (hqp : q < p) (C : ℝ) :
    ∃ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) ∧
      C * tpqpOrderF (Chapter12.arqpPiOf False p) q ε < (ε 0 * ε 1)⁻¹ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (by omega : 2 ≤ p)
  have hqp' : (q : ℝ) + 1 ≤ p := by exact_mod_cast (by omega : q + 1 ≤ p)
  have e1 : Chapter12.arqpPiOf False p 1 = 1 + 1 / p := by
    rw [Chapter12.arqpPiOf_of_neg not_false]; field_simp; push_cast; ring
  have hp1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one hp0]; linarith
  refine exists_tpqpOrderF_lt (by rw [e1]; have : 0 < 1 / (p : ℝ) := by positivity
                                  linarith) (by rw [e1]; linarith) (fun i hi => ?_) C
  have hb : (2 - Chapter12.arqpPiOf False p 1) / (Chapter12.arqpPiOf False p 1 - 1) =
      (p : ℝ) - 1 := by rw [e1]; field_simp; ring
  rw [hb, Chapter12.arqpPiOf_of_neg not_false]
  have hiq : (i : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.1 hi).2
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hp0]
  nlinarith

/-- **For `q < p`, `q ≤ 2`, the bound of `theorem_14_3_9_arqp_unit_corrected` is not within the
printed order** (unit-radius exponents `π_j = (p+1)/(p-j+1)`): for every `C` there are tolerances
with `C O_F < (ε₀ ε_1)^{-1}` (`exists_tpqpOrderF_lt`; `(2 - π_1)/(π_1 - 1) = p - 1`, and
`π_2 - 2 = (3 - p)/(p - 1) < p - 1` for `p ≥ 3`). -/
theorem exists_tpqpOrderF_lt_arqp_unit {p q : ℕ} (hq : 1 ≤ q) (hq2 : q ≤ 2) (hqp : q < p)
    (C : ℝ) :
    ∃ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) ∧
      C * tpqpOrderF (Chapter12.arqpPiOf True p) q ε < (ε 0 * ε 1)⁻¹ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have e1 : Chapter12.arqpPiOf True p 1 = 1 + 1 / p := by
    rw [Chapter12.arqpPiOf_of_pos trivial, Nat.sub_add_cancel (by omega : 1 ≤ p)]
    field_simp; push_cast; ring
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (by omega : 2 ≤ p)
  have hp1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one hp0]; linarith
  refine exists_tpqpOrderF_lt (by rw [e1]; have : 0 < 1 / (p : ℝ) := by positivity
                                  linarith) (by rw [e1]; linarith) (fun i hi => ?_) C
  have hb : (2 - Chapter12.arqpPiOf True p 1) / (Chapter12.arqpPiOf True p 1 - 1) =
      (p : ℝ) - 1 := by rw [e1]; field_simp; ring
  rw [hb]
  obtain ⟨hi1, hiq⟩ := Finset.mem_Icc.1 hi
  have hi2 : i ≤ 2 := hiq.trans hq2
  interval_cases i
  · rw [e1]; have : 1 / (p : ℝ) ≤ 1 / 2 := by gcongr
    linarith
  · have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (by omega : 3 ≤ p)
    rw [Chapter12.arqpPiOf_of_pos trivial]
    have e2 : ((p - 2 + 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [show p - 2 + 1 = p - 1 by omega, Nat.cast_sub (by omega)]; push_cast; ring
    rw [e2, sub_lt_iff_lt_add, div_lt_iff₀ (by linarith)]
    push_cast
    nlinarith

end NotDominated

end CartisGouldToint.Chapter14
