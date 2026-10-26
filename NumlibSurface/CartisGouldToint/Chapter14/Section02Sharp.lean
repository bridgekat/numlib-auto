import NumlibSurface.CartisGouldToint.Chapter14.Section02

/-!
# Cartis–Gould–Toint §14.2: sharpness of the simply constrained complexity orders

Sharpness of the complexity orders of Theorem 14.2.4 of C. Cartis, N. I. M. Gould and
Ph. L. Toint, *Evaluation Complexity of Algorithms for Nonconvex Optimization*
[cartis2022evaluation] ("the orders of complexity mentioned in the last column of the table are
sharp"). The book's argument ("unconstrained problems are a special case of simply constrained
ones") is carried out with the feasible set `X = ℝ` or `X = ℝ¹` (`univ`). For the
dynamic-accuracy methods it needs new data, because the Chapter 12 slow runs are not runs of the
Chapter 13 steps.

## Main results

* `theorem_14_2_4_sharp` — the TRq-SC, ARqp-SC (`q ≤ 2`) and ARqpC-SC (`q = 1`, convex `h`)
  orders, from Theorem 12.2.6, Corollary 12.2.16 and Corollary 14.1.11 with `X = ℝ`;
  `theorem_14_2_4_sharp_arqp` — the ARqp-SC order for `q ≥ 3` (Theorem 12.2.17);
* `theorem_14_2_4_sharp_arqp_otherwise` — the ARqp-SC order `ε^{-q(p+1)/p}` of the lower-bound
  radius mode for every `1 ≤ q ≤ p`, on the closed nonconvex `X = (-∞, R] ∪ [R + 2, ∞) ⊂ ℝ`
  (Theorem 12.2.17 restricted to `X`; the "otherwise" entries for `q = 1`, nonconvex `X`, and
  `q = 2`, `X ≠ ℝⁿ`);
* `theorem_14_2_4_sharp_trqida`, `theorem_14_2_4_sharp_trqeda` — the TRqIDA-SC and TRqEDA-SC
  orders `ε^{-(q+1)}`, from the example of Theorem 12.2.6 lifted to `ℝ¹` (for TRqEDA with `f`
  halved);
* `theorem_14_2_4_sharp_arqpida`, `theorem_14_2_4_sharp_arqpeda` — the ARqpIDA-SC and ARqpEDA-SC
  order `ε^{-(p+1)/(p-q+1)}` of the unit-radii mode for `q ≤ 2` (for `q = 1` and for `q = p = 2`
  also the order of the lower-bound mode), from the example of Theorem 12.2.15 lifted to `ℝ¹`;
* `theorem_14_2_4_sharp_arqpeda_otherwise` — the ARqpEDA-SC order `ε^{-q(p+1)/p}` of the
  lower-bound mode, for every `q ≤ p`, from the example of Theorem 12.2.17 (`r = p`);
* `theorem_14_2_4_sharp_arqpida_otherwise` — the ARqpIDA-SC order `ε^{-q(p+1)/p}` of the
  lower-bound mode for `q = p ≥ 3`, from pure `p`-th order spikes (Theorem 12.2.15 with `q = p`);
* `theorem_14_2_4_sharp_arqpida_otherwise_constrained` — the ARqpIDA-SC order `ε^{-q(p+1)/p}` of
  the lower-bound mode for every `1 ≤ q ≤ p` (in particular the "otherwise" entries for `q = 1`,
  nonconvex `X`, and `q = 2`, `X ≠ ℝⁿ`), on the closed feasible set
  `X = {v | v 1 = 0} ∪ {v | ρ ≤ v 1} ⊂ ℝ²` (`v 1` the second coordinate: a line and a parallel
  half-plane at distance `ρ ∈ (ε, 2ε]`),
  from the example of Theorem 12.2.17 on the line.

All runs are genuine runs of the Chapter 13 run predicates with exact derivatives (and values),
with class constants independent of `ε`. For `q = 2 < p` on `ℝⁿ` the lower-bound-mode order of
the ARqpIDA-SC row is not attained (`theorem_14_2_4_arqpida_le_two` in `Chapter14.Section02`), so
the "otherwise" entry for `q = 2` needs `X ≠ ℝⁿ`.

## Deviations from the book

* TRqIDA-SC and TRqEDA-SC. The slow example of Theorem 12.2.6 becomes a run of these methods
  only for suitable constants:
  - `ϑ = Δ₀ = ε`, forced by `ε_min ≤ ϑ ≤ Δ₀`;
  - initial accuracies passing (13.1.9) along the steps (`h_{0,i} ≤ κ_s ε^{q-i+1}`);
  - for TRqEDA, (13.3.8) at radius `ε`.

  The tests (13.1.14) and (13.3.7) have half the threshold of the TRq test, so TRqEDA is run on
  `f/2` to make it terminate at `k_ε`. TRqIDA has no termination rule and is continued after
  `k_ε` by an arbitrary run from `x_{k_ε}`.
* ARqpIDA-SC and ARqpEDA-SC. The Chapter 12 slow runs are not runs of the Chapter 13
  regularization steps. The Step-1 test (13.1.53) has half the threshold of the ARqp test, and the
  model-decrease condition (13.1.54) can fail at the Step-1 displacements: for the example of
  Theorem 12.2.17 with `p = q = 3`, `ς = 1`, near `k_ε`, `Δm̄ = 5ε⁴/192 < ε⁴/24`. The data are
  therefore adapted as follows.
  - **Unit-radii mode** (`q ≤ 2`, Theorem 12.2.15, `σ₀ = p!/(q-1)!`, unit initial radii). The
    Step-1 radius of order `q` is halved from `1` to a dyadic radius `2^{-m}` at the scale of the
    step, where (13.1.54) holds while it fails at twice that radius. This requires `ε` below some
    `ε₀(p, q)`.
  - **Lower-bound mode of ARqpEDA** (Theorem 12.2.17 with `r = p`, radii `ε`). The weight is
    `σ₀ = (3/(p+2))^p/2` instead of (12.2.85), and the Step-1 displacements achieve exactly the
    fraction `ς` of the measures.
  - **Lower-bound mode of ARqpIDA** (`q = p ≥ 3`, `σ₀ = p`, initial radii `ε`). The Step-2 radii
    are `ε/p`.
  - **Lower-bound mode of ARqpIDA with a feasible set** (`1 ≤ q ≤ p`, `σ₀ = (3/(p+2))^p`, all
    radii `ε`). The criterion `Chapter13.arTest_feasible` asks for approximate optimality for
    *some* radii, and on the line alone the gradient spikes `β_k ≈ ε^q/q!` meet it at radius `1`.
    A second coordinate with `∂f/∂(v 1) = -1` and the half-plane `{ρ ≤ v 1}` make every radius
    `δ ≥ ρ` fail, while radii `δ < ρ` (including the algorithm's radii `ε`) only see the line;
    `ρ^{q-1} = ε^{q-1}(1 + 1/k_ε)` (`ρ = ε(1 + 1/k_ε)` for `q = 1`) makes the first hit exactly
    `k_ε`. After `k_ε` the run makes
    one more step, to a point where the derivatives along the line vanish, and continues with
    accuracy-improving iterations there.
  - **Termination and continuation.** ARqpEDA is run on `f/2` so that it terminates at `k_ε`.
    ARqpIDA is continued after `k_ε` by ARqpIDA iterations from the state at `k_ε`
    (`Chapter13.exists_algorithm_13_1_2_exact`, `Chapter13.exists_arqpDA_steps`).
  - **Accuracies.** The initial accuracies are assumed to pass (13.1.46) along the steps and, for
    ARqpEDA, (13.3.17) at termination.

## Remarks

* The table's sharpness claim for the "otherwise" entry of the ARqpIDA-SC row is met by
  `theorem_14_2_4_sharp_arqpida_otherwise_constrained` (a feasible set `X ≠ ℝⁿ`). The book's proof,
  by reduction to `X = ℝⁿ`, would also need the case `X = ℝⁿ`, `3 ≤ q < p`, which is open here:
  the example of Theorem 12.2.17 meets the criterion at `x₀` (its measures at radius `1` are
  `β_0 ≤ ε/j!`), and pure `q`-th order spikes fail it at every radius but have the order
  `ε^{-(p+1)/(p-q+1)}`. Heuristically, failing the criterion at radius `1` needs a derivative of
  some order `3 ≤ i ≤ q` of size `≳ ε` at every iterate, and if these derivatives are periodic
  along the run, Taylor consistency of the jets needs steps `t ≳ ε^{1/(p-2)} ≫ ε^{q/p}`. The
  book's statement of Theorem 12.2.17, "for some `δ_ε`", has the same caveat.
-/

open Set Metric
open scoped Nat

namespace CartisGouldToint.Chapter14

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness: the orders of the TRq-SC row
(`ε^{-(q+1)}`), of the ARqp-SC row for `q ≤ 2` (`ε^{-(p+1)/(p-q+1)}`) and of the ARqpC-SC row
for `q = 1` and convex `h` (`ε^{-(p+1)/p}`) are attained, by the slow examples of
Theorem 12.2.6, Corollary 12.2.16 and Corollary 14.1.11 run with the (simple) feasible set
`X = ℝ` (`univ`; `X = ℝ¹` and `h = ‖·‖` for ARqpC-SC). The ARqp-SC row for `q ≥ 3` is
`theorem_14_2_4_sharp_arqp`; the TRqIDA-SC and TRqEDA-SC rows are `theorem_14_2_4_sharp_trqida`
and `theorem_14_2_4_sharp_trqeda`, the ARqpIDA-SC and ARqpEDA-SC rows
`theorem_14_2_4_sharp_arqpida`, `theorem_14_2_4_sharp_arqpeda`,
`theorem_14_2_4_sharp_arqpeda_otherwise` and `theorem_14_2_4_sharp_arqpida_otherwise`. -/
theorem theorem_14_2_4_sharp {p q : ℕ} (hq : 1 ≤ q) :
    (∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / q ! → ∀ P : Optimization.TRqParams,
      P.Δ₀ = ε → ∃ f : ℝ → ℝ, (∀ t, flow ≤ f t) ∧ Chapter12.AssumptionD1pL f q (fun _ => L) ∧
        ∃ (x s : ℕ → ℝ) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝ),
          Chapter12.algorithm_12_2_1_feasible f univ P q (fun j => j ! * ε) 1 x s Δ jk d ∧
          Optimization.IsFirstHit (Chapter12.trqStop f P q (fun j => j ! * ε) 1 x Δ d)
            ⌈(ε ^ (q + 1))⁻¹⌉₊ ∧
          (ε ^ (q + 1))⁻¹ + 1 ≤ (Optimization.funEvalCount ⌈(ε ^ (q + 1))⁻¹⌉₊ : ℝ)) ∧
    (q ≤ 2 → q ≤ p → ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ P : Optimization.ARqpParams, P.σ₀ = (p ! : ℝ) / (q - 1)! →
      ∃ f : ℝ → ℝ, (∀ t, flow ≤ f t) ∧ Chapter12.AssumptionD1pL f p (fun _ => L) ∧
        ∃ (x s σ : ℕ → ℝ) (d : ℕ → ℕ → ℝ),
          Chapter12.algorithm_12_2_2_feasible f univ P p q (fun _ => ε) (fun _ => 1) x s σ
            (fun _ _ => 1) (fun _ _ => 1) d (fun _ _ => 0) ∧
          Optimization.IsFirstHit (Chapter12.arqpStop f P p q (fun _ => ε) x s σ (fun _ _ => 1) d)
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊) ∧
    (1 ≤ p → ∀ P : ARqpCParams, ∃ L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ c : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1),
        AssumptionCD1pL c p (fun _ => L) ∧ ‖c 0‖ ≤ L ∧
        AssumptionWBb (fun _ => 0) c (fun v => ‖v‖) univ 0 ∧
        ∃ (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ)
          (d dm : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)),
          algorithm_14_1_1 (fun _ => 0) c (fun v => ‖v‖) univ p 1 P (fun _ => ε) (fun _ => 1)
            x s σ δ δs d dm ∧
          Optimization.IsFirstHit
            (arqpcStop (fun _ => 0) c (fun v => ‖v‖) p 1 P (fun _ => ε) x s σ δ d)
            ⌈ε ^ (-((p + 1 : ℝ) / p))⌉₊ ∧
          ε ^ (-((p + 1 : ℝ) / p)) + 1 ≤
            (Optimization.funEvalCount ⌈ε ^ (-((p + 1 : ℝ) / p))⌉₊ : ℝ)) := by
  refine ⟨?_, fun hq2 hqp => ?_, fun hp P => ?_⟩
  · obtain ⟨flow, L, hL, H⟩ := Chapter12.theorem_12_2_6 hq
    refine ⟨flow, L, hL, fun ε hε hε1 P hP => ?_⟩
    obtain ⟨f, hb, hf, x, s, Δ, jk, d, hrun, -, -, hhit, -, hF, -⟩ := H ε hε hε1 P hP
    exact ⟨f, hb, hf, x, s, Δ, jk, d, Chapter12.algorithm_12_2_1_iff_feasible.1 hrun, hhit, hF⟩
  · obtain ⟨flow, L, hL, H⟩ := Chapter12.corollary_12_2_16 hq hq2 hqp
    refine ⟨flow, L, hL, fun ε hε hε1 P hP => ?_⟩
    obtain ⟨f, hb, hf, x, s, σ, d, hrun, -, hhit, -⟩ := H ε hε hε1 P hP
    exact ⟨f, hb, hf, x, s, σ, d, hrun, hhit⟩
  · obtain ⟨-, -, -, -, L, hL, H⟩ := corollary_14_1_11 hp P
    refine ⟨L, hL, fun ε hε hε1 => ?_⟩
    obtain ⟨c, hc, hc0, -, hw, x, s, σ, δ, δs, d, dm, hrun, -, hhit, -, hF, -⟩ := H ε hε hε1
    exact ⟨c, hc, hc0, hw, x, s, σ, δ, δs, d, dm, hrun, hhit, hF⟩

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the ARqp-SC row for `q ≥ 3`
(the "otherwise" order `ε^{-q(p+1)/p}`): the slow example of Theorem 12.2.17 run with the (simple)
feasible set `X = ℝ` (`univ`). For `3 ≤ q ≤ p` there are `f_low` and `L ≥ 1` such that for every
`ε ∈ (0, ½]` and ARqp constants with `σ₀` the weight (12.2.85) there is `f` with f.bB and f.D1pL
and an ARqp-SC run with radii `ε` satisfying the radius hypothesis of `theorem_14_2_4_arqp`
(`δ_{s_k,j} ≥ κ_δ(σ_k) ε_j`) that first terminates at `k_ε = ⌈ε^{-q(p+1)/p}⌉`, after
`k_ε + 1 ≥ ε^{-q(p+1)/p} + 1` evaluations. -/
theorem theorem_14_2_4_sharp_arqp {p q : ℕ} (hq : 2 < q) (hqp : q ≤ p) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ P : Optimization.ARqpParams,
      P.σ₀ = Chapter12.arqpSigmaSharp p q →
      ∃ f : ℝ → ℝ, (∀ t, flow ≤ f t) ∧ Chapter12.AssumptionD1pL f p (fun _ => L) ∧
        ∃ (x s σ : ℕ → ℝ) (d : ℕ → ℕ → ℝ),
          Chapter12.algorithm_12_2_2_feasible f univ P p q (fun _ => ε) (fun _ => ε) x s σ
            (fun _ _ => ε) (fun _ _ => ε) d (fun _ _ => 0) ∧
          (∀ k, (∀ i ≤ k, ¬ Chapter12.arqpStop f P p q (fun _ => ε) x s σ (fun _ _ => ε) d i) →
            ‖s k‖ < 1 → ∀ j ∈ Finset.Icc 1 q,
              Chapter12.arqpKappaDelta P (Chapter12.finMax 1 (fun _ => L) p) (σ k) * ε ≤ ε) ∧
          Optimization.IsFirstHit (Chapter12.arqpStop f P p q (fun _ => ε) x s σ (fun _ _ => ε) d)
            ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ ∧
          ε ^ (-((q : ℝ) * (p + 1) / p)) + 1 ≤
            (Optimization.funEvalCount ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ : ℝ) := by
  obtain ⟨flow, L, hL, H⟩ := Chapter12.theorem_12_2_17 (r := p) (by omega) hqp le_rfl
  refine ⟨flow, L, hL, fun ε hε hε2 P hP => ?_⟩
  obtain ⟨f, hb, hf, x, s, σ, d, hrun, -, -, hκ, -, hhit, -⟩ := H ε hε hε2 P hP
  refine ⟨f, hb, hf, x, s, σ, d, hrun, fun k _ _ _ _ => hκ k, hhit, ?_⟩
  simp only [Optimization.funEvalCount, Nat.cast_add, Nat.cast_one]
  linarith [Nat.le_ceil (ε ^ (-((q : ℝ) * (p + 1) / p)))]

/-! ### Sharpness of the ARqp-SC row in the lower-bound mode with a constrained feasible set

The slow example of Theorem 12.2.17 never leaves a half-line, so it is also an ARqp-SC run on a
closed nonconvex `X ⊂ ℝ` (`X ≠ ℝ`), which reaches the "otherwise" entries of the table for
`q ≤ 2`. -/

section ARqpOtherwise

open Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An approximate optimality displacement of a Taylor decrement over a set `S'` of displacements
is one over any smaller set `S ⊆ S'` containing it. -/
private theorem isApproxMeasureStep_of_subset {D : FormalMultilinearSeries ℝ E ℝ} {j : ℕ}
    {δ ς : ℝ} {d : E} {S S' : Set E} (hς : 0 ≤ ς)
    (h : IsApproxMeasureStep (D.taylorDecrement j) δ S' ς d) (hSS' : S ⊆ S') (hd : d ∈ S) :
    IsApproxMeasureStep (D.taylorDecrement j) δ S ς d :=
  ⟨⟨h.1.1, hd⟩, (mul_le_mul_of_nonneg_left (decrementMeasure_mono_set ⟨d, h.1.1, hd⟩
    (bddAbove_taylorDecrement D j δ S') hSS') hς).trans h.2⟩

/-- **Restricting an unconstrained ARqp run to a feasible set**: an ARqp run on `univ` is an
ARqp-SC run on `X` if its iterates reached, their Step-1 displacements, and the trial points and
Step-2 displacements of its short steps are feasible. -/
private theorem algorithm_12_2_2_feasible_of_univ {f : E → ℝ} {P : ARqpParams} {p q : ℕ}
    {ε δ₀ : ℕ → ℝ} {x s : ℕ → E} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → E}
    {X : Set E} (h : Chapter12.algorithm_12_2_2 f P p q ε δ₀ x s σ δ δs d dm)
    (hX : ∀ k, (∀ i < k, ¬ Chapter12.arqpStop f P p q ε x s σ δ d i) →
      x k ∈ X ∧ (∀ j ∈ Finset.Icc 1 q, x k + d k j ∈ X) ∧ x k + s k ∈ X ∧
        (‖s k‖ < 1 → ∀ j ∈ Finset.Icc 1 q, x k + s k + dm k j ∈ X)) :
    Chapter12.algorithm_12_2_2_feasible f X P p q ε δ₀ x s σ δ δs d dm := by
  have hς := P.ς_pos.le
  refine ⟨⟨h.toIsARRun.sigma_zero, fun k hk h1 => ?_, h.toIsARRun.accept⟩,
    (hX 0 fun _ h => absurd h (Nat.not_lt_zero _)).1, h.delta_zero, fun k hk j hj => ?_, h.radii⟩
  · have hst := h.toIsARRun.step k hk h1
    obtain ⟨-, -, hs, hdm⟩ := hX k hk
    refine ⟨hs, hst.model_le, fun he => (hst.isMinOn_of_eq he).of_subset (subset_univ _),
      hst.radius_pos, hst.radius_le_one, ?_⟩
    rcases hst.branch with hl | hb
    · exact Or.inl hl
    rcases le_or_gt 1 ‖s k‖ with hl | hl
    · exact Or.inl hl
    · refine Or.inr fun j hj => ⟨?_, (hb j hj).2⟩
      exact isApproxMeasureStep_of_subset hς (hb j hj).1 (fun _ _ => mem_univ _) (hdm hl j hj)
  · exact isApproxMeasureStep_of_subset hς (h.witness k hk j hj) (fun _ _ => mem_univ _)
      ((hX k hk).2.1 j hj)

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the ARqp-SC row in the lower-bound
mode of the radius policy (the "otherwise" order `ε^{-q(p+1)/p}`) for every `1 ≤ q ≤ p`, with a
closed nonconvex feasible set `X = (-∞, R] ∪ [R + 2, ∞) ⊂ ℝ`: the slow example of
Theorem 12.2.17 (`r = p`) restricted to `X`. For `1 ≤ q ≤ p` there are `f_low` and `L ≥ 1` such
that for every `ε ∈ (0, ½]` and ARqp constants with `σ₀` the weight (12.2.85) there are `R` and
`f` with f.bB and f.D1pL and an ARqp-SC run on `X` with radii `ε` satisfying the radius hypothesis
of the lower-bound mode of `theorem_14_2_4_arqp` (`δ_{s_k,j} ≥ κ_δ(σ_k) ε_j`) that first
terminates at `k_ε = ⌈ε^{-q(p+1)/p}⌉`, after `k_ε + 1 ≥ ε^{-q(p+1)/p} + 1` evaluations. The run
of Theorem 12.2.17 stays in `(-∞, R]` together with its displacements, so it is a run on `X`.
This covers the "otherwise" entries of the table for `q = 1` (nonconvex `X`) and `q = 2`
(`X ≠ ℝⁿ`), which the reduction to `X = ℝⁿ` does not reach; for `q > 2` it complements
`theorem_14_2_4_sharp_arqp` (`X = ℝ`). -/
theorem theorem_14_2_4_sharp_arqp_otherwise {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ P : ARqpParams,
      P.σ₀ = Chapter12.arqpSigmaSharp p q →
      ∃ (R : ℝ) (f : ℝ → ℝ), (∀ t, flow ≤ f t) ∧ Chapter12.AssumptionD1pL f p (fun _ => L) ∧
        ∃ (x s σ : ℕ → ℝ) (d : ℕ → ℕ → ℝ),
          Chapter12.algorithm_12_2_2_feasible f ({t | t ≤ R} ∪ {t | R + 2 ≤ t}) P p q
            (fun _ => ε) (fun _ => ε) x s σ (fun _ _ => ε) (fun _ _ => ε) d (fun _ _ => 0) ∧
          (∀ k, (∀ i ≤ k, ¬ Chapter12.arqpStop f P p q (fun _ => ε) x s σ (fun _ _ => ε) d i) →
            ‖s k‖ < 1 → ∀ j ∈ Finset.Icc 1 q,
              Chapter12.arqpKappaDelta P (Chapter12.finMax 1 (fun _ => L) p) (σ k) * ε ≤ ε) ∧
          IsFirstHit (Chapter12.arqpStop f P p q (fun _ => ε) x s σ (fun _ _ => ε) d)
            ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ ∧
          ε ^ (-((q : ℝ) * (p + 1) / p)) + 1 ≤
            (funEvalCount ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ : ℝ) := by
  obtain ⟨flow, L, hL, H⟩ := Chapter12.theorem_12_2_17 (r := p) hq hqp le_rfl
  refine ⟨flow, L, hL, fun ε hε hε2 P hP => ?_⟩
  obtain ⟨f, hb, hf, x, s, σ, d, hrun, -, -, hκ, -, hhit, -⟩ := H ε hε hε2 P hP
  set kε := ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊
  set R : ℝ := ∑ k ∈ Finset.range (kε + 1), (|x k| + |s k|) + 2 with hR
  have hxs : ∀ k ≤ kε, |x k| + |s k| ≤ R - 2 := fun k hk => by
    rw [hR, add_sub_cancel_right]
    exact Finset.single_le_sum (f := fun k => |x k| + |s k|) (fun _ _ => by positivity)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
  have hX : ∀ k, (∀ i < k, ¬ Chapter12.arqpStop f P p q (fun _ => ε) x s σ (fun _ _ => ε) d i) →
      x k ∈ {t | t ≤ R} ∪ {t | R + 2 ≤ t} ∧
      (∀ j ∈ Finset.Icc 1 q, x k + d k j ∈ {t | t ≤ R} ∪ {t | R + 2 ≤ t}) ∧
      x k + s k ∈ {t | t ≤ R} ∪ {t | R + 2 ≤ t} ∧
      (‖s k‖ < 1 → ∀ j ∈ Finset.Icc 1 q,
        x k + s k + (fun _ _ => (0 : ℝ)) k j ∈ {t | t ≤ R} ∪ {t | R + 2 ≤ t}) := by
    intro k hk
    have hkε : k ≤ kε := not_lt.1 fun hlt => hk kε hlt hhit.1
    have h1 := hxs k hkε
    have hxa := le_abs_self (x k)
    have hsa := le_abs_self (s k)
    have hsa' := abs_nonneg (s k)
    refine ⟨Or.inl (by simp only [mem_ofPred_eq]; linarith), fun j hj => Or.inl ?_,
      Or.inl (by simp only [mem_ofPred_eq]; linarith), fun _ j _ => Or.inl (by
        simp only [mem_ofPred_eq, add_zero]; linarith)⟩
    have hd := (hrun.witness k hk j hj).1.1
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at hd
    have := le_abs_self (d k j)
    simp only [mem_ofPred_eq]
    linarith
  refine ⟨R, f, hb, hf, x, s, σ, d, algorithm_12_2_2_feasible_of_univ hrun hX,
    fun k _ _ _ _ => hκ k, hhit, ?_⟩
  simp only [funEvalCount, Nat.cast_add, Nat.cast_one]
  linarith [Nat.le_ceil (ε ^ (-((q : ℝ) * (p + 1) / p)))]

end ARqpOtherwise

/-! ### Sharpness of the dynamic-accuracy trust-region rows

The orders of the TRqIDA-SC and TRqEDA-SC rows are attained with `X = ℝ¹` (`univ`) and exact
derivatives (zero approximation error), by the slow example of Theorem 12.2.6
(`Optimization.exists_slowTRq_interpolant`) lifted to `ℝ¹`. -/

section TRqDASharp

open Chapter13 Optimization
open scoped RealInnerProductSpace

/-- The unit vector of `ℝ¹`. -/
private noncomputable def u₁ : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1

private theorem norm_u₁ : ‖u₁‖ = 1 := by simp [u₁]

private theorem inner_smul_u₁ (r : ℝ) : ⟪u₁, r • u₁⟫ = r := by
  rw [inner_smul_right, real_inner_self_eq_norm_sq, norm_u₁]; ring

private theorem norm_smul_u₁ (r : ℝ) : ‖r • u₁‖ = |r| := by
  rw [norm_smul, norm_u₁, mul_one, Real.norm_eq_abs]

private theorem smul_u₁_succ (k : ℕ) (ε : ℝ) :
    ((k : ℝ) * ε) • u₁ + ε • u₁ = (((k : ℝ) + 1) * ε) • u₁ := by
  rw [← add_smul]; ring_nf

/-- **The slow trust-region example on `ℝ¹`** (Theorem 12.2.6 lifted along `e₁`, scaled by
`λ ∈ (0, 1]`). For `q ≥ 1` there are `f_low` and `L ≥ 1` such that, for every `ε ∈ (0, 1]` and
`λ ∈ (0, 1]`, with `k_ε = ⌈ε^{-(q+1)}⌉`, `c_k = 2 - k/k_ε` and `x_k = k ε e₁`, there is `f`
with `f ≥ f_low` and f.D0qL (all `L_{f,j} = L`) whose Taylor decrements at `x_k` (`k ≤ k_ε`) are
`ΔT_{f,j}(x_k, d) = 0` for `j < q` and `λ ε c_k ⟪e₁, d⟫^q` for `j = q`, and with
`f(x_{k+1}) = f(x_k) - λ ε^{q+1} c_k` (`k < k_ε`). -/
private theorem exists_slowTRq_ridge {q : ℕ} (hq : 1 ≤ q) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, (∀ y, flow ≤ f y) ∧ AssumptionD0qL f q (fun _ => L) ∧
        (∀ k ≤ ⌈(ε ^ (q + 1))⁻¹⌉₊, ∀ j ≤ q, ∀ d,
          (ftaylorSeries ℝ f (((k : ℝ) * ε) • u₁)).taylorDecrement j d =
            (if j = q then lam * ε * (2 - k / ⌈(ε ^ (q + 1))⁻¹⌉₊) else 0) * ⟪u₁, d⟫ ^ q) ∧
        ∀ k < ⌈(ε ^ (q + 1))⁻¹⌉₊, f ((((k : ℝ) + 1) * ε) • u₁) =
          f (((k : ℝ) * ε) • u₁) - lam * ε ^ (q + 1) * (2 - k / ⌈(ε ^ (q + 1))⁻¹⌉₊) := by
  obtain ⟨L, B, hL, hB, hG⟩ := exists_slowTRq_interpolant hq
  refine ⟨-B, max 1 (max L B), le_max_left _ _, fun ε hε hε1 lam hlam hlam1 => ?_⟩
  obtain ⟨G, hGc, hGL, hGB, hGd, hGf⟩ := hG ε (fun k => k * ε) hε hε1 fun k _ => by
    push_cast; ring
  set g : ℝ → ℝ := fun t => lam * G t with hg
  have hgc : ContDiff ℝ q g := contDiff_const.mul hGc
  have hgj : ∀ j t, iteratedDeriv j g t = lam * iteratedDeriv j G t := fun j t =>
    iteratedDeriv_const_mul_field lam G
  obtain ⟨hfc, hfb, hfl⟩ := ridge_const_mul_slow_bounds (G := G) (lam := lam) (e := u₁) hGc hB
    hGL hGB hlam hlam1 norm_u₁.le
  refine ⟨ridge g u₁, hfb, ⟨hfc, fun j hj => ⟨le_max_left _ _, hfl j hj⟩⟩,
    fun k hk j hj d => ?_, fun k hk => ?_⟩
  · have hspike : IsSpikeJetOf q g q ⟪u₁, ((k : ℝ) * ε) • u₁⟫
        (lam * (ε * (2 - k / ⌈(ε ^ (q + 1))⁻¹⌉₊) * q !)) := by
      rw [inner_smul_u₁]
      refine ⟨by rw [hgj, (hGd k hk).2]; ring, fun i hi1 hiq hne => ?_⟩
      rw [hgj, (hGd k hk).1 i hi1 (lt_of_le_of_ne hiq hne), mul_zero]
    by_cases hjq : j = q
    · subst hjq
      rw [taylorDecrement_ridge_spike hgc hq le_rfl hspike, ite_eq_left rfl]
      field_simp
    · rw [ite_eq_right hjq, zero_mul]
      exact taylorDecrement_ridge_of_lt hgc (lt_of_le_of_ne hj hjq) hspike d
  · simp only [ridge_apply, inner_smul_u₁, hg]
    have := hGf k hk
    push_cast at this
    rw [this]; ring

/-- The Taylor measure of a decrement `d ↦ a ⟪e₁, d⟫^q` (`a ≥ 0`) over the ball of radius `δ`. -/
private theorem taylorMeasure_of_dec {D : FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ}
    {j q : ℕ} {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hdec : ∀ d, D.taylorDecrement j d = a * ⟪u₁, d⟫ ^ q) :
    taylorMeasure D j δ univ = a * δ ^ q := by
  rw [taylorMeasure, show D.taylorDecrement j = fun d => a * ⟪u₁, d⟫ ^ q from funext hdec]
  exact decrementMeasure_mul_inner_pow norm_u₁ ha hδ

/-- Step-1 displacements achieving exactly the fraction `ς` of the measure. -/
private theorem exists_slow_witness (D : FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)
    (j : ℕ) {δ ς : ℝ} (hδ : 0 ≤ δ) (hς : ς ∈ Icc (0 : ℝ) 1) :
    ∃ d, IsApproxMeasureStep (D.taylorDecrement j) δ univ ς d ∧
      D.taylorDecrement j d = ς * taylorMeasure D j δ univ :=
  exists_isApproxMeasureStep_eq isClosed_univ (mem_univ 0) (starConvex_univ 0) hδ
    (D.continuous_taylorDecrement j).continuousOn (D.taylorDecrement_zero_right j) hς

section SlowStep

variable {P : TRqIDAParams} {ε lam c : ℝ} {x : ℕ → EuclideanSpace ℝ (Fin 1)} {Δ : ℕ → ℝ}
  {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ}
  {dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)} {jk : ℕ → ℕ} {s : ℕ → EuclideanSpace ℝ (Fin 1)}
  {acc : ℕ → Prop} {ρ : ℕ → ℝ} {k : ℕ}

/-- The Step-1 decreases along the slow example: `ς a_j ε^q` with `a_q = λ ε c` and `a_j = 0`
otherwise. -/
private theorem slow_dec_dd (hε : 0 < ε) (hA : 0 ≤ lam * ε * c)
    (hdec : ∀ j ∈ Finset.Icc 1 P.q, ∀ d,
      (D k).taylorDecrement j d = (if j = P.q then lam * ε * c else 0) * ⟪u₁, d⟫ ^ P.q)
    (hdd : ∀ j ∈ Finset.Icc 1 P.q,
      IsApproxMeasureStep ((D k).taylorDecrement j) ε univ P.ς (dd k j) ∧
        (D k).taylorDecrement j (dd k j) = P.ς * taylorMeasure (D k) j ε univ)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 P.q) :
    (D k).taylorDecrement j (dd k j) = P.ς * ((if j = P.q then lam * ε * c else 0) * ε ^ P.q) := by
  rw [(hdd j hj).2, taylorMeasure_of_dec (by split_ifs <;> [exact hA; exact le_rfl]) hε.le
    (hdec j hj)]

/-- Along the slow example the test (13.1.14) holds at order `q` (`λ c > ½`). -/
private theorem slow_trFail (hε : 0 < ε) (hϑ : P.ϑ = ε) (hlamc : 1 < 2 * (lam * c))
    (hdec : ∀ j ∈ Finset.Icc 1 P.q, ∀ d,
      (D k).taylorDecrement j d = (if j = P.q then lam * ε * c else 0) * ⟪u₁, d⟫ ^ P.q)
    (hdd : ∀ j ∈ Finset.Icc 1 P.q,
      IsApproxMeasureStep ((D k).taylorDecrement j) ε univ P.ς (dd k j) ∧
        (D k).taylorDecrement j (dd k j) = P.ς * taylorMeasure (D k) j ε univ)
    (hΔ : Δ k = ε) : trFail P (fun j => j ! * ε) D Δ dd k P.q := by
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have hA : 0 ≤ lam * ε * c := by nlinarith
  have hς := P.ς_pos
  rw [trFail, trRadius, hΔ, hϑ, min_self, slow_dec_dd hε hA hdec hdd hqm, ite_eq_left rfl]
  have hqf : (0 : ℝ) < P.q ! := by positivity
  have e : P.ς * (P.q ! * ε) * ε ^ P.q / P.q ! / 2 = P.ς * ε ^ P.q * ε / 2 := by
    field_simp
  rw [e]
  have h0 : 0 < P.ς * ε ^ P.q * ε := by positivity
  nlinarith

/-- **One iteration of the slow example is a TRqIDA/TRqEDA step** (`X = univ`, exact Taylor data
`D k`): with `ϑ = Δ_k = Δ_{k+1} = ε`, decrements `a_j ⟪e₁, d⟫^q` (`a_q = λ ε c`, `λ c > ½`),
Step-1 displacements achieving the fraction `ς` of the measures, the step `s_k = ε e₁` along
which the iterate moves, `j_k = q`, accuracies passing (13.1.9) and the ratio `ρ_k = 1`. -/
private theorem slow_trqDAStep (hε : 0 < ε) (hϑ : P.ϑ = ε) (hΔmax : ε ≤ P.Δmax)
    (hlamc : 1 < 2 * (lam * c)) (hA : 0 ≤ lam * ε * c)
    (hdec : ∀ j ∈ Finset.Icc 1 P.q, ∀ d,
      (D k).taylorDecrement j d = (if j = P.q then lam * ε * c else 0) * ⟪u₁, d⟫ ^ P.q)
    (hdd : ∀ j ∈ Finset.Icc 1 P.q,
      IsApproxMeasureStep ((D k).taylorDecrement j) ε univ P.ς (dd k j) ∧
        (D k).taylorDecrement j (dd k j) = P.ς * taylorMeasure (D k) j ε univ)
    (hΔ : Δ k = ε) (hΔ1 : Δ (k + 1) = ε) (hh1 : h (k + 1) = h k)
    (hhk : ∀ i ∈ Finset.Icc 1 P.q, h k i ≤ P.κs * ε ^ (P.q - i + 1)) (hjk : jk k = P.q)
    (hs : s k = ε • u₁) (hacc : ¬ acc k) (hx1 : x (k + 1) = x k + ε • u₁) (hρ : ρ k = 1) :
    TRqDAStep univ P (fun j => j ! * ε) x Δ h D dd jk s acc ρ k := by
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  have hrad : trRadius P Δ k = ε := by simp only [trRadius, hΔ, hϑ, min_self]
  have hfail := slow_trFail hε hϑ hlamc hdec hdd hΔ
  have hnot : ∀ j ∈ Finset.Icc 1 P.q, j ≠ P.q → ¬ trFail P (fun j => j ! * ε) D Δ dd k j := by
    intro j hj hjq hf
    rw [trFail, hrad, slow_dec_dd hε hA hdec hdd hj, ite_eq_right hjq, zero_mul, mul_zero] at hf
    have : 0 < P.ς * (j ! * ε) * ε ^ j / j ! / 2 := by positivity
    linarith
  have hη : P.η₁ ≤ 1 := P.η₁_le_η₂.trans P.η₂_lt_one.le
  refine ⟨fun j hj => ?_, fun hp => absurd hfail (hp _ hqm), fun _ => ?_, fun _ => ?_,
    fun _ => hΔ1 ▸ hΔmax, fun _ => hh1, fun _ hr => absurd hr (by rw [hρ]; exact not_lt.2 hη),
    fun ha => absurd ha hacc, fun ha => absurd ha hacc, fun ha => absurd ha hacc⟩
  · rw [hrad, setOf_add_mem_univ]; exact (hdd j hj).1
  · refine ⟨by rw [hjk]; exact hqm, by rw [hjk]; exact hfail,
      fun j hj hlt => hnot j hj (by rw [hjk] at hlt; exact hlt.ne), mem_univ _,
      by rw [hs, hΔ, norm_smul_u₁, abs_of_pos hε], ?_, iff_of_false hacc ?_⟩
    · rw [hjk, slow_dec_dd hε hA hdec hdd hqm, hs, hdec _ hqm, inner_smul_u₁, ite_eq_left rfl]
      have : 0 ≤ lam * ε * c * ε ^ P.q := by positivity
      nlinarith
    · rintro ⟨i, hi, hlt⟩
      rw [hs, norm_smul_u₁, abs_of_pos hε] at hlt
      linarith [hhk i hi]
  · refine ⟨by rw [hρ, ite_eq_left hη, hs, hx1], ?_⟩
    rw [hρ, hΔ, hΔ1]
    exact ⟨fun _ => ⟨le_rfl, le_mul_of_one_le_left hε.le P.one_le_γ₃⟩,
      fun _ h2 => absurd h2 (not_lt.2 P.η₂_lt_one.le), fun h1 => absurd h1 (not_lt.2 hη)⟩

end SlowStep

/-- The ratio of a slow iteration is `1`: the decrease `λ ε^{q+1} c` of `f` equals the decrease
`λ ε c ε^q` of the Taylor model along `s_k = ε e₁`. -/
private theorem slow_ratio {f : EuclideanSpace ℝ (Fin 1) → ℝ}
    {D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin 1)} {jk : ℕ → ℕ} {k q : ℕ} {ε lam c : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) (hc : 0 < c) (hjk : jk k = q) (hs : s k = ε • u₁)
    (hdec : (D k).taylorDecrement q (ε • u₁) = lam * ε * c * ε ^ q)
    (hf : f (x k + ε • u₁) = f (x k) - lam * ε ^ (q + 1) * c) :
    trqRatio f D x s jk k = 1 := by
  rw [trqRatio_eq, reductionRatio, hjk, hs, hdec, hf]
  have : 0 < lam * ε * c * ε ^ q := by positivity
  field_simp
  ring

/-- The bookkeeping of the slow trust-region example: for `ε ∈ (0, 1/q!]`,
`k_ε = ⌈ε^{-(q+1)}⌉ ≥ max(1, ε^{-(q+1)})`, `c_k = 2 - k/k_ε` is `> 1` before `k_ε`, `≥ 0` up to
`k_ε` and `1` at `k_ε`, and the tolerances `ε_j = j! ε` lie in `(0, 1]` with `ε_min = ε`. -/
private theorem slow_setup {q : ℕ} (hq : 1 ≤ q) {ε : ℝ} (hε : 0 < ε) (hεq : ε ≤ 1 / q !) :
    ε ≤ 1 ∧ 1 ≤ ⌈(ε ^ (q + 1))⁻¹⌉₊ ∧ (ε ^ (q + 1))⁻¹ ≤ ⌈(ε ^ (q + 1))⁻¹⌉₊ ∧
      (∀ k < ⌈(ε ^ (q + 1))⁻¹⌉₊, 1 < 2 - (k : ℝ) / ⌈(ε ^ (q + 1))⁻¹⌉₊) ∧
      (∀ k ≤ ⌈(ε ^ (q + 1))⁻¹⌉₊, 0 ≤ 2 - (k : ℝ) / ⌈(ε ^ (q + 1))⁻¹⌉₊) ∧
      2 - (⌈(ε ^ (q + 1))⁻¹⌉₊ : ℝ) / ⌈(ε ^ (q + 1))⁻¹⌉₊ = 1 ∧
      (∀ j ∈ Finset.Icc 1 q, (j ! : ℝ) * ε ∈ Set.Ioc 0 1) ∧
      epsMin q (fun j : ℕ => (j ! : ℝ) * ε) = ε := by
  have hqf : (0 : ℝ) < q ! := by positivity
  have hκ1 : 1 ≤ ⌈(ε ^ (q + 1))⁻¹⌉₊ :=
    Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hκpos : (0 : ℝ) < ⌈(ε ^ (q + 1))⁻¹⌉₊ := by exact_mod_cast hκ1
  refine ⟨hεq.trans (by
      rw [div_le_one hqf]; exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)),
    hκ1, Nat.le_ceil _, fun k hk => ?_, fun k hk => ?_, by rw [div_self hκpos.ne']; ring,
    fun j hj => ⟨by positivity, ?_⟩, ?_⟩
  · have : (k : ℝ) / ⌈(ε ^ (q + 1))⁻¹⌉₊ < 1 := (div_lt_one hκpos).2 (by exact_mod_cast hk)
    linarith
  · have : (k : ℝ) / ⌈(ε ^ (q + 1))⁻¹⌉₊ ≤ 1 := (div_le_one hκpos).2 (by exact_mod_cast hk)
    linarith
  · have hjq : (j ! : ℝ) ≤ q ! := by exact_mod_cast Nat.factorial_le (Finset.mem_Icc.1 hj).2
    calc (j ! : ℝ) * ε ≤ q ! * (1 / q !) := mul_le_mul hjq hεq hε.le hqf.le
      _ = 1 := by field_simp
  · have h1 := epsMin_le (ε := fun j : ℕ => (j ! : ℝ) * ε) (Finset.mem_Icc.2 ⟨le_rfl, hq⟩)
    refine le_antisymm (by simpa using h1) ((le_epsMin_iff hq).2 fun j _ => ?_)
    have h2 : (1 : ℝ) ≤ j ! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
    exact le_mul_of_one_le_left hε.le h2

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the TRqIDA-SC row: the order
`ε^{-(q+1)}` is attained with the (simple) feasible set `X = ℝ¹` (`univ`) and exact derivatives
(`κ_{∇,i} = 0`, so (13.1.2) asks for zero error). For `q ≥ 1` there are `f_low` and `L ≥ 1` such
that, for every `ε ∈ (0, 1/q!]` (tolerances `ε_j = j! ε`) and all TRqIDA constants with `q`,
`Δ₀ = ϑ = ε` and initial accuracies passing (13.1.9) along steps of length `ε`
(`h_{0,i} ≤ κ_s ε^{q-i+1}`), there is `f` with f.bB and f.D0qL (all `L_{f,j} = L`) and a TRqIDA-SC
run with exact derivatives from `x₀ = 0` whose first `(ε, δ_k)`-approximately optimal iterate is
`x_{k_ε}`, `k_ε = ⌈ε^{-(q+1)}⌉`, after `k_ε + 1 ≥ ε^{-(q+1)} + 1` function evaluations and as
many derivative evaluations. The run follows the slow example of Theorem 12.2.6
(`x_k = k ε e₁`, `Δ_k = ε`, `ρ_k = 1`, no accuracy-improving iteration) up to `k_ε`, and continues
as any run from `x_{k_ε}` (`Chapter13.exists_algorithm_13_1_1_exact`). -/
theorem theorem_14_2_4_sharp_trqida {q : ℕ} (hq : 1 ≤ q) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / q ! → ∀ P : TRqIDAParams, P.q = q →
      P.Δ₀ = ε → P.ϑ = ε → (∀ i ∈ Finset.Icc 1 q, P.h₀ i ≤ P.κs * ε ^ (q - i + 1)) →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, (∀ y, flow ≤ f y) ∧ AssumptionD0qL f q (fun _ => L) ∧
        ∃ (x : ℕ → EuclideanSpace ℝ (Fin 1)) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ)
          (D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)
          (dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)) (jk : ℕ → ℕ)
          (s : ℕ → EuclideanSpace ℝ (Fin 1)) (acc : ℕ → Prop),
          algorithm_13_1_1_feasible f univ (fun _ => 0) P (fun j => j ! * ε) 0 x Δ h D dd jk s
            acc ∧
          (∀ k, D k = ftaylorSeries ℝ f (x k)) ∧
          IsFirstHit (trTest_feasible f univ P (fun j => j ! * ε) x Δ) ⌈(ε ^ (q + 1))⁻¹⌉₊ ∧
          (ε ^ (q + 1))⁻¹ + 1 ≤ (derivEvalCount (fun i => ¬ acc i) ⌈(ε ^ (q + 1))⁻¹⌉₊ : ℝ) ∧
          (ε ^ (q + 1))⁻¹ + 1 ≤ (derivEvalCount
            (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i))
              ⌈(ε ^ (q + 1))⁻¹⌉₊ : ℝ) := by
  obtain ⟨flow, L, hL, H⟩ := exists_slowTRq_ridge hq
  refine ⟨flow, L, hL, fun ε hε hεq P hPq hΔ₀ hϑ hh₀ => ?_⟩
  subst hPq
  obtain ⟨hε1, hκ1, hκge, hc1, hc0, hcκ, hεv, hεmin⟩ := slow_setup P.one_le_q hε hεq
  obtain ⟨f, hb, hf, hdec, hfdec⟩ := H ε hε hε1 1 one_pos le_rfl
  refine ⟨f, hb, hf, ?_⟩
  set κ := ⌈(ε ^ (P.q + 1))⁻¹⌉₊ with hκ
  clear_value κ
  have hϑε : epsMin P.q (fun j : ℕ => (j ! : ℝ) * ε) ≤ P.ϑ := by rw [hεmin, hϑ]
  set xp : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => ((k : ℝ) * ε) • u₁ with hxp
  have hxp1 : ∀ k : ℕ, xp k + ε • u₁ = (((k : ℝ) + 1) * ε) • u₁ := fun k => smul_u₁_succ k ε
  obtain ⟨x', Δ', h', D', dd', jk', s', acc', hr, hD'⟩ :=
    exists_algorithm_13_1_1_exact (f := f) (κg := fun _ => 0) hεv hϑε (fun _ _ => le_rfl) (xp κ)
  have hw : ∀ k j, ∃ e, IsApproxMeasureStep ((ftaylorSeries ℝ f (xp k)).taylorDecrement j) ε univ
      P.ς e ∧ (ftaylorSeries ℝ f (xp k)).taylorDecrement j e =
        P.ς * taylorMeasure (ftaylorSeries ℝ f (xp k)) j ε univ :=
    fun k j => exists_slow_witness _ j hε.le ⟨P.ς_pos.le, P.ς_le_one⟩
  choose ddp hddp using hw
  -- the run: the slow example up to `κ`, then the run `r` from `x_κ`
  obtain ⟨X, hX⟩ : ∃ X : ℕ → EuclideanSpace ℝ (Fin 1),
      ∀ k, X k = if k < κ then xp k else x' (k - κ) := ⟨_, fun _ => rfl⟩
  obtain ⟨Δv, hΔv⟩ : ∃ Δv : ℕ → ℝ, ∀ k, Δv k = if k < κ then ε else Δ' (k - κ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨hv, hhv⟩ : ∃ hv : ℕ → ℕ → ℝ, ∀ k, hv k = if k < κ then P.h₀ else h' (k - κ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨ddv, hddv⟩ : ∃ ddv : ℕ → ℕ → EuclideanSpace ℝ (Fin 1),
      ∀ k, ddv k = if k < κ then ddp k else dd' (k - κ) := ⟨_, fun _ => rfl⟩
  obtain ⟨jkv, hjkv⟩ : ∃ jkv : ℕ → ℕ, ∀ k, jkv k = if k < κ then P.q else jk' (k - κ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨sv, hsv⟩ : ∃ sv : ℕ → EuclideanSpace ℝ (Fin 1),
      ∀ k, sv k = if k < κ then ε • u₁ else s' (k - κ) := ⟨_, fun _ => rfl⟩
  obtain ⟨accv, haccv⟩ : ∃ accv : ℕ → Prop, ∀ k, accv k = if k < κ then False else acc' (k - κ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Dv, hDv⟩ : ∃ Dv : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ,
      ∀ k, Dv k = ftaylorSeries ℝ f (X k) := ⟨_, fun _ => rfl⟩
  have hXle : ∀ k ≤ κ, X k = xp k := fun k hk => by
    rcases hk.lt_or_eq with hk | rfl
    · rw [hX, ite_eq_left hk]
    · rw [hX, ite_eq_right (lt_irrefl _), Nat.sub_self, hr.x_zero]
  have hΔle : ∀ k ≤ κ, Δv k = ε := fun k hk => by
    rcases hk.lt_or_eq with hk | rfl
    · rw [hΔv, ite_eq_left hk]
    · rw [hΔv, ite_eq_right (lt_irrefl _), Nat.sub_self, hr.Δ_zero, hΔ₀]
  have hhle : ∀ k ≤ κ, hv k = P.h₀ := fun k hk => by
    rcases hk.lt_or_eq with hk | rfl
    · rw [hhv, ite_eq_left hk]
    · rw [hhv, ite_eq_right (lt_irrefl _), Nat.sub_self, hr.h_zero]
  have hdecX : ∀ k ≤ κ, ∀ j ∈ Finset.Icc 1 P.q, ∀ d, (Dv k).taylorDecrement j d =
      (if j = P.q then 1 * ε * (2 - k / κ) else 0) * ⟪u₁, d⟫ ^ P.q := fun k hk j hj d => by
    rw [hDv, hXle k hk]; exact hdec k hk j (Finset.mem_Icc.1 hj).2 d
  have hmeas : ∀ k ≤ κ, ∀ j ∈ Finset.Icc 1 P.q, taylorMeasure (Dv k) j ε univ =
      (if j = P.q then 1 * ε * (2 - k / κ) else 0) * ε ^ P.q := fun k hk j hj => by
    refine taylorMeasure_of_dec ?_ hε.le (hdecX k hk j hj)
    split_ifs
    · have := hc0 k hk
      positivity
    · exact le_rfl
  have hρ1 : ∀ k < κ, trqRatio f Dv X sv jkv k = 1 := fun k hk =>
    slow_ratio hε one_pos (zero_lt_one.trans (hc1 k hk)) (by rw [hjkv, ite_eq_left hk])
      (by rw [hsv, ite_eq_left hk])
      (by rw [hdecX k hk.le P.q (Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩), inner_smul_u₁,
        ite_eq_left rfl])
      (by rw [hXle k hk.le, hxp1, hfdec k hk])
  have hstep : ∀ k, TRqDAStep univ P (fun j => j ! * ε) X Δv hv Dv ddv jkv sv accv
      (trqRatio f Dv X sv jkv) k := by
    intro k
    by_cases hk : k < κ
    · refine slow_trqDAStep (lam := 1) (c := 2 - k / κ) hε hϑ (hΔ₀ ▸ P.Δ₀_le_Δmax)
        (by linarith [hc1 k hk]) (by nlinarith [hc1 k hk]) (hdecX k hk.le) (fun j hj => ?_)
        (hΔle k hk.le) (hΔle (k + 1) hk) (by rw [hhle k hk.le, hhle (k + 1) hk])
        (by rw [hhle k hk.le]; exact hh₀) (by rw [hjkv, ite_eq_left hk])
        (by rw [hsv, ite_eq_left hk]) (by rw [haccv, ite_eq_left hk]; exact not_false)
        (by rw [hXle k hk.le, hXle (k + 1) hk, hxp1]; simp only [hxp, Nat.cast_add, Nat.cast_one])
        (hρ1 k hk)
      rw [hddv, ite_eq_left hk, hDv, hXle k hk.le]
      exact hddp k j
    · have hk' : κ ≤ k := not_lt.1 hk
      have hk1 : ¬ k + 1 < κ := by omega
      have hsub : k + 1 - κ = k - κ + 1 := by omega
      refine (hr.step (k - κ)).congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rw [hX, ite_eq_right hk]
      · rw [hX, ite_eq_right hk1, hsub]
      · rw [hΔv, ite_eq_right hk]
      · rw [hΔv, ite_eq_right hk1, hsub]
      · rw [hhv, ite_eq_right hk]
      · rw [hhv, ite_eq_right hk1, hsub]
      · rw [hDv, hD', hX, ite_eq_right hk]
      · rw [hDv, hD', hX, ite_eq_right hk1, hsub]
      · rw [hddv, ite_eq_right hk]
      · rw [hjkv, ite_eq_right hk]
      · rw [hsv, ite_eq_right hk]
      · rw [haccv, ite_eq_right hk]
      · rw [trqRatio_eq, trqRatio_eq, hDv, hD', hX, ite_eq_right hk, hsv, ite_eq_right hk,
          hjkv, ite_eq_right hk]
  have hrun : algorithm_13_1_1_feasible f univ (fun _ => 0) P (fun j => j ! * ε) 0 X Δv hv Dv
      ddv jkv sv accv :=
    ⟨hεv, hϑε, fun _ _ => le_rfl, by rw [hXle 0 (Nat.zero_le _)]; simp [hxp], mem_univ _,
      by rw [hΔle 0 (Nat.zero_le _), hΔ₀], hhle 0 (Nat.zero_le _),
      fun k => by rw [hDv]; exact (jetApprox_self _ _).mono_err fun i _ => by simp, hstep⟩
  have hnacc : ∀ i < κ, ¬ accv i := fun i hi => by rw [haccv, ite_eq_left hi]; exact not_false
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have htest : ∀ k ≤ κ, (trTest_feasible f univ P (fun j => j ! * ε) X Δv k ↔ k = κ) := by
    intro k hk
    have hrad : trRadius P Δv k = ε := by simp only [trRadius, hΔle k hk, hϑ, min_self]
    rw [trTest_feasible, hrad, setOf_add_mem_univ, isEpsDeltaApprox_iff, ← hDv k]
    constructor
    · intro ht
      by_contra hne
      have h1 := ht P.q hqm
      rw [hmeas k hk _ hqm, ite_eq_left rfl] at h1
      have h2 := hc1 k (lt_of_le_of_ne hk hne)
      have e : (P.q ! : ℝ) * ε * ε ^ P.q / P.q ! = ε * ε ^ P.q := by field_simp
      rw [e] at h1
      have : 0 < ε * ε ^ P.q := by positivity
      nlinarith
    · rintro rfl j hj
      rw [hmeas _ le_rfl j hj]
      by_cases hjq : j = P.q
      · subst hjq
        rw [ite_eq_left rfl, hcκ]
        apply le_of_eq
        field_simp
      · rw [ite_eq_right hjq, zero_mul]
        positivity
  refine ⟨X, Δv, hv, Dv, ddv, jkv, sv, accv, hrun, hDv,
    ⟨(htest κ le_rfl).2 rfl, fun i hi => fun ht => hi.ne ((htest i hi.le).1 ht)⟩, ?_, ?_⟩
  · rw [derivEvalCount_of_forall hnacc]; push_cast; linarith
  · rw [derivEvalCount_of_forall fun i hi => Or.inr ⟨hnacc i hi, by
      rw [hρ1 i hi]; exact P.η₁_le_η₂.trans P.η₂_lt_one.le⟩]
    push_cast; linarith

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the TRqEDA-SC row: the order
`ε^{-(q+1)}` is attained with the (simple) feasible set `X = ℝ¹` (`univ`) and exact function and
derivative values. For `q ≥ 1` there are `f_low` and `L ≥ 1` such that, for every
`ε ∈ (0, 1/q!]` (tolerances `ε_j = j! ε`) and all TRqEDA constants with `q`, `Δ₀ = ϑ = ε`,
(13.3.5) `κ_s ≤ min(η₁, 1 - η₂)/4` and initial accuracies passing (13.1.9) along steps of
length `ε` and the termination test (13.3.8) at radius `ε`
(`∑_{i=1}^q h_{0,i} ε^i/i! ≤ ½ ς ε ε^q/q!`), there is `f` with f.bB and f.D0qL (all
`L_{f,j} = L`) and a TRqEDA-SC run with exact derivatives and function values from `x₀ = 0`
that first terminates at `k_ε = ⌈ε^{-(q+1)}⌉`, after `2 k_ε ≥ 2 ε^{-(q+1)}` function evaluations
(each value recomputed) and `k_ε + 1 ≥ ε^{-(q+1)} + 1` derivative evaluations. The run is the
slow example of Theorem 12.2.6 with `f` halved (`x_k = k ε e₁`, `Δ_k = ε`, `ρ_k = 1`, no
accuracy-improving iteration), the halving making the test (13.3.7), whose threshold is half
that of TRq, pass exactly at `k_ε`. -/
theorem theorem_14_2_4_sharp_trqeda {q : ℕ} (hq : 1 ≤ q) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / q ! → ∀ P : TRqIDAParams, P.q = q →
      P.Δ₀ = ε → P.ϑ = ε → P.κs ≤ min P.η₁ (1 - P.η₂) / 4 →
      (∀ i ∈ Finset.Icc 1 q, P.h₀ i ≤ P.κs * ε ^ (q - i + 1)) →
      ∑ i ∈ Finset.Icc 1 q, P.h₀ i * ε ^ i / i ! ≤ P.ς * ε * ε ^ q / q ! / 2 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, (∀ y, flow ≤ f y) ∧ AssumptionD0qL f q (fun _ => L) ∧
        ∃ (x : ℕ → EuclideanSpace ℝ (Fin 1)) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ)
          (D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)
          (dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)) (jk : ℕ → ℕ)
          (s : ℕ → EuclideanSpace ℝ (Fin 1)) (acc : ℕ → Prop) (fx fxs h₀ : ℕ → ℝ)
          (R : ℕ → Prop),
          algorithm_13_3_1_feasible f univ P (fun j => j ! * ε) 0 x Δ h D dd jk s acc fx fxs h₀
            R ∧
          (∀ k, D k = ftaylorSeries ℝ f (x k) ∧ fx k = f (x k) ∧ fxs k = f (x k + s k)) ∧
          IsFirstHit (edaStopTR P (fun j => j ! * ε) D Δ h dd) ⌈(ε ^ (q + 1))⁻¹⌉₊ ∧
          2 * (ε ^ (q + 1))⁻¹ ≤ (edaFunEvalCount acc R ⌈(ε ^ (q + 1))⁻¹⌉₊ : ℝ) ∧
          (ε ^ (q + 1))⁻¹ + 1 ≤ (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
            P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) i))
              ⌈(ε ^ (q + 1))⁻¹⌉₊ : ℝ) := by
  obtain ⟨flow, L, hL, H⟩ := exists_slowTRq_ridge hq
  refine ⟨flow, L, hL, fun ε hε hεq P hPq hΔ₀ hϑ hκs hh₀ hsum => ?_⟩
  subst hPq
  obtain ⟨hε1, hκ1, hκge, hc1, hc0', hcκ, hεv, hεmin⟩ := slow_setup P.one_le_q hε hεq
  obtain ⟨f, hb, hf, hdec, hfdec⟩ := H ε hε hε1 (1 / 2) (by norm_num) (by norm_num)
  refine ⟨f, hb, hf, ?_⟩
  set κ := ⌈(ε ^ (P.q + 1))⁻¹⌉₊ with hκ
  clear_value κ
  have hc0 : ∀ k ≤ κ, 0 ≤ 1 / 2 * ε * (2 - (k : ℝ) / κ) := fun k hk => by
    have := hc0' k hk
    positivity
  set xp : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => ((k : ℝ) * ε) • u₁ with hxp
  have hxp1 : ∀ k : ℕ, xp k + ε • u₁ = (((k : ℝ) + 1) * ε) • u₁ := fun k => smul_u₁_succ k ε
  have hw : ∀ k j, ∃ e, IsApproxMeasureStep ((ftaylorSeries ℝ f (xp k)).taylorDecrement j) ε univ
      P.ς e ∧ (ftaylorSeries ℝ f (xp k)).taylorDecrement j e =
        P.ς * taylorMeasure (ftaylorSeries ℝ f (xp k)) j ε univ :=
    fun k j => exists_slow_witness _ j hε.le ⟨P.ς_pos.le, P.ς_le_one⟩
  choose ddp hddp using hw
  obtain ⟨Dv, hDv⟩ : ∃ Dv : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ,
      ∀ k, Dv k = ftaylorSeries ℝ f (xp k) := ⟨_, fun _ => rfl⟩
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have hdecX : ∀ k ≤ κ, ∀ j ∈ Finset.Icc 1 P.q, ∀ d, (Dv k).taylorDecrement j d =
      (if j = P.q then 1 / 2 * ε * (2 - k / κ) else 0) * ⟪u₁, d⟫ ^ P.q := fun k hk j hj d => by
    rw [hDv]; exact hdec k hk j (Finset.mem_Icc.1 hj).2 d
  have hddX : ∀ k, ∀ j ∈ Finset.Icc 1 P.q,
      IsApproxMeasureStep ((Dv k).taylorDecrement j) ε univ P.ς (ddp k j) ∧
        (Dv k).taylorDecrement j (ddp k j) = P.ς * taylorMeasure (Dv k) j ε univ :=
    fun k j _ => by rw [hDv]; exact hddp k j
  set sv : ℕ → EuclideanSpace ℝ (Fin 1) := fun _ => ε • u₁ with hsv
  set jkv : ℕ → ℕ := fun _ => P.q with hjkv
  set fx : ℕ → ℝ := fun k => f (xp k) with hfx
  set fxs : ℕ → ℝ := fun k => f (xp k + sv k) with hfxs
  have hdecs : ∀ k ≤ κ, (Dv k).taylorDecrement (jkv k) (sv k) =
      1 / 2 * ε * (2 - k / κ) * ε ^ P.q := fun k hk => by
    rw [hdecX k hk _ hqm, inner_smul_u₁, ite_eq_left rfl]
  have hρ1 : ∀ k < κ, edaRatio fx fxs (fun i => (Dv i).taylorDecrement (jkv i) (sv i)) k = 1 :=
    fun k hk => slow_ratio (D := Dv) (x := xp) (f := f) (lam := 1 / 2) (c := 2 - k / κ) hε
      (by norm_num)
      (zero_lt_one.trans (hc1 k hk)) rfl rfl (by rw [hdecX k hk.le _ hqm, inner_smul_u₁,
        ite_eq_left rfl]) (by rw [hxp1, hfdec k hk])
  have hstop : ∀ k ≤ κ, (edaStopTR P (fun j => j ! * ε) Dv (fun _ => ε) (fun _ => P.h₀) ddp k ↔
      k = κ) := by
    intro k hk
    constructor
    · rintro ⟨hp, -⟩
      by_contra hne
      exact hp _ hqm (slow_trFail (lam := 1 / 2) (c := 2 - k / κ) hε hϑ
        (by linarith [hc1 k (lt_of_le_of_ne hk hne)]) (hdecX k hk) (hddX k) rfl)
    · rintro rfl
      refine ⟨fun j hj hfj => ?_, ?_⟩
      · rw [trFail, trRadius, hϑ, min_self, slow_dec_dd hε (hc0 _ le_rfl) (hdecX _ le_rfl)
          (hddX _) hj] at hfj
        by_cases hjq : j = P.q
        · subst hjq
          rw [ite_eq_left rfl, hcκ] at hfj
          have e : P.ς * (P.q ! * ε) * ε ^ P.q / P.q ! / 2 =
              P.ς * (1 / 2 * ε * 1 * ε ^ P.q) := by field_simp
          rw [e] at hfj
          exact lt_irrefl _ hfj
        · rw [ite_eq_right hjq, zero_mul, mul_zero] at hfj
          have : 0 ≤ P.ς * (j ! * ε) * ε ^ j / j ! / 2 := by
            have := P.ς_pos; positivity
          linarith
      · simp only [trRadius, hϑ, min_self, hεmin]
        exact hsum
  have hnstop : ∀ k < κ, ¬ edaStopTR P (fun j => j ! * ε) Dv (fun _ => ε) (fun _ => P.h₀) ddp k :=
    fun k hk hs => hk.ne ((hstop k hk.le).1 hs)
  have hreach : ∀ k, (∀ j ≤ k, ¬ edaStopTR P (fun j => j ! * ε) Dv (fun _ => ε)
      (fun _ => P.h₀) ddp j) → k < κ := fun k hk => by
    by_contra hge
    exact hk κ (not_lt.1 hge) ((hstop κ le_rfl).2 rfl)
  have hrun : algorithm_13_3_1_feasible f univ P (fun j => j ! * ε) 0 xp (fun _ => ε)
      (fun _ => P.h₀) Dv ddp jkv sv (fun _ => False) fx fxs
      (fun k => P.κs * (Dv k).taylorDecrement (jkv k) (sv k)) (fun _ => True) := by
    refine ⟨hκs, hεv, hεmin.trans hϑ.symm |>.le, by simp [hxp], mem_univ _, hΔ₀.symm, rfl,
      fun k _ => ?_, fun k _ j hj => ?_, fun k hk => ?_⟩
    · rw [hDv]
      exact (jetApprox_self _ _).mono_err fun i hi => (P.h₀_pos i hi).le
    · rw [trRadius, hϑ, min_self, setOf_add_mem_univ]
      exact (hddX k j hj).1
    · have hkκ := hreach k hk
      have hpos : 0 < P.κs * (Dv k).taylorDecrement (jkv k) (sv k) := by
        rw [hdecs k hkκ.le]
        have := P.κs_pos
        have := hc1 k hkκ
        have : 0 < 2 - (k : ℝ) / κ := by linarith
        positivity
      refine ⟨slow_trqDAStep (lam := 1 / 2) (c := 2 - k / κ) hε hϑ (hΔ₀ ▸ P.Δ₀_le_Δmax)
        (by linarith [hc1 k hkκ]) (hc0 k hkκ.le) (hdecX k hkκ.le) (hddX k) rfl rfl rfl hh₀ rfl
        rfl not_false (by rw [hxp1]; simp only [hxp, Nat.cast_add, Nat.cast_one]) (hρ1 k hkκ),
        fun _ => ⟨hpos, le_rfl, by simp [hfxs, hpos.le], by simp [hfx, hpos.le],
          fun h => absurd trivial h⟩⟩
  refine ⟨xp, fun _ => ε, fun _ => P.h₀, Dv, ddp, jkv, sv, fun _ => False, fx, fxs,
    fun k => P.κs * (Dv k).taylorDecrement (jkv k) (sv k), fun _ => True, hrun,
    fun k => ⟨hDv k, rfl, rfl⟩, ⟨(hstop κ le_rfl).2 rfl, hnstop⟩, ?_, ?_⟩
  · rw [edaFunEvalCount, card_filter_range_of_forall fun _ _ => not_false,
      card_filter_range_of_forall fun _ _ => ⟨not_false, trivial⟩]
    push_cast; linarith
  · rw [derivEvalCount_of_forall fun i hi => Or.inr ⟨not_false, by
      rw [hρ1 i hi]; exact P.η₁_le_η₂.trans P.η₂_lt_one.le⟩]
    push_cast; linarith

end TRqDASharp

/-! ### Sharpness of the dynamic-accuracy regularization rows

The orders of the ARqpIDA-SC and ARqpEDA-SC rows in the unit-radii mode (`q ≤ 2`) are attained
with `X = ℝ¹` (`univ`) and exact derivatives (and function values), by the slow example of
Theorem 12.2.15 (`Optimization.exists_slowTaylorOrder_interpolant`) lifted to `ℝ¹`; the order of
the ARqpEDA-SC row in the lower-bound mode by the slow example of Theorem 12.2.17
(`Optimization.exists_slowARqpSmooth_interpolant`). -/

section ARqpDASharp

open Chapter13 Optimization
open scoped RealInnerProductSpace

/-- The norm of `ℝ¹` is the absolute value of the coordinate along `e₁`. -/
private theorem norm_eq_abs_inner_u₁ (v : EuclideanSpace ℝ (Fin 1)) : ‖v‖ = |⟪u₁, v⟫| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]
  simp [u₁, EuclideanSpace.inner_single_left]

/-- **The slow regularization example on `ℝ¹`** (the data of Theorem 12.2.15 lifted along
`e₁`, scaled by `λ ∈ (0, 1]`). For `1 ≤ q ≤ p` there are `f_low` and `L ≥ 1` such that, for
every `ε ∈ (0, 1]`, with `k_ε = ⌈ε^{-(p+1)/(p-q+1)}⌉`, `a_k = λ (ε + ε (k_ε - k)/k_ε)` and points
`x_{k+1} = x_k + a_k^{1/(p-q+1)}`, there is a `C^p` function `g` of one variable whose ridge
`f = g(⟪e₁, ·⟫)` satisfies f.bB and f.D0pL (all `L_{f,j} = L`), with spike jets
`g^{(q)}(x_k) = -a_k` (other derivatives of orders `1, …, p` zero) for `k ≤ k_ε` and
`g(x_{k+1}) = g(x_k) - a_k (x_{k+1} - x_k)^q/q!` for `k < k_ε`. -/
private theorem exists_slowARqp_ridge {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) {lam : ℝ}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ xr : ℕ → ℝ,
      (∀ k < ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊, xr (k + 1) = xr k +
        (lam * (ε + ε * ((⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ : ℝ) - k) /
          ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊)) ^ (1 / ((p - q + 1 : ℕ) : ℝ))) →
      ∃ g : ℝ → ℝ, ContDiff ℝ p g ∧ (∀ y, flow ≤ ridge g u₁ y) ∧
        AssumptionD0qL (ridge g u₁) p (fun _ => L) ∧
        (∀ k ≤ ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊, IsSpikeJetOf p g q (xr k)
          (lam * (ε + ε * ((⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ : ℝ) - k) /
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊))) ∧
        ∀ k < ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊, g (xr (k + 1)) = g (xr k) -
          lam * (ε + ε * ((⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ : ℝ) - k) /
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊) * (xr (k + 1) - xr k) ^ q / q ! := by
  obtain ⟨L, B, hL, hB, hG⟩ := exists_slowTaylorOrder_interpolant hq hqp hlam
  refine ⟨-B, max 1 (max L B), le_max_left _ _, fun ε hε hε1 xr hxr => ?_⟩
  obtain ⟨G, hGc, hGL, hGB, hGd, hGf⟩ := hG ε _ xr hε hε1 rfl hxr
  set g : ℝ → ℝ := fun t => lam * G t with hg
  have hgc : ContDiff ℝ p g := contDiff_const.mul hGc
  have hgj : ∀ j t, iteratedDeriv j g t = lam * iteratedDeriv j G t := fun j t =>
    iteratedDeriv_const_mul_field lam G
  obtain ⟨hfc, hfb, hfl⟩ := ridge_const_mul_slow_bounds (G := G) (lam := lam) (e := u₁) hGc hB
    hGL hGB hlam hlam1 norm_u₁.le
  refine ⟨g, hgc, hfb, ⟨hfc, fun j hj => ⟨le_max_left _ _, hfl j hj⟩⟩,
    fun k hk => ⟨?_, fun j hj1 hjp hjq => ?_⟩, fun k hk => ?_⟩
  · rw [hgj, (hGd k hk).1]; ring
  · rw [hgj, (hGd k hk).2 j hj1 hjp hjq, mul_zero]
  · simp only [hg]
    rw [hGf k hk]; ring

section SlowARStep

variable {P : ARqpIDAParams} {ε a r : ℝ} {x : ℕ → EuclideanSpace ℝ (Fin 1)} {σ : ℕ → ℝ}
  {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ}
  {D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ}
  {dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)} {jk : ℕ → ℕ} {s : ℕ → EuclideanSpace ℝ (Fin 1)}
  {acc : ℕ → Prop} {ρ : ℕ → ℝ} {k : ℕ}

/-- The Step-1 measures along the slow regularization example: `0` below `q` and `(a/q!) δ^q`
at order `q`. -/
private theorem slowAR_measure (ha : 0 ≤ a)
    (hdec : ∀ j ≤ P.q, ∀ d, (D k).taylorDecrement j d =
      (if j = P.q then a / P.q ! else 0) * ⟪u₁, d⟫ ^ P.q) {j : ℕ} (hj : j ≤ P.q) {t : ℝ}
    (ht : 0 ≤ t) :
    taylorMeasure (D k) j t univ = (if j = P.q then a / P.q ! else 0) * t ^ P.q :=
  taylorMeasure_of_dec (by split_ifs <;> positivity) ht (hdec j hj)

/-- `½ ς ε t/c < (a/c) t` for `a > ε/2`, `ς ≤ 1`, `t, c > 0`. -/
private theorem slowAR_half_lt {ς ε a t c : ℝ} (hς1 : ς ≤ 1) (hε : 0 < ε) (ha : ε / 2 < a)
    (ht : 0 < t) (hc : 0 < c) : ς * ε * t / c / 2 < a / c * t := by
  rw [show ς * ε * t / c / 2 = ς * ε / 2 * t / c by ring, show a / c * t = a * t / c by ring]
  refine div_lt_div_of_pos_right ?_ hc
  have : ς * ε / 2 ≤ ε / 2 := by nlinarith
  nlinarith

/-- Along the slow regularization example the test (13.1.53) fails at order `q` with the
displacement `r e₁` (`a > ε/2`). -/
private theorem slowAR_not_pass (hε : 0 < ε) (ha : ε / 2 < a) (hr : 0 < r)
    (hδ₁ : δ₁ k P.q = r) (hdd : dd k P.q = r • u₁)
    (hdq : (D k).taylorDecrement P.q (r • u₁) = a / P.q ! * r ^ P.q) :
    ¬ arPass P (fun _ => ε) D δ₁ dd k P.q := by
  rw [arPass, hδ₁, hdd, hdq]
  exact not_le.2 (slowAR_half_lt P.ς_le_one hε ha (by positivity) (by positivity))

/-- **One iteration of the slow regularization example is an ARqpIDA/ARqpEDA step** (`X = univ`,
`q ≤ 2`, tolerances `ε_j = ε`): with unit radii `δ_k = δ_{k+1} = δ_{s_k} = 1`, decrements
`(a/q!) ⟪e₁, d⟫^q` at orders `q` and `p` (none below `q`) with `a > ε/2`, a Step-1 radius
`δ^{(1)}_{k,q} = r` at which (13.1.54) holds while it fails at `2 r ≤ 1` (the halving loop stops at
`r`), the Step-1 displacements `r e₁` (order `q`) and `0` (below), a global minimizer `s_k` of the
model as step with `‖s_k‖ < 1`, accuracies passing (13.1.46), and the ratio `ρ_k = 1`. -/
private theorem slow_arqpDAStep (hq2 : P.q ≤ 2) (hε : 0 < ε) (ha : ε / 2 < a)
    (hr : 0 < r) (h2r : 2 * r ≤ 1) (hrd : ∃ m : ℕ, r = 1 / 2 ^ m)
    (hr54 : σ k / ((P.p + 1)! : ℝ) * r ^ (P.p + 1) ≤ (a - P.ς * ε / 4) / P.q ! * r ^ P.q)
    (hr54' : (a - P.ς * ε / 4) / P.q ! * (2 * r) ^ P.q <
      σ k / ((P.p + 1)! : ℝ) * (2 * r) ^ (P.p + 1))
    (hδ : ∀ j ∈ Finset.Icc 1 P.q, δ k j = 1) (hδ1 : δ (k + 1) = δs k)
    (hδs : ∀ j ∈ Finset.Icc 1 P.q, δs k j = 1) (hδ₁ : δ₁ k = fun j => if j = P.q then r else 1)
    (hdd : dd k = fun j => if j = P.q then r • u₁ else 0) (hjk : jk k = P.q)
    (hdec : ∀ j ≤ P.q, ∀ d, (D k).taylorDecrement j d =
      (if j = P.q then a / P.q ! else 0) * ⟪u₁, d⟫ ^ P.q)
    (hdecp : ∀ d, (D k).taylorDecrement P.p d = a / P.q ! * ⟪u₁, d⟫ ^ P.q)
    (hmin : IsMinOn (regularizedModel (D k) P.p (σ k)) univ (s k))
    (hs1 : ‖s k‖ < 1) (hhk : ∀ i ∈ Finset.Icc 1 P.p, h k i ≤ P.κs * ‖s k‖ ^ (P.p - i + 1))
    (hacc : ¬ acc k) (hx1 : x (k + 1) = x k + s k) (hσ1 : σ (k + 1) = σ k)
    (hσk : P.σmin ≤ σ k) (hh1 : h (k + 1) = h k) (hρ : ρ k = 1) :
    ARqpDAStep univ P (fun _ => ε) x σ δ δ₁ δs h D dd jk s acc ρ k := by
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  have hqf : (0 : ℝ) < P.q ! := by positivity
  have ha0 : 0 < a := by linarith
  have hA : 0 < a / P.q ! := by positivity
  have hσ0 : 0 ≤ σ k := P.σmin_pos.le.trans hσk
  have hη : P.η₁ ≤ 1 := P.η₁_le_η₂.trans P.η₂_lt_one.le
  -- Taylor decrements along `t e₁`
  have hdq : ∀ t : ℝ, (D k).taylorDecrement P.q (t • u₁) = a / P.q ! * t ^ P.q := fun t => by
    rw [hdec _ le_rfl, ite_eq_left rfl, inner_smul_u₁]
  have hdlt : ∀ j < P.q, ∀ d, (D k).taylorDecrement j d = 0 := fun j hj d => by
    rw [hdec j hj.le, ite_eq_right hj.ne, zero_mul]
  have hM : ∀ t : ℝ, 0 ≤ t → arModelDec P D σ k (t • u₁) =
      a / P.q ! * t ^ P.q - σ k / ((P.p + 1)! : ℝ) * t ^ (P.p + 1) := fun t ht => by
    rw [arModelDec_eq, hdecp, inner_smul_u₁, norm_smul_u₁, abs_of_nonneg ht]
  -- the test (13.1.53) fails at order `q` with the displacement `r e₁`
  have hfail : ¬ arPass P (fun _ => ε) D δ₁ dd k P.q :=
    slowAR_not_pass hε ha hr (by rw [hδ₁]; simp) (by rw [hdd]; simp) (hdq r)
  have hpass_lt : ∀ j ∈ Finset.Icc 1 P.q, j < P.q → arPass P (fun _ => ε) D δ₁ dd k j := by
    intro j hj hlt
    rw [arPass, hdd]
    simp only [ite_eq_right hlt.ne, FormalMultilinearSeries.taylorDecrement_zero_right]
    rw [hδ₁]
    simp only [ite_eq_right hlt.ne]
    positivity
  refine ⟨⟨fun j hj => ?_, fun j hj => ?_, fun j hj hlt => ?_, fun j hj => ?_, fun j hj => ?_⟩,
    fun hp => absurd (hp _ hqm) hfail, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => hh1,
    fun _ hr' => absurd hr' (by rw [hρ]; exact not_lt.2 hη), fun ha' => absurd ha' hacc,
    fun ha' => absurd ha' hacc, fun ha' => absurd ha' hacc, fun ha' => absurd ha' hacc⟩
  · rw [hδ₁]; dsimp only; split_ifs <;> positivity
  · rw [hδ₁, hδ j hj]; dsimp only; split_ifs <;> linarith
  · -- the halving loop stopped at `r`
    rw [hδ₁, hδ j hj] at hlt ⊢
    dsimp only at hlt ⊢
    by_cases hjq : j = P.q
    · subst hjq
      rw [ite_eq_left rfl] at hlt ⊢
      refine ⟨h2r, ⟨(2 * r) • u₁, by rw [norm_smul_u₁, abs_of_pos (by positivity)], mem_univ _,
        ?_, ?_⟩, u₁, norm_u₁.le, mem_univ _, ?_⟩
      · rw [hdq]
        exact slowAR_half_lt hς1 hε ha (by positivity) hqf
      · rw [hM _ (by positivity)]
        have : P.ς * ε * (2 * r) ^ P.q / P.q ! / 4 = (P.ς * ε / 4) / P.q ! * (2 * r) ^ P.q := by
          ring
        rw [this]
        have e : (a - P.ς * ε / 4) / P.q ! * (2 * r) ^ P.q =
            a / P.q ! * (2 * r) ^ P.q - (P.ς * ε / 4) / P.q ! * (2 * r) ^ P.q := by ring
        linarith
      · have h1 : u₁ = (1 : ℝ) • u₁ := (one_smul ℝ u₁).symm
        rw [h1, hdq]
        exact slowAR_half_lt hς1 hε ha (by positivity) hqf
    · rw [ite_eq_right hjq] at hlt
      exact absurd hlt (lt_irrefl _)
  · -- the radii are obtained by halving
    rw [hδ₁, hδ j hj]
    dsimp only
    split_ifs
    · exact hrd
    · exact ⟨0, by norm_num⟩
  · -- the Step-1 displacements
    have hj' := (Finset.mem_Icc.1 hj).2
    rw [hδ₁, hdd, setOf_add_mem_univ]
    dsimp only
    by_cases hjq : j = P.q
    · subst hjq
      simp only [ite_true]
      refine ⟨⟨by rw [mem_closedBall_zero_iff, norm_smul_u₁, abs_of_pos hr], mem_univ _⟩, ?_⟩
      change P.ς * taylorMeasure (D k) P.q r univ ≤ _
      rw [slowAR_measure ha0.le hdec le_rfl hr.le, ite_eq_left rfl, hdq]
      have : 0 ≤ a / P.q ! * r ^ P.q := by positivity
      nlinarith
    · simp only [ite_eq_right hjq]
      refine ⟨⟨mem_closedBall_self zero_le_one, mem_univ _⟩, ?_⟩
      change P.ς * taylorMeasure (D k) j 1 univ ≤ _
      rw [slowAR_measure ha0.le hdec hj' zero_le_one, ite_eq_right hjq, zero_mul, mul_zero,
        FormalMultilinearSeries.taylorDecrement_zero_right]
  · -- Step 2
    refine ⟨by rw [hjk]; exact hqm, by rw [hjk]; exact hfail,
      fun j hj hlt => hpass_lt j hj (by rw [hjk] at hlt; exact hlt),
      fun j hj hlt => absurd (Finset.mem_Icc.1 hj).2 (by rw [hjk] at hlt; omega), ?_,
      mem_univ _, ?_, Or.inr fun ℓ hℓ => ?_, iff_of_false hacc ?_⟩
    · rw [hjk, hdd, hδ₁]
      simp only [ite_true]
      rw [hM _ hr.le]
      have : P.ς * ε * r ^ P.q / P.q ! / 4 = (P.ς * ε / 4) / P.q ! * r ^ P.q := by ring
      rw [this]
      have e : (a - P.ς * ε / 4) / P.q ! * r ^ P.q =
          a / P.q ! * r ^ P.q - (P.ς * ε / 4) / P.q ! * r ^ P.q := by ring
      linarith
    · simp only [arModelDec]
      have := isMinOn_iff.1 hmin (dd k (jk k)) (mem_univ _)
      linarith
    · have hℓ2 : ℓ ∈ Finset.Icc 1 2 :=
        Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hℓ).1, (Finset.mem_Icc.1 hℓ).2.trans hq2⟩
      have hℓp : ℓ ≤ P.p := (Finset.mem_Icc.1 hℓ).2.trans P.q_le_p
      have hφ := taylorMeasure_eq_zero_of_isLocalMin
        ((contDiff_regularizedModel (D := D k) (p := P.p) (σ := σ k)).contDiffAt.of_le
          (by exact_mod_cast hℓp)) (hmin.isLocalMin Filter.univ_mem) hℓ2 zero_le_one
      rw [hδs ℓ hℓ, setOf_add_mem_univ]
      refine ⟨⟨zero_lt_one, le_rfl⟩, 0, ⟨⟨mem_closedBall_self zero_le_one, mem_univ _⟩, ?_⟩, ?_⟩
      · change P.ς * taylorMeasure _ ℓ 1 univ ≤ _
        rw [hφ, mul_zero, FormalMultilinearSeries.taylorDecrement_zero_right]
      · rw [FormalMultilinearSeries.taylorDecrement_zero_right]
        have := P.θ_pos
        positivity
    · rintro ⟨-, i, hi, hlt⟩
      linarith [hhk i hi]
  · rw [hρ, hx1, hσ1]
    exact arAcceptance_of_one_le P.toARParams le_rfl _ _ hσk hσ0
  · rw [hδ1, hρ, ite_eq_left ⟨hη, hs1⟩]

/-- A radius `r ∈ (0, ½]` lies between consecutive dyadic radii reached by halving from `1`:
`2^{-m} ≤ r < 2 · 2^{-m}` for some `m ≥ 1`. -/
private theorem exists_dyadic_mem {r : ℝ} (hr : 0 < r) (hr1 : 2 * r ≤ 1) :
    ∃ m : ℕ, 1 ≤ m ∧ 1 / 2 ^ m ≤ r ∧ r < 2 * (1 / 2 ^ m) := by
  classical
  have hex : ∃ m : ℕ, 1 / (2 : ℝ) ^ m ≤ r := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨n, by rw [one_div_pow] at hn; exact hn.le⟩
  set m := Nat.find hex with hmdef
  have hm : 1 / (2 : ℝ) ^ m ≤ r := Nat.find_spec hex
  have hm1 : 1 ≤ m := by
    by_contra h0
    have : m = 0 := by omega
    rw [this, pow_zero, div_one] at hm
    linarith
  refine ⟨m, hm1, hm, ?_⟩
  have hlt : ¬ 1 / (2 : ℝ) ^ (m - 1) ≤ r := Nat.find_min hex (show m - 1 < m by omega)
  rw [not_le] at hlt
  have e : (1 : ℝ) / 2 ^ (m - 1) = 2 * (1 / 2 ^ m) := by
    obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, pow_succ]; field_simp
  rwa [e] at hlt

/-- **The slow regularization run up to `k_ε`** (the example of Theorem 12.2.15 on `ℝ¹`, `f`
scaled by `λ ∈ [½, 1]`, as a run of the ARqpIDA/ARqpEDA steps with unit radii, `q ≤ 2`). There
are `f_low`, `L ≥ 1` and `ε₀ ∈ (0, ¼]` such that for every `ε ∈ (0, ε₀]` and constants with
`σ₀ = p!/(q-1)!`, with `k_ε = ⌈ε^{-(p+1)/(p-q+1)}⌉`, some `f` with f.bB and f.D0pL, iterates
`x_k` from `0`, radii `δ^{(1)}_k`, displacements `d_k`, steps `s_k` and levels `a_k` satisfy:
`a_k > λ ε` for `k < k_ε` and `a_{k_ε} = λ ε`; the measures at `x_k` (`k ≤ k_ε`) are `0` below
order `q` and `(a_k/q!) δ^q` at order `q`; the steps are short and their Taylor decrease is the
decrease of `f`; (13.1.53) fails at order `q` before `k_ε`; Step 1 at `k_ε` keeps the unit radii
with displacements achieving exactly the fraction `ς` of the measures; and for accuracies `h_k = h₀`
passing (13.1.46) along the steps (`h_{0,i} ≤ κ_s (ε/2)^{p-i+1}`), no accuracy-improving iteration
and ratios `ρ_k = 1` before `k_ε`, every iteration `k < k_ε` is an `ARqpDAStep` with `σ_k = σ₀`,
unit radii `δ_k = δ_{s_k} = 1`, `j_k = q` and exact Taylor data. -/
private theorem exists_slowARqp_run {p q : ℕ} (hq : 1 ≤ q) (hq2 : q ≤ 2) (hqp : q ≤ p)
    {lam : ℝ} (hlam : 1 / 2 ≤ lam) (hlam1 : lam ≤ 1) :
    ∃ flow L ε₀ : ℝ, 1 ≤ L ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 4 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ P : ARqpIDAParams, P.p = p → P.q = q → P.σ₀ = (p ! : ℝ) / (q - 1)! →
      (∀ j ∈ Finset.Icc 1 q, P.δ₀ j = 1) →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, (∀ y, flow ≤ f y) ∧ AssumptionD0pL f p (fun _ => L) ∧
        ∃ (X : ℕ → EuclideanSpace ℝ (Fin 1)) (δ₁ : ℕ → ℕ → ℝ)
          (dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)) (s : ℕ → EuclideanSpace ℝ (Fin 1))
          (a : ℕ → ℝ), X 0 = 0 ∧
          (∀ k < ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊, lam * ε < a k) ∧
          a ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ = lam * ε ∧
          (∀ k ≤ ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊, ∀ j ∈ Finset.Icc 1 P.q,
            ∀ t : ℝ, 0 ≤ t → taylorMeasure (ftaylorSeries ℝ f (X k)) j t univ =
              (if j = P.q then a k / P.q ! else 0) * t ^ P.q) ∧
          (∀ k < ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊, X (k + 1) = X k + s k ∧
            ‖s k‖ < 1 ∧
            f (X k) - f (X k + s k) = (ftaylorSeries ℝ f (X k)).taylorDecrement P.p (s k) ∧
            0 < (ftaylorSeries ℝ f (X k)).taylorDecrement P.p (s k)) ∧
          (∀ k < ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊,
            ¬ arPass P (fun _ => ε) (fun i => ftaylorSeries ℝ f (X i)) δ₁ dd k P.q) ∧
          δ₁ ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ = (fun _ => 1) ∧
          (∀ j ∈ Finset.Icc 1 P.q,
            (ftaylorSeries ℝ f (X ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊)).taylorDecrement
              j (dd ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ j) =
            P.ς * (if j = P.q then a ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ / P.q !
              else 0)) ∧
          ARqpStep1 univ P (fun _ => ε) X (fun _ => P.σ₀) (fun _ => P.δ₀) δ₁
            (fun i => ftaylorSeries ℝ f (X i)) dd
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ ∧
          ∀ (h : ℕ → ℕ → ℝ) (acc : ℕ → Prop) (ρ : ℕ → ℝ),
            (∀ k ≤ ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊, h k = P.h₀) →
            (∀ i ∈ Finset.Icc 1 P.p, P.h₀ i ≤ P.κs * (ε / 2) ^ (P.p - i + 1)) →
            (∀ k < ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊, ¬ acc k) →
            (∀ k < ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊, ρ k = 1) →
            ∀ k < ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊,
            ARqpDAStep univ P (fun _ => ε) X (fun _ => P.σ₀) (fun _ => P.δ₀) δ₁ (fun _ => P.δ₀) h
              (fun i => ftaylorSeries ℝ f (X i)) dd (fun _ => P.q) s acc ρ k := by
  obtain ⟨flow, L, hL, H⟩ := exists_slowARqp_ridge hq hqp (by linarith : (0 : ℝ) < lam) hlam1
  have hR0 : p - q + 1 ≠ 0 := by omega
  have hRpos : (0 : ℝ) < ((p - q + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hR0
  have hK : (0 : ℝ) < (p ! : ℝ) / (q - 1)! * q ! / (p + 1)! := by positivity
  refine ⟨flow, L, min (1 / 4) ((p ! : ℝ) / (q - 1)! * q ! / (p + 1)! / 2 ^ (p - q + 1 + 1)),
    hL, by positivity, min_le_left _ _, fun ε hε hεε P hPp hPq hσ hδ₀ => ?_⟩
  subst hPp hPq
  have hε4 : ε ≤ 1 / 4 := hεε.trans (min_le_left _ _)
  have hεK : ε ≤ (P.p ! : ℝ) / (P.q - 1)! * P.q ! / (P.p + 1)! / 2 ^ (P.p - P.q + 1 + 1) :=
    hεε.trans (min_le_right _ _)
  obtain ⟨hκ1, -⟩ := one_le_ceil_rpow_neg_and_mul_le hε (by linarith)
    (le_of_lt (by positivity : (0 : ℝ) < (P.p + 1 : ℝ) / ((P.p - P.q + 1 : ℕ) : ℝ)))
  set κ := ⌈ε ^ (-((P.p + 1 : ℝ) / ((P.p - P.q + 1 : ℕ) : ℝ)))⌉₊ with hκ
  have hκpos : (0 : ℝ) < κ := by exact_mod_cast hκ1
  set R : ℕ := P.p - P.q + 1 with hR
  set K : ℝ := (P.p ! : ℝ) / (P.q - 1)! * P.q ! / (P.p + 1)! with hKdef
  -- the levels `a_k`, the step lengths `t_k` and the points
  set a : ℕ → ℝ := fun k => lam * (ε + ε * ((κ : ℝ) - k) / κ) with ha
  set t : ℕ → ℝ := fun k => a k ^ (1 / (R : ℝ)) with ht
  set xr : ℕ → ℝ := fun k => ∑ i ∈ Finset.range k, t i with hxr
  have hxr1 : ∀ k, xr (k + 1) = xr k + t k := fun k => Finset.sum_range_succ _ _
  obtain ⟨g, hgc, hb, hf, hspike, hval⟩ := H ε hε (by linarith) xr fun k _ => hxr1 k
  have ha_ge : ∀ k ≤ κ, lam * ε ≤ a k := fun k hk => by
    have : (0 : ℝ) ≤ ε * ((κ : ℝ) - k) / κ := by
      have : (k : ℝ) ≤ κ := by exact_mod_cast hk
      have : 0 ≤ (κ : ℝ) - k := by linarith
      positivity
    simp only [ha]; nlinarith
  have ha_gt : ∀ k < κ, lam * ε < a k := fun k hk => by
    have : (0 : ℝ) < ε * ((κ : ℝ) - k) / κ := by
      have : (k : ℝ) < κ := by exact_mod_cast hk
      have : 0 < (κ : ℝ) - k := by linarith
      positivity
    simp only [ha]; nlinarith
  have ha_le : ∀ k ≤ κ, a k ≤ 2 * ε := fun k hk => by
    have : ε * ((κ : ℝ) - k) / κ ≤ ε := by
      rw [div_le_iff₀ hκpos]
      have : (0 : ℝ) ≤ k := k.cast_nonneg
      nlinarith
    simp only [ha]
    have h0 : 0 ≤ ε * ((κ : ℝ) - k) / κ := by
      have : (k : ℝ) ≤ κ := by exact_mod_cast hk
      have : 0 ≤ (κ : ℝ) - k := by linarith
      positivity
    nlinarith
  have ha_eq : a κ = lam * ε := by simp only [ha]; rw [sub_self, mul_zero, zero_div, add_zero]
  have ha_pos : ∀ k ≤ κ, 0 < a k := fun k hk => by
    have := ha_ge k hk; nlinarith
  -- the step lengths
  have ht_ge : ∀ k ≤ κ, ε / 2 ≤ t k := fun k hk => by
    have h1 : a k ≤ a k ^ (1 / (R : ℝ)) := by
      conv_lhs => rw [← Real.rpow_one (a k)]
      exact Real.rpow_le_rpow_of_exponent_ge (ha_pos k hk) (by linarith [ha_le k hk])
        (by rw [div_le_one hRpos]; exact_mod_cast Nat.one_le_iff_ne_zero.2 hR0)
    simp only [ht]; nlinarith [ha_ge k hk]
  have ht_lt : ∀ k ≤ κ, t k < 1 := fun k hk =>
    Real.rpow_lt_one (ha_pos k hk).le (by linarith [ha_le k hk]) (by positivity)
  have ht_pos : ∀ k ≤ κ, 0 < t k := fun k hk => by linarith [ht_ge k hk]
  -- the function and its Taylor data
  set f : EuclideanSpace ℝ (Fin 1) → ℝ := ridge g u₁ with hfdef
  set X : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => xr k • u₁ with hX
  set s : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => t k • u₁ with hs
  have hXs : ∀ k, X (k + 1) = X k + s k := fun k => by
    simp only [hX, hs, hxr1, add_smul]
  have hspX : ∀ k ≤ κ, IsSpikeJetOf P.p g P.q ⟪u₁, X k⟫ (a k) := fun k hk => by
    rw [inner_smul_u₁]; exact hspike k hk
  have hspXq : ∀ k ≤ κ, IsSpikeJetOf P.q g P.q ⟪u₁, X k⟫ (a k) := fun k hk =>
    ⟨(hspX k hk).1, fun j h1 hj hne => (hspX k hk).2 j h1 (hj.trans P.q_le_p) hne⟩
  have hgp : ContDiff ℝ P.p g := hgc
  have hgq : ContDiff ℝ P.q g := hgp.of_le (by exact_mod_cast P.q_le_p)
  have hdec : ∀ k ≤ κ, ∀ j ≤ P.q, ∀ d, (ftaylorSeries ℝ f (X k)).taylorDecrement j d =
      (if j = P.q then a k / P.q ! else 0) * ⟪u₁, d⟫ ^ P.q := fun k hk j hj d => by
    rcases hj.lt_or_eq with hjq | rfl
    · rw [ite_eq_right hjq.ne, zero_mul]
      exact taylorDecrement_ridge_of_lt hgq hjq (hspXq k hk) d
    · rw [ite_eq_left rfl, taylorDecrement_ridge_spike hgq P.one_le_q le_rfl (hspXq k hk)]
      ring
  have hdecp : ∀ k ≤ κ, ∀ d, (ftaylorSeries ℝ f (X k)).taylorDecrement P.p d =
      a k / P.q ! * ⟪u₁, d⟫ ^ P.q := fun k hk d => by
    rw [taylorDecrement_ridge_spike hgp P.one_le_q P.q_le_p (hspX k hk)]
    ring
  have hmeas : ∀ k ≤ κ, ∀ j ∈ Finset.Icc 1 P.q, ∀ t' : ℝ, 0 ≤ t' →
      taylorMeasure (ftaylorSeries ℝ f (X k)) j t' univ =
        (if j = P.q then a k / P.q ! else 0) * t' ^ P.q := fun k hk j hj t' ht' =>
    slowAR_measure (D := fun i => ftaylorSeries ℝ f (X i)) (ha_pos k hk).le (hdec k hk)
      (Finset.mem_Icc.1 hj).2 ht'
  have hσ0 : 0 < P.σ₀ := P.σ₀_pos
  -- the model minimizers
  have hlam1' : P.σ₀ * (P.q - 1)! / P.p ! = 1 := by rw [hσ]; field_simp
  have hmin : ∀ k ≤ κ, IsMinOn (regularizedModel (ftaylorSeries ℝ f (X k)) P.p P.σ₀) univ (s k) :=
    fun k hk => by
      obtain ⟨hm, -, -⟩ := isMinOn_neg_monomial_add_regularization P.one_le_q P.q_le_p hσ0
        (ha_pos k hk)
      rw [hlam1', div_one] at hm
      intro y _
      simp only [mem_ofPred_eq]
      rw [regularizedModel_ridge_spike norm_eq_abs_inner_u₁ hgp P.one_le_q P.q_le_p (hspX k hk),
        ridge_apply, ridge_apply, show s k = t k • u₁ from rfl, inner_smul_u₁ (t k)]
      exact (add_le_add_iff_left _).2 (isMinOn_iff.1 hm _ (mem_univ _))
  have hnorm_s : ∀ k, ‖s k‖ = |t k| := fun k => norm_smul_u₁ _
  have hdecs : ∀ k ≤ κ, (ftaylorSeries ℝ f (X k)).taylorDecrement P.p (s k) =
      a k / P.q ! * t k ^ P.q := fun k hk => by rw [hdecp k hk, hs, inner_smul_u₁]
  have hfval : ∀ k < κ, f (X k) - f (X k + s k) =
      (ftaylorSeries ℝ f (X k)).taylorDecrement P.p (s k) := fun k hk => by
    rw [hdecs k hk.le, ← hXs, hfdef, ridge_apply, ridge_apply, hX, inner_smul_u₁, inner_smul_u₁,
      hval k hk, hxr1]
    ring
  -- the Step-1 radii `r_k` at which the halving loop stops
  set M : ℕ → ℝ := fun k => (a k - P.ς * ε / 4) / K with hM
  set r : ℕ → ℝ := fun k => M k ^ ((R : ℝ)⁻¹) with hr
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  have hM_pos : ∀ k < κ, 0 < M k := fun k hk => by
    have := ha_gt k hk
    have : P.ς * ε / 4 < a k := by nlinarith
    simp only [hM]; exact div_pos (by linarith) hK
  have hrR : ∀ k < κ, r k ^ R = M k := fun k hk => Real.rpow_inv_natCast_pow (hM_pos k hk).le hR0
  have hr_pos : ∀ k < κ, 0 < r k := fun k hk => Real.rpow_pos_of_pos (hM_pos k hk) _
  have hpow : ∀ y : ℝ, y ^ (P.p + 1) = y ^ P.q * y ^ R := fun y => by
    rw [← pow_add]; congr 1; omega
  have hKσ : K = P.σ₀ * P.q ! / (P.p + 1)! := by rw [hKdef, hσ]
  have h2r : ∀ k < κ, 2 * r k ≤ 1 := fun k hk => by
    have hle : (2 * r k) ^ R ≤ 1 := by
      rw [mul_pow, hrR k hk, hM]
      simp only
      have h1 : a k - P.ς * ε / 4 ≤ 2 * ε := by nlinarith [ha_le k hk.le]
      have h2 : 2 * ε ≤ 2 * (K / 2 ^ (R + 1)) := by linarith
      have h3 : (a k - P.ς * ε / 4) / K ≤ 2 * (K / 2 ^ (R + 1)) / K :=
        div_le_div_of_nonneg_right (h1.trans h2) hK.le
      have h4 : 2 * (K / 2 ^ (R + 1)) / K = 1 / 2 ^ R := by
        rw [pow_succ]; field_simp
      rw [h4] at h3
      calc (2 : ℝ) ^ R * ((a k - P.ς * ε / 4) / K) ≤ 2 ^ R * (1 / 2 ^ R) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = 1 := by field_simp
    exact (pow_le_one_iff_of_nonneg (by linarith [hr_pos k hk]) hR0).1 hle
  -- the dyadic radii `rd_k ∈ (r_k/2, r_k]` reached by halving from `1`
  have heq : ∀ k < κ, P.σ₀ / ((P.p + 1)! : ℝ) * r k ^ R = (a k - P.ς * ε / 4) / P.q ! :=
    fun k hk => by rw [hrR k hk, hM]; simp only; rw [hKσ]; field_simp
  choose! md hmd using fun k (hk : k < κ) => exists_dyadic_mem (hr_pos k hk) (h2r k hk)
  set rd : ℕ → ℝ := fun k => 1 / 2 ^ md k with hrd
  have hrd_pos : ∀ k, 0 < rd k := fun k => by positivity
  have h2rd : ∀ k < κ, 2 * rd k ≤ 1 := fun k hk => by
    have h1 := (hmd k hk).1
    simp only [hrd]
    rw [mul_one_div, div_le_one (by positivity)]
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ md k := pow_le_pow_right₀ one_le_two h1
  have hrd54 : ∀ k < κ, P.σ₀ / ((P.p + 1)! : ℝ) * rd k ^ (P.p + 1) ≤
      (a k - P.ς * ε / 4) / P.q ! * rd k ^ P.q := fun k hk => by
    rw [hpow, ← heq k hk]
    have h1 : rd k ^ R ≤ r k ^ R := pow_le_pow_left₀ (hrd_pos k).le (hmd k hk).2.1 R
    have h2 : 0 ≤ P.σ₀ / ((P.p + 1)! : ℝ) * rd k ^ P.q := by have := (hrd_pos k).le; positivity
    calc P.σ₀ / ((P.p + 1)! : ℝ) * (rd k ^ P.q * rd k ^ R)
        = P.σ₀ / ((P.p + 1)! : ℝ) * rd k ^ P.q * rd k ^ R := by ring
      _ ≤ P.σ₀ / ((P.p + 1)! : ℝ) * rd k ^ P.q * r k ^ R := mul_le_mul_of_nonneg_left h1 h2
      _ = P.σ₀ / ((P.p + 1)! : ℝ) * r k ^ R * rd k ^ P.q := by ring
  have hrd54' : ∀ k < κ, (a k - P.ς * ε / 4) / P.q ! * (2 * rd k) ^ P.q <
      P.σ₀ / ((P.p + 1)! : ℝ) * (2 * rd k) ^ (P.p + 1) := fun k hk => by
    rw [hpow, ← heq k hk]
    have h1 : r k ^ R < (2 * rd k) ^ R :=
      pow_lt_pow_left₀ (hmd k hk).2.2 (hr_pos k hk).le hR0
    have h2 : 0 < P.σ₀ / ((P.p + 1)! : ℝ) * (2 * rd k) ^ P.q := by
      have := hrd_pos k; positivity
    calc P.σ₀ / ((P.p + 1)! : ℝ) * r k ^ R * (2 * rd k) ^ P.q
        = P.σ₀ / ((P.p + 1)! : ℝ) * (2 * rd k) ^ P.q * r k ^ R := by ring
      _ < P.σ₀ / ((P.p + 1)! : ℝ) * (2 * rd k) ^ P.q * (2 * rd k) ^ R :=
          mul_lt_mul_of_pos_left h1 h2
      _ = P.σ₀ / ((P.p + 1)! : ℝ) * ((2 * rd k) ^ P.q * (2 * rd k) ^ R) := by ring
  -- the displacements at `k_ε`
  choose w hw using fun k => exists_slow_witness (ftaylorSeries ℝ f (X k)) P.q zero_le_one
    ⟨P.ς_pos.le, P.ς_le_one⟩
  obtain ⟨δ₁, hδ₁⟩ : ∃ δ₁ : ℕ → ℕ → ℝ, ∀ k, δ₁ k =
      if k < κ then (fun j => if j = P.q then rd k else 1) else fun _ => 1 := ⟨_, fun _ => rfl⟩
  obtain ⟨dd, hdd⟩ : ∃ dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1), ∀ k, dd k =
      if k < κ then (fun j => if j = P.q then rd k • u₁ else 0)
      else fun j => if j = P.q then w k else 0 := ⟨_, fun _ => rfl⟩
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have hεa : ∀ k < κ, ε / 2 < a k := fun k hk => by
    have h1 := ha_gt k hk
    have h2 : ε / 2 ≤ lam * ε := by nlinarith
    linarith
  have hdecq : ∀ k ≤ κ, ∀ y : ℝ, (ftaylorSeries ℝ f (X k)).taylorDecrement P.q (y • u₁) =
      a k / P.q ! * y ^ P.q := fun k hk y => by
    rw [hdec k hk _ le_rfl, ite_eq_left rfl, inner_smul_u₁]
  have hδ₁κ : δ₁ κ = fun _ => 1 := by rw [hδ₁, ite_eq_right (lt_irrefl κ)]
  have hddκ : dd κ = fun j => if j = P.q then w κ else 0 := by
    rw [hdd, ite_eq_right (lt_irrefl κ)]
  refine ⟨f, hb, hf, X, δ₁, dd, s, a, by simp [hX, hxr], ha_gt, ha_eq, hmeas,
    fun k hk => ⟨hXs k, by rw [hnorm_s, abs_of_pos (ht_pos k hk.le)]; exact ht_lt k hk.le,
      hfval k hk, by rw [hdecs k hk.le]; have := ha_pos k hk.le; have := ht_pos k hk.le
                     positivity⟩,
    fun k hk => slowAR_not_pass (D := fun i => ftaylorSeries ℝ f (X i)) hε
      (hεa k hk) (hrd_pos k) (by rw [hδ₁, ite_eq_left hk]; simp)
      (by rw [hdd, ite_eq_left hk]; simp) (hdecq k hk.le _),
    hδ₁κ, fun j hj => ?_, ?_, fun h acc ρ hh hh₀ hacc hρ k hk => ?_⟩
  · rw [hddκ]
    dsimp only
    split_ifs with hjq
    · subst hjq
      rw [(hw κ).2, hmeas κ le_rfl _ hqm 1 zero_le_one, ite_eq_left rfl, one_pow, mul_one]
    · rw [FormalMultilinearSeries.taylorDecrement_zero_right, mul_zero]
  · refine ⟨fun j _ => by rw [hδ₁κ]; exact one_pos, fun j hj => by rw [hδ₁κ, hδ₀ j hj],
      fun j hj hlt => by rw [hδ₁κ, hδ₀ j hj] at hlt; exact absurd hlt (lt_irrefl _),
      fun j hj => ⟨0, by rw [hδ₁κ, hδ₀ j hj]; norm_num⟩, fun j hj => ?_⟩
    rw [hδ₁κ, hddκ, setOf_add_mem_univ]
    dsimp only
    split_ifs with hjq
    · subst hjq; exact (hw κ).1
    · refine ⟨⟨mem_closedBall_self zero_le_one, mem_univ _⟩, ?_⟩
      change P.ς * taylorMeasure _ j 1 univ ≤ _
      rw [hmeas κ le_rfl j hj 1 zero_le_one, ite_eq_right hjq, zero_mul, mul_zero,
        FormalMultilinearSeries.taylorDecrement_zero_right]
  · have hk1 : k + 1 ≤ κ := hk
    refine slow_arqpDAStep (x := X) (σ := fun _ => P.σ₀) (δ := fun _ => P.δ₀) (δ₁ := δ₁)
      (δs := fun _ => P.δ₀) (h := h) (dd := dd) (jk := fun _ => P.q) (s := s) (acc := acc)
      (ρ := ρ) (k := k) (D := fun i => ftaylorSeries ℝ f (X i)) (r := rd k) (a := a k) hq2 hε
      (hεa k hk) (hrd_pos k) (h2rd k hk) ⟨md k, rfl⟩ (hrd54 k hk) (hrd54' k hk) hδ₀ rfl hδ₀
      (by rw [hδ₁, ite_eq_left hk]) (by rw [hdd, ite_eq_left hk]) rfl (hdec k hk.le)
      (hdecp k hk.le) (hmin k hk.le)
      (by rw [hnorm_s, abs_of_pos (ht_pos k hk.le)]; exact ht_lt k hk.le) (fun i hi => ?_)
      (hacc k hk) (hXs k) rfl P.σmin_le_σ₀ (by rw [hh k hk.le, hh (k + 1) hk1]) (hρ k hk)
    rw [hh k hk.le, hnorm_s, abs_of_pos (ht_pos k hk.le)]
    refine (hh₀ i hi).trans (mul_le_mul_of_nonneg_left ?_ P.κs_pos.le)
    exact pow_le_pow_left₀ (by positivity) (ht_ge k hk.le) _

/-- **One iteration of the slow regularization example with small radii** (`X = univ`, any
`q ≤ p`, tolerances `ε_j = ε`): with Step-1 radii `δ_k = δ^{(1)}_k = r` at every order (no
halving) at which (13.1.54) holds, decrements `(a/q!) ⟪e₁, d⟫^q` at orders `q` and `p` (none
below `q`) with `a > ε/2`, the Step-1 displacements `r e₁` (order `q`) and `0` (below), a global
minimizer `s_k` of the model as step, short, whose model decrements of orders `1, …, q` are
nonpositive on the ball of radius `r'` (the Step-2 radii `δ_{s_k} = r' = δ_{k+1}`), accuracies
passing (13.1.46), and the ratio `ρ_k = 1`. -/
private theorem slowTop_arqpDAStep {r' : ℝ} (hε : 0 < ε) (ha : ε / 2 < a) (hr : 0 < r)
    (hr' : 0 < r') (hr'1 : r' ≤ 1)
    (hr54 : σ k / ((P.p + 1)! : ℝ) * r ^ (P.p + 1) ≤ (a - P.ς * ε / 4) / P.q ! * r ^ P.q)
    (hδ : ∀ j ∈ Finset.Icc 1 P.q, δ k j = r) (hδ1 : δ (k + 1) = δs k) (hδ₁ : δ₁ k = δ k)
    (hδs : ∀ j ∈ Finset.Icc 1 P.q, δs k j = r')
    (hdd : dd k = fun j => if j = P.q then r • u₁ else 0) (hjk : jk k = P.q)
    (hdec : ∀ j ≤ P.q, ∀ d, (D k).taylorDecrement j d =
      (if j = P.q then a / P.q ! else 0) * ⟪u₁, d⟫ ^ P.q)
    (hdecp : ∀ d, (D k).taylorDecrement P.p d = a / P.q ! * ⟪u₁, d⟫ ^ P.q)
    (hmin : IsMinOn (regularizedModel (D k) P.p (σ k)) univ (s k))
    (hmodel : ∀ ℓ ∈ Finset.Icc 1 P.q, ∀ d, ‖d‖ ≤ r' →
      (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ d ≤ 0)
    (hs1 : ‖s k‖ < 1) (hhk : ∀ i ∈ Finset.Icc 1 P.p, h k i ≤ P.κs * ‖s k‖ ^ (P.p - i + 1))
    (hacc : ¬ acc k) (hx1 : x (k + 1) = x k + s k) (hσ1 : σ (k + 1) = σ k)
    (hσk : P.σmin ≤ σ k) (hh1 : h (k + 1) = h k) (hρ : ρ k = 1) :
    ARqpDAStep univ P (fun _ => ε) x σ δ δ₁ δs h D dd jk s acc ρ k := by
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  have hqf : (0 : ℝ) < P.q ! := by positivity
  have ha0 : 0 < a := by linarith
  have hσ0 : 0 ≤ σ k := P.σmin_pos.le.trans hσk
  have hη : P.η₁ ≤ 1 := P.η₁_le_η₂.trans P.η₂_lt_one.le
  have hdq : ∀ t : ℝ, (D k).taylorDecrement P.q (t • u₁) = a / P.q ! * t ^ P.q := fun t => by
    rw [hdec _ le_rfl, ite_eq_left rfl, inner_smul_u₁]
  have hM : ∀ t : ℝ, 0 ≤ t → arModelDec P D σ k (t • u₁) =
      a / P.q ! * t ^ P.q - σ k / ((P.p + 1)! : ℝ) * t ^ (P.p + 1) := fun t ht => by
    rw [arModelDec_eq, hdecp, inner_smul_u₁, norm_smul_u₁, abs_of_nonneg ht]
  have hfail : ¬ arPass P (fun _ => ε) D δ₁ dd k P.q :=
    slowAR_not_pass hε ha hr (by rw [hδ₁, hδ _ hqm]) (by rw [hdd]; simp) (hdq r)
  have hpass_lt : ∀ j ∈ Finset.Icc 1 P.q, j < P.q → arPass P (fun _ => ε) D δ₁ dd k j := by
    intro j hj hlt
    rw [arPass, hdd]
    simp only [ite_eq_right hlt.ne, FormalMultilinearSeries.taylorDecrement_zero_right]
    rw [hδ₁, hδ j hj]
    positivity
  refine ⟨⟨fun j hj => by rw [hδ₁, hδ j hj]; exact hr, fun j _ => by rw [hδ₁],
    fun j _ hlt => by rw [hδ₁] at hlt; exact absurd hlt (lt_irrefl _),
    fun j _ => ⟨0, by rw [hδ₁]; norm_num⟩, fun j hj => ?_⟩,
    fun hp => absurd (hp _ hqm) hfail, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => hh1,
    fun _ hr'' => absurd hr'' (by rw [hρ]; exact not_lt.2 hη), fun ha' => absurd ha' hacc,
    fun ha' => absurd ha' hacc, fun ha' => absurd ha' hacc, fun ha' => absurd ha' hacc⟩
  · -- the Step-1 displacements
    have hj' := (Finset.mem_Icc.1 hj).2
    rw [hδ₁, hδ j hj, hdd, setOf_add_mem_univ]
    dsimp only
    by_cases hjq : j = P.q
    · subst hjq
      simp only [ite_true]
      refine ⟨⟨by rw [mem_closedBall_zero_iff, norm_smul_u₁, abs_of_pos hr], mem_univ _⟩, ?_⟩
      change P.ς * taylorMeasure (D k) P.q r univ ≤ _
      rw [slowAR_measure ha0.le hdec le_rfl hr.le, ite_eq_left rfl, hdq]
      have : 0 ≤ a / P.q ! * r ^ P.q := by positivity
      nlinarith
    · simp only [ite_eq_right hjq]
      refine ⟨⟨mem_closedBall_self hr.le, mem_univ _⟩, ?_⟩
      change P.ς * taylorMeasure (D k) j r univ ≤ _
      rw [slowAR_measure ha0.le hdec hj' hr.le, ite_eq_right hjq, zero_mul, mul_zero,
        FormalMultilinearSeries.taylorDecrement_zero_right]
  · -- Step 2
    refine ⟨by rw [hjk]; exact hqm, by rw [hjk]; exact hfail,
      fun j hj hlt => hpass_lt j hj (by rw [hjk] at hlt; exact hlt),
      fun j hj hlt => absurd (Finset.mem_Icc.1 hj).2 (by rw [hjk] at hlt; omega), ?_,
      mem_univ _, ?_, Or.inr fun ℓ hℓ => ?_, iff_of_false hacc ?_⟩
    · rw [hjk, hdd, hδ₁, hδ _ hqm]
      simp only [ite_true]
      rw [hM _ hr.le]
      have : P.ς * ε * r ^ P.q / P.q ! / 4 = (P.ς * ε / 4) / P.q ! * r ^ P.q := by ring
      rw [this]
      have e : (a - P.ς * ε / 4) / P.q ! * r ^ P.q =
          a / P.q ! * r ^ P.q - (P.ς * ε / 4) / P.q ! * r ^ P.q := by ring
      linarith
    · simp only [arModelDec]
      have := isMinOn_iff.1 hmin (dd k (jk k)) (mem_univ _)
      linarith
    · have hℓ' : ∀ d ∈ closedBall (0 : EuclideanSpace ℝ (Fin 1)) r' ∩ univ,
          (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ d ≤ 0 :=
        fun d hd => hmodel ℓ hℓ d (mem_closedBall_zero_iff.1 hd.1)
      rw [hδs ℓ hℓ, setOf_add_mem_univ]
      refine ⟨⟨hr', hr'1⟩, 0, ⟨⟨mem_closedBall_self hr'.le, mem_univ _⟩, ?_⟩, ?_⟩
      · rw [FormalMultilinearSeries.taylorDecrement_zero_right]
        exact mul_nonpos_of_nonneg_of_nonpos hς.le
          (decrementMeasure_le ⟨0, mem_closedBall_self hr'.le, mem_univ _⟩ hℓ')
      · rw [FormalMultilinearSeries.taylorDecrement_zero_right]
        have := P.θ_pos
        positivity
    · rintro ⟨-, i, hi, hlt⟩
      linarith [hhk i hi]
  · rw [hρ, hx1, hσ1]
    exact arAcceptance_of_one_le P.toARParams le_rfl _ _ hσk hσ0
  · rw [hδ1, hρ, ite_eq_left ⟨hη, hs1⟩]

end SlowARStep

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the ARqpIDA-SC row for `q ∈ {1, 2}`:
the order `ε^{-(p+1)/(p-q+1)}` of the unit-radii mode is attained with the (simple) feasible set
`X = ℝ¹` (`univ`) and exact derivatives (`κ_{∇,i} = 0`). For `1 ≤ q ≤ min(2, p)` there are
`f_low`, `L ≥ 1` and `ε₀ > 0` such that, for every `ε ∈ (0, ε₀]` (all `ε_j = ε`) and all ARqpIDA
constants with orders `p, q`, `σ₀ = p!/(q-1)!`, unit initial radii and initial accuracies
`0 < h_{0,i} ≤ κ_s (ε/2)^{p-i+1}` (so that (13.1.46) passes along the steps), there is `f` with
f.bB and f.D0pL (all `L_{f,j} = L`) and an ARqpIDA-SC run with exact derivatives from `x₀ = 0`
satisfying the radii control in both modes (`Chapter13.RadiiControlOf u` for every `u` and every
`L̄ ≥ 1`: unit radii after every short trial step), whose first iterate that is
`(ε, δ)`-approximately optimal for some radii `δ ∈ (0, 1]^q` (`Chapter13.arTest_feasible`) is
`x_{k_ε}`, `k_ε = ⌈ε^{-(p+1)/(p-q+1)}⌉`, after `k_ε + 1 ≥ ε^{-(p+1)/(p-q+1)} + 1` function and
derivative evaluations. The run follows the slow example of Theorem 12.2.15 (spike jets
`f^{(q)}(x_k) = -(ε + ω_k)`, steps the global model minimizers, `σ_k = σ₀`, `ρ_k = 1`, no
accuracy-improving iteration) up to `k_ε`, the Step-1 radius of order `q` being halved to the
scale of the step (where (13.1.54) holds), and continues as any run from `x_{k_ε}`
(`Chapter13.exists_algorithm_13_1_2_exact`). For `q = 1` and for `q = p = 2` the order is also
the order `ε^{-q(p+1)/p}` of the lower-bound mode. -/
theorem theorem_14_2_4_sharp_arqpida {p q : ℕ} (hq : 1 ≤ q) (hq2 : q ≤ 2) (hqp : q ≤ p) :
    ∃ flow L ε₀ : ℝ, 1 ≤ L ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ P : ARqpIDAParams,
      P.p = p → P.q = q → P.σ₀ = (p ! : ℝ) / (q - 1)! → (∀ j ∈ Finset.Icc 1 q, P.δ₀ j = 1) →
      (∀ i ∈ Finset.Icc 1 p, 0 < P.h₀ i ∧ P.h₀ i ≤ P.κs * (ε / 2) ^ (p - i + 1)) →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, (∀ y, flow ≤ f y) ∧ AssumptionD0pL f p (fun _ => L) ∧
        ∃ (x : ℕ → EuclideanSpace ℝ (Fin 1)) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ)
          (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)
          (dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)) (jk : ℕ → ℕ)
          (s : ℕ → EuclideanSpace ℝ (Fin 1)) (acc : ℕ → Prop),
          algorithm_13_1_2_feasible f univ (fun _ => 0) P (fun _ => ε) 0 x σ δ δ₁ δs h D dd jk s
            acc ∧
          (∀ k, D k = ftaylorSeries ℝ f (x k)) ∧
          (∀ (u : Prop) (Lb : ℝ), 1 ≤ Lb → ∀ k, RadiiControlOf u P (fun _ => ε) Lb σ δs s acc k) ∧
          IsFirstHit (arTest_feasible f univ P (fun _ => ε) x)
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ ∧
          ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ))) + 1 ≤ (derivEvalCount (fun i => ¬ acc i)
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ : ℝ) ∧
          ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ))) + 1 ≤ (derivEvalCount
            (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i))
              ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ : ℝ) := by
  obtain ⟨flow, L, ε₀, hL, hε₀, hε₀4, H⟩ := exists_slowARqp_run hq hq2 hqp (lam := 1)
    (by norm_num) le_rfl
  refine ⟨flow, L, ε₀, hL, hε₀, fun ε hε hεε P hPp hPq hσ hδ₀ hh₀ => ?_⟩
  obtain ⟨f, hb, hf, X, δ₁p, ddp, sp, a, hX0, ha_gt, ha_eq, hmeas, hsp, hnp, -, -, -, hrun⟩ :=
    H ε hε hεε P hPp hPq hσ hδ₀
  subst hPp hPq
  refine ⟨f, hb, hf, ?_⟩
  set κ := ⌈ε ^ (-((P.p + 1 : ℝ) / ((P.p - P.q + 1 : ℕ) : ℝ)))⌉₊ with hκ
  have hκge : ε ^ (-((P.p + 1 : ℝ) / ((P.p - P.q + 1 : ℕ) : ℝ))) ≤ κ := Nat.le_ceil _
  clear_value κ
  have hκ1 : 1 ≤ κ := by
    have : 0 < ε ^ (-((P.p + 1 : ℝ) / ((P.p - P.q + 1 : ℕ) : ℝ))) := Real.rpow_pos_of_pos hε _
    exact_mod_cast (show (0 : ℝ) < κ by linarith)
  have hε1 : ε ≤ 1 := by linarith
  have hεv : ∀ j ∈ Finset.Icc 1 P.q, (fun _ : ℕ => ε) j ∈ Set.Ioc 0 1 := fun _ _ => ⟨hε, hε1⟩
  have hεδ : ∀ j ∈ Finset.Icc 1 P.q, (fun _ : ℕ => ε) j ≤ P.δ₀ j := fun j hj => by
    rw [hδ₀ j hj]; exact hε1
  obtain ⟨x', σ', δ', δ₁', δs', h', D', dd', jk', s', acc', hr, hD', hrc'⟩ :=
    exists_algorithm_13_1_2_exact (f := f) (κg := fun _ => 0) (L := fun _ => L) hf hεv hεδ
      (fun _ _ => le_rfl) (fun i hi => (hh₀ i hi).1) (X κ)
  -- the run: the slow example up to `κ`, then the run from `x_κ`
  obtain ⟨Xv, hXv⟩ : ∃ Xv : ℕ → EuclideanSpace ℝ (Fin 1),
      ∀ k, Xv k = if k < κ then X k else x' (k - κ) := ⟨_, fun _ => rfl⟩
  obtain ⟨σv, hσv⟩ : ∃ σv : ℕ → ℝ, ∀ k, σv k = if k < κ then P.σ₀ else σ' (k - κ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨δv, hδv⟩ : ∃ δv : ℕ → ℕ → ℝ, ∀ k, δv k = if k < κ then P.δ₀ else δ' (k - κ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨δ₁v, hδ₁v⟩ : ∃ δ₁v : ℕ → ℕ → ℝ, ∀ k, δ₁v k = if k < κ then δ₁p k else δ₁' (k - κ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨δsv, hδsv⟩ : ∃ δsv : ℕ → ℕ → ℝ,
      ∀ k, δsv k = if k < κ then P.δ₀ else δs' (k - κ) := ⟨_, fun _ => rfl⟩
  obtain ⟨hv, hhv⟩ : ∃ hv : ℕ → ℕ → ℝ, ∀ k, hv k = if k < κ then P.h₀ else h' (k - κ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨ddv, hddv⟩ : ∃ ddv : ℕ → ℕ → EuclideanSpace ℝ (Fin 1),
      ∀ k, ddv k = if k < κ then ddp k else dd' (k - κ) := ⟨_, fun _ => rfl⟩
  obtain ⟨jkv, hjkv⟩ : ∃ jkv : ℕ → ℕ, ∀ k, jkv k = if k < κ then P.q else jk' (k - κ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨sv, hsv⟩ : ∃ sv : ℕ → EuclideanSpace ℝ (Fin 1),
      ∀ k, sv k = if k < κ then sp k else s' (k - κ) := ⟨_, fun _ => rfl⟩
  obtain ⟨accv, haccv⟩ : ∃ accv : ℕ → Prop, ∀ k, accv k = if k < κ then False else acc' (k - κ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Dv, hDv⟩ : ∃ Dv : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ,
      ∀ k, Dv k = ftaylorSeries ℝ f (Xv k) := ⟨_, fun _ => rfl⟩
  have hXle : ∀ k ≤ κ, Xv k = X k := fun k hk => by
    rcases hk.lt_or_eq with hk | rfl
    · rw [hXv, ite_eq_left hk]
    · rw [hXv, ite_eq_right (lt_irrefl _), Nat.sub_self, hr.x_zero]
  have hσle : ∀ k ≤ κ, σv k = P.σ₀ := fun k hk => by
    rcases hk.lt_or_eq with hk | rfl
    · rw [hσv, ite_eq_left hk]
    · rw [hσv, ite_eq_right (lt_irrefl _), Nat.sub_self, hr.σ_zero]
  have hδle : ∀ k ≤ κ, δv k = P.δ₀ := fun k hk => by
    rcases hk.lt_or_eq with hk | rfl
    · rw [hδv, ite_eq_left hk]
    · rw [hδv, ite_eq_right (lt_irrefl _), Nat.sub_self, hr.δ_zero]
  have hhle : ∀ k ≤ κ, hv k = P.h₀ := fun k hk => by
    rcases hk.lt_or_eq with hk | rfl
    · rw [hhv, ite_eq_left hk]
    · rw [hhv, ite_eq_right (lt_irrefl _), Nat.sub_self, hr.h_zero]
  have hnacc : ∀ k < κ, ¬ accv k := fun k hk => by rw [haccv, ite_eq_left hk]; exact not_false
  have hρ1 : ∀ k < κ, arqpIDARatio f P Dv Xv sv k = 1 := fun k hk => by
    obtain ⟨-, -, hfv, hpos⟩ := hsp k hk
    rw [arqpIDARatio, reductionRatio_def, hDv, hXle k hk.le, hsv, ite_eq_left hk, hfv,
      div_self hpos.ne']
  have hstep : ∀ k, ARqpDAStep univ P (fun _ => ε) Xv σv δv δ₁v δsv hv Dv ddv jkv sv accv
      (arqpIDARatio f P Dv Xv sv) k := by
    intro k
    by_cases hk : k < κ
    · have hk1 : k + 1 ≤ κ := hk
      refine (hrun hv accv (arqpIDARatio f P Dv Xv sv) hhle (fun i hi => (hh₀ i hi).2) hnacc hρ1
        k hk).congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ Iff.rfl rfl
      · exact hXle k hk.le
      · exact hXle (k + 1) hk1
      · exact hσle k hk.le
      · exact hσle (k + 1) hk1
      · exact hδle k hk.le
      · exact hδle (k + 1) hk1
      · rw [hδ₁v, ite_eq_left hk]
      · rw [hδsv, ite_eq_left hk]
      · rfl
      · rfl
      · rw [hDv, hXle k hk.le]
      · rw [hDv, hXle (k + 1) hk1]
      · rw [hddv, ite_eq_left hk]
      · rw [hjkv, ite_eq_left hk]
      · rw [hsv, ite_eq_left hk]
    · have hk' : κ ≤ k := not_lt.1 hk
      have hk1 : ¬ k + 1 < κ := by omega
      have hsub : k + 1 - κ = k - κ + 1 := by omega
      refine (hr.step (k - κ)).congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rw [hXv, ite_eq_right hk]
      · rw [hXv, ite_eq_right hk1, hsub]
      · rw [hσv, ite_eq_right hk]
      · rw [hσv, ite_eq_right hk1, hsub]
      · rw [hδv, ite_eq_right hk]
      · rw [hδv, ite_eq_right hk1, hsub]
      · rw [hδ₁v, ite_eq_right hk]
      · rw [hδsv, ite_eq_right hk]
      · rw [hhv, ite_eq_right hk]
      · rw [hhv, ite_eq_right hk1, hsub]
      · rw [hDv, hD', hXv, ite_eq_right hk]
      · rw [hDv, hD', hXv, ite_eq_right hk1, hsub]
      · rw [hddv, ite_eq_right hk]
      · rw [hjkv, ite_eq_right hk]
      · rw [hsv, ite_eq_right hk]
      · rw [haccv, ite_eq_right hk]
      · rw [arqpIDARatio, arqpIDARatio, hDv, hD', hXv, ite_eq_right hk, hsv, ite_eq_right hk]
  have hrun' : algorithm_13_1_2_feasible f univ (fun _ => 0) P (fun _ => ε) 0 Xv σv δv δ₁v δsv
      hv Dv ddv jkv sv accv :=
    ⟨hεv, hεδ, fun _ _ => le_rfl, by rw [hXle 0 (Nat.zero_le _), hX0], mem_univ _,
      hσle 0 (Nat.zero_le _), hδle 0 (Nat.zero_le _), hhle 0 (Nat.zero_le _),
      fun k => by rw [hDv]; exact (jetApprox_self _ _).mono_err fun i _ => by simp, hstep⟩
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have hqf : (0 : ℝ) < P.q ! := by positivity
  have htest : ∀ k ≤ κ, (arTest_feasible f univ P (fun _ => ε) Xv k ↔ k = κ) := by
    intro k hk
    rw [arTest_feasible, setOf_add_mem_univ, hXle k hk]
    constructor
    · rintro ⟨δ', hδ', ht⟩
      by_contra hne
      have h1 := ht P.q hqm
      have hδq := (hδ' P.q hqm).1
      rw [hmeas k hk P.q hqm _ hδq.le, ite_eq_left rfl] at h1
      have h2 := ha_gt k (lt_of_le_of_ne hk hne)
      have h3 : 0 < δ' P.q ^ P.q := by positivity
      have : a k / P.q ! * δ' P.q ^ P.q > ε * δ' P.q ^ P.q / P.q ! := by
        rw [div_mul_eq_mul_div]
        exact div_lt_div_of_pos_right (by nlinarith) hqf
      linarith
    · rintro rfl
      refine ⟨fun _ => 1, fun _ _ => ⟨one_pos, le_rfl⟩, fun j hj => ?_⟩
      rw [hmeas k hk j hj 1 zero_le_one, one_pow, mul_one, one_pow, mul_one]
      split_ifs with hjq
      · subst hjq; rw [ha_eq, one_mul]
      · positivity
  refine ⟨Xv, σv, δv, δ₁v, δsv, hv, Dv, ddv, jkv, sv, accv, hrun', hDv,
    fun u Lb hLb k => RadiiControlOf.of_unit hLb (fun _ _ => hε1) fun hk hs1 j hj => ?_,
    ⟨(htest κ le_rfl).2 rfl, fun i hi ht => hi.ne ((htest i hi.le).1 ht)⟩, ?_, ?_⟩
  · by_cases hkκ : k < κ
    · rw [hδsv, ite_eq_left hkκ]; exact hδ₀ j hj
    · rw [hδsv, ite_eq_right hkκ]
      rw [haccv, ite_eq_right hkκ] at hk
      rw [hsv, ite_eq_right hkκ] at hs1
      exact (hrc' (k - κ) hk hs1).1 hq2 j hj
  · rw [derivEvalCount_of_forall hnacc]; push_cast at hκge ⊢; linarith
  · rw [derivEvalCount_of_forall fun i hi => Or.inr ⟨hnacc i hi, by
      rw [hρ1 i hi]; exact P.η₁_le_η₂.trans P.η₂_lt_one.le⟩]
    push_cast at hκge ⊢; linarith

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the ARqpEDA-SC row for `q ∈ {1, 2}`:
the order `ε^{-(p+1)/(p-q+1)}` of the unit-radii mode is attained with the (simple) feasible set
`X = ℝ¹` (`univ`) and exact derivatives and function values. For `1 ≤ q ≤ min(2, p)` there are
`f_low`, `L ≥ 1` and `ε₀ > 0` such that, for every `ε ∈ (0, ε₀]` (all `ε_j = ε`) and all ARqpEDA
constants with orders `p, q`, `σ₀ = p!/(q-1)!`, unit initial radii, (13.3.13)
`κ_s ≤ min(η₁, 1 - η₂)/4`, initial accuracies passing (13.1.46) along the steps
(`h_{0,i} ≤ κ_s (ε/2)^{p-i+1}`) and the termination test (13.3.17) at unit radii
(`∑_{i=1}^j h_{0,i}/i! ≤ ½ ς ε/j!`), there is `f` with f.bB and f.D0pL (all `L_{f,j} = L`) and
an ARqpEDA-SC run with exact derivatives and function values from `x₀ = 0` satisfying the radii
control in both modes (`Chapter13.RadiiControlOf u` for every `u` and every `L̄ ≥ 1`), which
first terminates at `k_ε = ⌈ε^{-(p+1)/(p-q+1)}⌉`, after `2 k_ε ≥ 2 ε^{-(p+1)/(p-q+1)}` function
evaluations (each value recomputed) and `k_ε + 1 ≥ ε^{-(p+1)/(p-q+1)} + 1` derivative
evaluations. The run is the slow example of Theorem 12.2.15 with `f` halved (spike jets
`f^{(q)}(x_k) = -(ε + ω_k)/2`, steps the global model minimizers, `σ_k = σ₀`, `ρ_k = 1`, no
accuracy-improving iteration, the Step-1 radius of order `q` halved to the scale of the step), the
halving making the test (13.1.53), whose threshold is half that of ARqp, pass exactly at
`k_ε`. For `q = 1` and for `q = p = 2` the order is also the order `ε^{-q(p+1)/p}` of the
lower-bound mode. -/
theorem theorem_14_2_4_sharp_arqpeda {p q : ℕ} (hq : 1 ≤ q) (hq2 : q ≤ 2) (hqp : q ≤ p) :
    ∃ flow L ε₀ : ℝ, 1 ≤ L ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ P : ARqpIDAParams,
      P.p = p → P.q = q → P.σ₀ = (p ! : ℝ) / (q - 1)! → (∀ j ∈ Finset.Icc 1 q, P.δ₀ j = 1) →
      P.κs ≤ min P.η₁ (1 - P.η₂) / 4 →
      (∀ i ∈ Finset.Icc 1 p, P.h₀ i ≤ P.κs * (ε / 2) ^ (p - i + 1)) →
      (∀ j ∈ Finset.Icc 1 q, ∑ i ∈ Finset.Icc 1 j, P.h₀ i / i ! ≤ P.ς * ε / j ! / 2) →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, (∀ y, flow ≤ f y) ∧ AssumptionD0pL f p (fun _ => L) ∧
        ∃ (x : ℕ → EuclideanSpace ℝ (Fin 1)) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ)
          (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)
          (dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)) (jk : ℕ → ℕ)
          (s : ℕ → EuclideanSpace ℝ (Fin 1)) (acc : ℕ → Prop) (fx fxs h₀ : ℕ → ℝ)
          (R : ℕ → Prop),
          algorithm_13_3_2_feasible f univ P (fun _ => ε) 0 x σ δ δ₁ δs h D dd jk s acc fx fxs
            h₀ R ∧
          (∀ k, D k = ftaylorSeries ℝ f (x k) ∧ fx k = f (x k) ∧ fxs k = f (x k + s k)) ∧
          (∀ (u : Prop) (Lb : ℝ), 1 ≤ Lb → ∀ k, RadiiControlOf u P (fun _ => ε) Lb σ δs s acc k) ∧
          IsFirstHit (edaStopAR P (fun _ => ε) D δ₁ h dd)
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ ∧
          2 * ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ))) ≤ (edaFunEvalCount acc R
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ : ℝ) ∧
          ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ))) + 1 ≤ (derivEvalCount (fun i => acc i ∨
            (¬ acc i ∧ P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i))
              ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ : ℝ) := by
  obtain ⟨flow, L, ε₀, hL, hε₀, hε₀4, H⟩ := exists_slowARqp_run hq hq2 hqp (lam := 1 / 2)
    le_rfl (by norm_num)
  refine ⟨flow, L, ε₀, hL, hε₀, fun ε hε hεε P hPp hPq hσ hδ₀ hκs hh₀ hsum => ?_⟩
  obtain ⟨f, hb, hf, X, δ₁, dd, s, a, hX0, ha_gt, ha_eq, -, hsp, hnp, hδ₁κ, hddκ, hstep1κ,
    hrun⟩ := H ε hε hεε P hPp hPq hσ hδ₀
  subst hPp hPq
  refine ⟨f, hb, hf, ?_⟩
  set κ := ⌈ε ^ (-((P.p + 1 : ℝ) / ((P.p - P.q + 1 : ℕ) : ℝ)))⌉₊ with hκ
  have hκge : ε ^ (-((P.p + 1 : ℝ) / ((P.p - P.q + 1 : ℕ) : ℝ))) ≤ κ := Nat.le_ceil _
  clear_value κ
  have hε1 : ε ≤ 1 := by linarith
  set D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ :=
    fun i => ftaylorSeries ℝ f (X i) with hD
  set fx : ℕ → ℝ := fun k => f (X k) with hfx
  set fxs : ℕ → ℝ := fun k => f (X k + s k) with hfxs
  set ρ : ℕ → ℝ := edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) with hρ
  have hρ1 : ∀ k < κ, ρ k = 1 := fun k hk => by
    obtain ⟨-, -, hfv, hpos⟩ := hsp k hk
    simp only [hρ, edaRatio, hfx, hfxs]
    rw [hfv, div_self hpos.ne']
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have hstop : ∀ k ≤ κ, (edaStopAR P (fun _ => ε) D δ₁ (fun _ => P.h₀) dd k ↔ k = κ) := by
    intro k hk
    constructor
    · rintro ⟨hp, -⟩
      by_contra hne
      exact hnp k (lt_of_le_of_ne hk hne) (hp _ hqm)
    · rintro rfl
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · rw [arPass, hddκ j hj, hδ₁κ, one_pow, mul_one]
        split_ifs with hjq
        · subst hjq; rw [ha_eq]; apply le_of_eq; ring
        · rw [mul_zero]; have := P.ς_pos; positivity
      · rw [hδ₁κ]
        simp only [one_pow, mul_one]
        exact hsum j hj
  have hnstop : ∀ k < κ, ¬ edaStopAR P (fun _ => ε) D δ₁ (fun _ => P.h₀) dd k :=
    fun k hk hs => hk.ne ((hstop k hk.le).1 hs)
  have hreach : ∀ k, (∀ j < k, ¬ edaStopAR P (fun _ => ε) D δ₁ (fun _ => P.h₀) dd j) → k ≤ κ :=
    fun k hk => by
      by_contra hge
      exact hk κ (not_le.1 hge) ((hstop κ le_rfl).2 rfl)
  have hstep := hrun (fun _ => P.h₀) (fun _ => False) ρ (fun _ _ => rfl) hh₀
    (fun _ _ => not_false) hρ1
  have hrun' : algorithm_13_3_2_feasible f univ P (fun _ => ε) 0 X (fun _ => P.σ₀)
      (fun _ => P.δ₀) δ₁ (fun _ => P.δ₀) (fun _ => P.h₀) D dd (fun _ => P.q) s (fun _ => False)
      fx fxs
      (fun k => P.κs * (D k).taylorDecrement P.p (s k)) (fun _ => True) := by
    refine ⟨hκs, fun _ _ => ⟨hε, hε1⟩, fun j hj => by rw [hδ₀ j hj]; exact hε1, hX0, mem_univ _,
      rfl, rfl, rfl, fun k _ => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · exact (jetApprox_self _ _).mono_err fun i hi => P.h₀_nonneg i hi
    · rcases (hreach k hk).lt_or_eq with hlt | rfl
      · exact (hstep k hlt).toARqpStep1
      · exact hstep1κ
    · have hkκ : k < κ := by
        rcases (hreach k fun j hj => hk j hj.le).lt_or_eq with hlt | rfl
        · exact hlt
        · exact absurd ((hstop k le_rfl).2 rfl) (hk k le_rfl)
      obtain ⟨-, -, -, hpos⟩ := hsp k hkκ
      have hpos' : 0 < P.κs * (D k).taylorDecrement P.p (s k) := mul_pos P.κs_pos hpos
      exact ⟨hstep k hkκ, fun _ => ⟨hpos', le_rfl, by simp [hfxs, hpos'.le],
        by simp [hfx, hpos'.le], fun h => absurd trivial h⟩⟩
  refine ⟨X, fun _ => P.σ₀, fun _ => P.δ₀, δ₁, fun _ => P.δ₀, fun _ => P.h₀, D, dd,
    fun _ => P.q, s, fun _ => False, fx, fxs, fun k => P.κs * (D k).taylorDecrement P.p (s k),
    fun _ => True, hrun', fun k => ⟨rfl, rfl, rfl⟩,
    fun u Lb hLb k => RadiiControlOf.of_unit hLb (fun _ _ => hε1) fun _ _ j hj => hδ₀ j hj,
    ⟨(hstop κ le_rfl).2 rfl, hnstop⟩, ?_, ?_⟩
  · rw [edaFunEvalCount, card_filter_range_of_forall fun _ _ => not_false,
      card_filter_range_of_forall fun _ _ => ⟨not_false, trivial⟩]
    push_cast at hκge ⊢; linarith
  · rw [derivEvalCount_of_forall fun i hi => Or.inr ⟨not_false, by
      rw [← hρ, hρ1 i hi]; exact P.η₁_le_η₂.trans P.η₂_lt_one.le⟩]
    push_cast at hκge ⊢; linarith

/-- The weight `σ = (3/(p+2))^p` of the gradient interpolant. -/
private theorem slowGrad_sigma_pos (p : ℕ) : (0 : ℝ) < (3 / ((p : ℝ) + 2)) ^ p := by positivity

/-- **The slow gradient example on `ℝ¹`** (the data of Theorem 12.2.17 with `r = p` and the weight
`σ = (3/(p+2))^p`, lifted along `e₁` and halved). For `1 ≤ q ≤ p` there are `f_low` and `L ≥ 1`
such that, for every `ε ∈ (0, 1]`, with `k_ε = ⌈ε^{-q(p+1)/p}⌉`,
`β_k = (ε^q + ε^{qp/p} (k_ε - k)/k_ε)/q!` and points `x_{k+1} = x_k + (p! β_k/σ)^{1/p}`, there is a
`C^p` function `g` of one variable whose ridge `f = g(⟪e₁, ·⟫)` satisfies f.bB and f.D0pL (all
`L_{f,j} = L`), with spike jets `g'(x_k) = -β_k/2` (other derivatives of orders `2, …, p` zero)
for `k ≤ k_ε` and `g(x_{k+1}) = g(x_k) - β_k/2 (x_{k+1} - x_k)` for `k < k_ε`. -/
private theorem exists_slowGrad_ridge {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ xr : ℕ → ℝ,
      (∀ k < ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊, xr (k + 1) = xr k + (p ! *
        ((ε ^ q + ε ^ ((q : ℝ) * p / p) * ((⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ : ℝ) - k) /
          ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊) / q !) / (3 / ((p : ℝ) + 2)) ^ p) ^
            (1 / (p : ℝ))) →
      ∃ g : ℝ → ℝ, ContDiff ℝ p g ∧ (∀ y, flow ≤ ridge g u₁ y) ∧
        AssumptionD0qL (ridge g u₁) p (fun _ => L) ∧
        (∀ k ≤ ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊, IsSpikeJetOf p g 1 (xr k)
          ((ε ^ q + ε ^ ((q : ℝ) * p / p) * ((⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ : ℝ) - k) /
            ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊) / q ! / 2)) ∧
        ∀ k < ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊, g (xr (k + 1)) = g (xr k) -
          (ε ^ q + ε ^ ((q : ℝ) * p / p) * ((⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ : ℝ) - k) /
            ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊) / q ! / 2 * (xr (k + 1) - xr k) := by
  obtain ⟨L, B, hL, hB, hG⟩ :=
    exists_slowARqpSmooth_interpolant hq hqp le_rfl (slowGrad_sigma_pos p)
  refine ⟨-B, max 1 (max L B), le_max_left _ _, fun ε hε hε1 xr hxr => ?_⟩
  obtain ⟨G, hGc, hGL, hGB, hGd, hGf⟩ := hG ε _ xr hε hε1 rfl hxr
  set g : ℝ → ℝ := fun t => (1 / 2 : ℝ) * G t with hg
  have hgc : ContDiff ℝ p g := contDiff_const.mul hGc
  have hgj : ∀ j t, iteratedDeriv j g t = 1 / 2 * iteratedDeriv j G t := fun j t =>
    iteratedDeriv_const_mul_field (1 / 2 : ℝ) G
  obtain ⟨hfc, hfb, hfl⟩ := ridge_const_mul_slow_bounds (G := G) (lam := 1 / 2) (e := u₁) hGc hB
    hGL hGB (by norm_num) (by norm_num) norm_u₁.le
  refine ⟨g, hgc, hfb, ⟨hfc, fun j hj => ⟨le_max_left _ _, hfl j hj⟩⟩,
    fun k hk => ⟨?_, fun j hj1 hjp hj => ?_⟩, fun k hk => ?_⟩
  · rw [hgj, iteratedDeriv_one, (hGd k hk).1]; ring
  · rw [hgj, (hGd k hk).2 j (by omega) hjp, mul_zero]
  · simp only [hg]
    rw [hGf k hk]; ring

section SlowGradStep

variable {P : ARqpIDAParams} {ε β : ℝ} {x : ℕ → EuclideanSpace ℝ (Fin 1)} {σ : ℕ → ℝ}
  {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ}
  {D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ}
  {dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)} {jk : ℕ → ℕ} {s : ℕ → EuclideanSpace ℝ (Fin 1)}
  {acc : ℕ → Prop} {ρ : ℕ → ℝ} {k : ℕ}

/-- `ε^q/q! ≤ ½ ε^j/j!` for `j < q` and `0 ≤ ε ≤ ½`. -/
private theorem slowGrad_pow_le {j q : ℕ} (hε : 0 ≤ ε) (hε2 : ε ≤ 1 / 2) (hjq : j < q) :
    ε ^ q / q ! ≤ ε ^ j / j ! / 2 := by
  have h1 : ε ^ q ≤ ε ^ j / 2 := by
    have e : ε ^ q = ε ^ j * ε ^ (q - j) := by rw [← pow_add]; congr 1; omega
    have h2 : ε ^ (q - j) ≤ ε := pow_le_of_le_one hε (by linarith) (by omega)
    rw [e]
    have := pow_nonneg hε j
    nlinarith
  have hjf : (j ! : ℝ) ≤ q ! := by exact_mod_cast Nat.factorial_le hjq.le
  have hj0 : (0 : ℝ) < j ! := by positivity
  calc ε ^ q / q ! ≤ ε ^ j / 2 / q ! := div_le_div_of_nonneg_right h1 (by positivity)
    _ ≤ ε ^ j / 2 / j ! := div_le_div_of_nonneg_left (by positivity) hj0 hjf
    _ = ε ^ j / j ! / 2 := by ring

/-- The Step-1 decreases along the slow gradient example: `ς β ε` at every order. -/
private theorem slowGrad_dec_dd (hε : 0 < ε) (hβ : 0 < β)
    (hdec : ∀ j ∈ Finset.Icc 1 P.p, ∀ d, (D k).taylorDecrement j d = β * ⟪u₁, d⟫)
    (hdd : ∀ j ∈ Finset.Icc 1 P.q,
      IsApproxMeasureStep ((D k).taylorDecrement j) ε univ P.ς (dd k j) ∧
        (D k).taylorDecrement j (dd k j) = P.ς * taylorMeasure (D k) j ε univ)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 P.q) :
    (D k).taylorDecrement j (dd k j) = P.ς * (β * ε) := by
  rw [(hdd j hj).2, taylorMeasure_of_dec (q := 1) hβ.le hε.le fun d => by
    rw [hdec j (P.Icc_q_subset hj), pow_one], pow_one]

/-- Along the slow gradient example the test (13.1.53) fails at order `q` (`β > ε^q/(2 q!)`). -/
private theorem slowGrad_not_pass (hε : 0 < ε) (hβ : ε ^ P.q / P.q ! / 2 < β)
    (hδ₁ : δ₁ k P.q = ε) (hdq : (D k).taylorDecrement P.q (dd k P.q) = P.ς * (β * ε)) :
    ¬ arPass P (fun _ => ε) D δ₁ dd k P.q := by
  rw [arPass, hdq, hδ₁, not_le]
  have : ε * ε ^ P.q / P.q ! / 2 < β * ε := by
    rw [show ε * ε ^ P.q / P.q ! / 2 = ε ^ P.q / P.q ! / 2 * ε by ring]
    exact mul_lt_mul_of_pos_right hβ hε
  have e : P.ς * ε * ε ^ P.q / P.q ! / 2 = P.ς * (ε * ε ^ P.q / P.q ! / 2) := by ring
  rw [e]
  exact mul_lt_mul_of_pos_left this P.ς_pos

/-- **One iteration of the slow gradient example is an ARqpIDA/ARqpEDA step** (`X = univ`,
tolerances `ε_j = ε ≤ ½`): with radii `δ_k = δ^{(1)}_k = δ_{k+1} = δ_{s_k} = ε`, decrements
`β ⟪e₁, d⟫` at all orders `1, …, p` with `ε^q/(2 q!) < β ≤ ε^q/q!`, a weight with
`σ_k/(p+1)! ≤ 1/(4 q!)`, Step-1 displacements achieving the fraction `ς` of the measures, a global
minimizer `s_k` of the model as step, short, with nonpositive model decrements of orders
`1, …, q` on the ball of radius `ε` around it, accuracies passing (13.1.46), and the ratio
`ρ_k = 1`. -/
private theorem slowGrad_arqpDAStep (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hβ : ε ^ P.q / P.q ! / 2 < β) (hβ1 : β ≤ ε ^ P.q / P.q !)
    (hσ54 : σ k / ((P.p + 1)! : ℝ) ≤ 1 / (4 * P.q !))
    (hδ : ∀ j ∈ Finset.Icc 1 P.q, δ k j = ε) (hδ1 : δ (k + 1) = δs k) (hδ₁ : δ₁ k = δ k)
    (hδs : ∀ j ∈ Finset.Icc 1 P.q, δs k j = ε) (hjk : jk k = P.q)
    (hdec : ∀ j ∈ Finset.Icc 1 P.p, ∀ d, (D k).taylorDecrement j d = β * ⟪u₁, d⟫)
    (hdd : ∀ j ∈ Finset.Icc 1 P.q,
      IsApproxMeasureStep ((D k).taylorDecrement j) ε univ P.ς (dd k j) ∧
        (D k).taylorDecrement j (dd k j) = P.ς * taylorMeasure (D k) j ε univ)
    (hmin : IsMinOn (regularizedModel (D k) P.p (σ k)) univ (s k))
    (hmodel : ∀ ℓ ∈ Finset.Icc 1 P.q, ∀ d, ‖d‖ ≤ ε →
      (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ d ≤ 0)
    (hs1 : ‖s k‖ < 1) (hhk : ∀ i ∈ Finset.Icc 1 P.p, h k i ≤ P.κs * ‖s k‖ ^ (P.p - i + 1))
    (hacc : ¬ acc k) (hx1 : x (k + 1) = x k + s k) (hσ1 : σ (k + 1) = σ k)
    (hσk : P.σmin ≤ σ k) (hh1 : h (k + 1) = h k) (hρ : ρ k = 1) :
    ARqpDAStep univ P (fun _ => ε) x σ δ δ₁ δs h D dd jk s acc ρ k := by
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  have hqf : (0 : ℝ) < P.q ! := by positivity
  have hβ0 : 0 < β := lt_of_le_of_lt (by positivity) hβ
  have hσ0 : 0 ≤ σ k := P.σmin_pos.le.trans hσk
  have hη : P.η₁ ≤ 1 := P.η₁_le_η₂.trans P.η₂_lt_one.le
  have hdv := fun {j} (hj : j ∈ Finset.Icc 1 P.q) => slowGrad_dec_dd (dd := dd) hε hβ0 hdec hdd hj
  have hfail : ¬ arPass P (fun _ => ε) D δ₁ dd k P.q :=
    slowGrad_not_pass hε hβ (by rw [hδ₁, hδ _ hqm]) (hdv hqm)
  have hpass_lt : ∀ j ∈ Finset.Icc 1 P.q, j < P.q → arPass P (fun _ => ε) D δ₁ dd k j := by
    intro j hj hlt
    rw [arPass, hdv hj, hδ₁, hδ j hj]
    have h1 := slowGrad_pow_le hε.le hε2 hlt
    have h2 : β * ε ≤ ε * ε ^ j / j ! / 2 := by
      rw [show ε * ε ^ j / j ! / 2 = ε ^ j / j ! / 2 * ε by ring]
      exact mul_le_mul_of_nonneg_right (hβ1.trans h1) hε.le
    have e : P.ς * ε * ε ^ j / j ! / 2 = P.ς * (ε * ε ^ j / j ! / 2) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h2 hς.le
  refine ⟨⟨fun j hj => by rw [hδ₁, hδ j hj]; exact hε, fun j _ => by rw [hδ₁],
    fun j _ hlt => by rw [hδ₁] at hlt; exact absurd hlt (lt_irrefl _),
    fun j _ => ⟨0, by rw [hδ₁]; norm_num⟩, fun j hj => ?_⟩,
    fun hp => absurd (hp _ hqm) hfail, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => hh1,
    fun _ hr' => absurd hr' (by rw [hρ]; exact not_lt.2 hη), fun ha' => absurd ha' hacc,
    fun ha' => absurd ha' hacc, fun ha' => absurd ha' hacc, fun ha' => absurd ha' hacc⟩
  · rw [hδ₁, hδ j hj, setOf_add_mem_univ]; exact (hdd j hj).1
  · -- Step 2
    refine ⟨by rw [hjk]; exact hqm, by rw [hjk]; exact hfail,
      fun j hj hlt => hpass_lt j hj (by rw [hjk] at hlt; exact hlt),
      fun j hj hlt => absurd (Finset.mem_Icc.1 hj).2 (by rw [hjk] at hlt; omega), ?_,
      mem_univ _, ?_, Or.inr fun ℓ hℓ => ?_, iff_of_false hacc ?_⟩
    · -- (13.1.54)
      rw [hjk, hδ₁, hδ _ hqm, arModelDec_eq]
      have hdq := hdv hqm
      have hdp : (D k).taylorDecrement P.p (dd k P.q) = P.ς * (β * ε) := by
        rw [hdec _ (Finset.mem_Icc.2 ⟨P.one_le_p, le_rfl⟩), ← hdec _ (P.Icc_q_subset hqm), hdq]
      have hin : ⟪u₁, dd k P.q⟫ = P.ς * ε := by
        rw [hdec _ (P.Icc_q_subset hqm)] at hdq
        have : β * ⟪u₁, dd k P.q⟫ = β * (P.ς * ε) := by rw [hdq]; ring
        exact mul_left_cancel₀ hβ0.ne' this
      rw [hdp, norm_eq_abs_inner_u₁, hin, abs_of_pos (by positivity)]
      have hpow : (P.ς * ε) ^ (P.p + 1) ≤ P.ς * ε ^ (P.q + 1) := by
        rw [mul_pow]
        exact mul_le_mul (pow_le_of_le_one hς.le hς1 (by omega))
          (pow_le_pow_of_le_one hε.le (by linarith) (by have := P.q_le_p; omega))
          (by positivity) hς.le
      have h3 : σ k / ((P.p + 1)! : ℝ) * (P.ς * ε) ^ (P.p + 1) ≤
          1 / (4 * P.q !) * (P.ς * ε ^ (P.q + 1)) :=
        mul_le_mul hσ54 hpow (by positivity) (by positivity)
      have h2 : P.ς * (ε * ε ^ P.q / P.q ! / 2) < P.ς * (β * ε) := by
        refine mul_lt_mul_of_pos_left ?_ hς
        rw [show ε * ε ^ P.q / P.q ! / 2 = ε ^ P.q / P.q ! / 2 * ε by ring]
        exact mul_lt_mul_of_pos_right hβ hε
      have e1 : P.ς * ε * ε ^ P.q / P.q ! / 4 = 1 / (4 * P.q !) * (P.ς * ε ^ (P.q + 1)) := by
        rw [pow_succ]; field_simp
      have e2 : P.ς * (ε * ε ^ P.q / P.q ! / 2) = 2 * (1 / (4 * P.q !) * (P.ς * ε ^ (P.q + 1))) :=
        by rw [pow_succ]; field_simp; ring
      linarith
    · simp only [arModelDec]
      have := isMinOn_iff.1 hmin (dd k (jk k)) (mem_univ _)
      linarith
    · have hℓ' : ∀ d ∈ closedBall (0 : EuclideanSpace ℝ (Fin 1)) ε ∩ univ,
          (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ d ≤ 0 :=
        fun d hd => hmodel ℓ hℓ d (mem_closedBall_zero_iff.1 hd.1)
      rw [hδs ℓ hℓ, setOf_add_mem_univ]
      refine ⟨⟨hε, by linarith⟩, 0, ⟨⟨mem_closedBall_self hε.le, mem_univ _⟩, ?_⟩, ?_⟩
      · rw [FormalMultilinearSeries.taylorDecrement_zero_right]
        exact mul_nonpos_of_nonneg_of_nonpos hς.le
          (decrementMeasure_le ⟨0, mem_closedBall_self hε.le, mem_univ _⟩ hℓ')
      · rw [FormalMultilinearSeries.taylorDecrement_zero_right]
        have := P.θ_pos
        positivity
    · rintro ⟨-, i, hi, hlt⟩
      linarith [hhk i hi]
  · rw [hρ, hx1, hσ1]
    exact arAcceptance_of_one_le P.toARParams le_rfl _ _ hσk hσ0
  · rw [hδ1, hρ, ite_eq_left ⟨hη, hs1⟩]

end SlowGradStep

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the ARqpEDA-SC row in the
lower-bound mode of the radii control (the "otherwise" order `ε^{-q(p+1)/p}`), for every
`1 ≤ q ≤ p`, with the (simple) feasible set `X = ℝ¹` (`univ`) and exact derivatives and function
values. There are `f_low`, `L ≥ 1` and `ε₀ > 0` such that, for every `ε ∈ (0, ε₀]` (all
`ε_j = ε`) and all ARqpEDA constants with orders `p, q`, weight `σ₀ = (3/(p+2))^p/2`, initial
radii `δ₀ = ε`, (13.3.13) `κ_s ≤ min(η₁, 1 - η₂)/4`, initial accuracies passing (13.1.46) along
the steps (`h_{0,i} ≤ κ_s ε^{p-i+1}`) and the termination test (13.3.17) at radius `ε`
(`∑_{i=1}^j h_{0,i} ε^i/i! ≤ ½ ς ε ε^j/j!`), there is `f` with f.bB and f.D0pL (all
`L_{f,j} = L`) and an ARqpEDA-SC run with exact derivatives and function values from `x₀ = 0`
satisfying the radii control in the lower-bound mode (`Chapter13.RadiiControlOf False` for every
`L̄ ≥ 1`; all radii are `ε`), which first terminates at `k_ε = ⌈ε^{-q(p+1)/p}⌉`, after
`2 k_ε ≥ 2 ε^{-q(p+1)/p}` function evaluations (each value recomputed) and
`k_ε + 1 ≥ ε^{-q(p+1)/p} + 1` derivative evaluations. The run is the slow example of
Theorem 12.2.17 (with `r = p`) with `f` halved and a smaller weight: gradient spikes
`f'(x_k) = -β_k/2`, `β_k = (ε^q + ω_k)/q!`, steps the global model minimizers, `σ_k = σ₀`,
`ρ_k = 1`, no accuracy-improving iteration, and Step-1 displacements achieving exactly the
fraction `ς` of the measures; the weight is small enough for (13.1.54) to hold at these
displacements (unlike with the weight (12.2.85) of Theorem 12.2.17) and for the measures of the
model at its minimizer to vanish at radius `ε` (Example 12.1.3). -/
theorem theorem_14_2_4_sharp_arqpeda_otherwise {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    ∃ flow L ε₀ : ℝ, 1 ≤ L ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ P : ARqpIDAParams,
      P.p = p → P.q = q → P.σ₀ = (3 / ((p : ℝ) + 2)) ^ p / 2 → (∀ j ∈ Finset.Icc 1 q, P.δ₀ j = ε) →
      P.κs ≤ min P.η₁ (1 - P.η₂) / 4 →
      (∀ i ∈ Finset.Icc 1 p, P.h₀ i ≤ P.κs * ε ^ (p - i + 1)) →
      (∀ j ∈ Finset.Icc 1 q, ∑ i ∈ Finset.Icc 1 j, P.h₀ i * ε ^ i / i ! ≤
        P.ς * ε * ε ^ j / j ! / 2) →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, (∀ y, flow ≤ f y) ∧ AssumptionD0pL f p (fun _ => L) ∧
        ∃ (x : ℕ → EuclideanSpace ℝ (Fin 1)) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ)
          (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)
          (dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)) (jk : ℕ → ℕ)
          (s : ℕ → EuclideanSpace ℝ (Fin 1)) (acc : ℕ → Prop) (fx fxs h₀ : ℕ → ℝ)
          (R : ℕ → Prop),
          algorithm_13_3_2_feasible f univ P (fun _ => ε) 0 x σ δ δ₁ δs h D dd jk s acc fx fxs
            h₀ R ∧
          (∀ k, D k = ftaylorSeries ℝ f (x k) ∧ fx k = f (x k) ∧ fxs k = f (x k + s k)) ∧
          (∀ Lb : ℝ, 1 ≤ Lb → ∀ k, RadiiControlOf False P (fun _ => ε) Lb σ δs s acc k) ∧
          IsFirstHit (edaStopAR P (fun _ => ε) D δ₁ h dd)
            ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ ∧
          2 * ε ^ (-((q : ℝ) * (p + 1) / p)) ≤
            (edaFunEvalCount acc R ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ : ℝ) ∧
          ε ^ (-((q : ℝ) * (p + 1) / p)) + 1 ≤ (derivEvalCount (fun i => acc i ∨
            (¬ acc i ∧ P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i))
              ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ : ℝ) := by
  obtain ⟨flow, L, hL, H⟩ := exists_slowGrad_ridge hq hqp
  have hp : 1 ≤ p := hq.trans hqp
  have hσI := slowGrad_sigma_pos p
  refine ⟨flow, L, min (1 / 2) ((3 / ((p : ℝ) + 2)) ^ p / (4 * p !)), hL, by positivity,
    fun ε hε hεε P hPp hPq hσ hδ₀ hκs hh₀ hsum => ?_⟩
  subst hPp hPq
  have hε2 : ε ≤ 1 / 2 := hεε.trans (min_le_left _ _)
  have hεσ : ε ≤ (3 / ((P.p : ℝ) + 2)) ^ P.p / (4 * P.p !) := hεε.trans (min_le_right _ _)
  have hε1 : ε ≤ 1 := by linarith
  set σI : ℝ := (3 / ((P.p : ℝ) + 2)) ^ P.p with hσIdef
  have hσI1 : σI ≤ 1 := pow_le_one₀ (by positivity) (by
    rw [div_le_one (by positivity)]; have : (1 : ℝ) ≤ P.p := by exact_mod_cast hp
    linarith)
  have hκ1 : 1 ≤ ⌈ε ^ (-((P.q : ℝ) * (P.p + 1) / P.p))⌉₊ :=
    Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hε _)).ne'
  have hκge : ε ^ (-((P.q : ℝ) * (P.p + 1) / P.p)) ≤ ⌈ε ^ (-((P.q : ℝ) * (P.p + 1) / P.p))⌉₊ :=
    Nat.le_ceil _
  set κ := ⌈ε ^ (-((P.q : ℝ) * (P.p + 1) / P.p))⌉₊ with hκ
  have hκpos : (0 : ℝ) < κ := by exact_mod_cast hκ1
  have hp0 : P.p ≠ 0 := by omega
  have hqpp : ε ^ ((P.q : ℝ) * P.p / P.p) = ε ^ P.q := by
    rw [mul_div_assoc, div_self (by exact_mod_cast hp0), mul_one, Real.rpow_natCast]
  have hqf : (0 : ℝ) < P.q ! := by positivity
  have hpf : (0 : ℝ) < P.p ! := by positivity
  -- the levels, the steps and the points
  set βI : ℕ → ℝ := fun k => (ε ^ P.q + ε ^ ((P.q : ℝ) * P.p / P.p) * ((κ : ℝ) - k) / κ) / P.q !
    with hβI
  set t : ℕ → ℝ := fun k => (P.p ! * βI k / σI) ^ (1 / (P.p : ℝ)) with ht
  set xr : ℕ → ℝ := fun k => ∑ i ∈ Finset.range k, t i with hxr
  have hxr1 : ∀ k, xr (k + 1) = xr k + t k := fun k => Finset.sum_range_succ _ _
  obtain ⟨g, hgc, hb, hf, hspike, hval⟩ := H ε hε hε1 xr fun k _ => hxr1 k
  have hω0 : ∀ k ≤ κ, 0 ≤ ε ^ P.q * ((κ : ℝ) - k) / κ := fun k hk => by
    have : (k : ℝ) ≤ κ := by exact_mod_cast hk
    have : 0 ≤ (κ : ℝ) - k := by linarith
    positivity
  have hω1 : ∀ k ≤ κ, ε ^ P.q * ((κ : ℝ) - k) / κ ≤ ε ^ P.q := fun k hk => by
    rw [div_le_iff₀ hκpos]
    have : (0 : ℝ) ≤ k := k.cast_nonneg
    have := pow_pos hε P.q
    nlinarith
  have hωpos : ∀ k < κ, 0 < ε ^ P.q * ((κ : ℝ) - k) / κ := fun k hk => by
    have : (k : ℝ) < κ := by exact_mod_cast hk
    have : 0 < (κ : ℝ) - k := by linarith
    positivity
  have hβI : ∀ k, βI k = (ε ^ P.q + ε ^ P.q * ((κ : ℝ) - k) / κ) / P.q ! := fun k => by
    simp only [hβI, hqpp]
  have hβ_gt : ∀ k < κ, ε ^ P.q / P.q ! / 2 < βI k / 2 := fun k hk => by
    rw [hβI]
    have := hωpos k hk
    have : ε ^ P.q / P.q ! < (ε ^ P.q + ε ^ P.q * ((κ : ℝ) - k) / κ) / P.q ! :=
      div_lt_div_of_pos_right (by linarith) hqf
    linarith
  have hβ_ge : ∀ k ≤ κ, ε ^ P.q / P.q ! ≤ βI k := fun k hk => by
    rw [hβI]
    exact div_le_div_of_nonneg_right (by linarith [hω0 k hk]) hqf.le
  have hβ_le : ∀ k ≤ κ, βI k / 2 ≤ ε ^ P.q / P.q ! := fun k hk => by
    rw [hβI]
    have := hω1 k hk
    rw [div_div, div_le_div_iff₀ (by positivity) hqf]
    nlinarith
  have hβ_eq : βI κ / 2 = ε ^ P.q / P.q ! / 2 := by
    rw [hβI, sub_self, mul_zero, zero_div, add_zero]
  have hβ_pos : ∀ k ≤ κ, 0 < βI k := fun k hk =>
    lt_of_lt_of_le (by positivity) (hβ_ge k hk)
  -- the step lengths
  have hX_ge : ∀ k ≤ κ, (ε * ((P.p + 2) / 3)) ^ P.p ≤ P.p ! * βI k / σI := fun k hk => by
    have h1 : (ε * ((P.p + 2) / 3)) ^ P.p = ε ^ P.p / σI := by
      rw [hσIdef, mul_pow, div_pow, div_pow, div_div_eq_mul_div]
      field_simp
    rw [h1, div_le_div_iff_of_pos_right hσI]
    have h2 : ε ^ P.p ≤ ε ^ P.q := pow_le_pow_of_le_one hε.le hε1 P.q_le_p
    have h3 : ε ^ P.q ≤ P.p ! * (ε ^ P.q / P.q !) := by
      rw [mul_div_assoc', le_div_iff₀ hqf]
      have : (P.q ! : ℝ) ≤ P.p ! := by exact_mod_cast Nat.factorial_le P.q_le_p
      have := pow_pos hε P.q
      nlinarith
    calc ε ^ P.p ≤ P.p ! * (ε ^ P.q / P.q !) := h2.trans h3
      _ ≤ P.p ! * βI k := mul_le_mul_of_nonneg_left (hβ_ge k hk) hpf.le
  have hX_le : ∀ k ≤ κ, P.p ! * βI k / σI ≤ 1 / 2 := fun k hk => by
    have h1 : βI k ≤ 2 * ε := by
      have := hβ_le k hk
      have h2 : ε ^ P.q / P.q ! ≤ ε := by
        rw [div_le_iff₀ hqf]
        have : (1 : ℝ) ≤ P.q ! := by
          exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
        have : ε ^ P.q ≤ ε := pow_le_of_le_one hε.le hε1 (by have := P.one_le_q; omega)
        nlinarith
      linarith
    rw [div_le_iff₀ hσI]
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * P.p !)).1 hεσ
    nlinarith
  have ht_ge : ∀ k ≤ κ, ε * ((P.p + 2) / 3) ≤ t k := fun k hk => by
    have h := Real.rpow_le_rpow (by positivity) (hX_ge k hk) (by positivity : (0 : ℝ) ≤ 1 / P.p)
    rwa [one_div, Real.pow_rpow_inv_natCast (by positivity) hp0, ← one_div] at h
  have ht_lt : ∀ k ≤ κ, t k < 1 := fun k hk =>
    Real.rpow_lt_one (by have := hβ_pos k hk; positivity) (by linarith [hX_le k hk])
      (by positivity)
  have hεt : ∀ k ≤ κ, ε ≤ t k := fun k hk => by
    have := ht_ge k hk
    have : ε ≤ ε * ((P.p + 2) / 3) := by
      have : (1 : ℝ) ≤ (P.p + 2) / 3 := by
        rw [le_div_iff₀ (by norm_num)]; have : (1 : ℝ) ≤ P.p := by exact_mod_cast hp
        linarith
      nlinarith
    linarith
  -- the function and its Taylor data
  have hσ₀ : 0 < P.σ₀ := P.σ₀_pos
  set f : EuclideanSpace ℝ (Fin 1) → ℝ := ridge g u₁ with hfdef
  set X : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => xr k • u₁ with hX
  set s : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => t k • u₁ with hs
  have hXs : ∀ k, X (k + 1) = X k + s k := fun k => by
    simp only [hX, hs, hxr1, add_smul]
  have hspX : ∀ k ≤ κ, IsSpikeJetOf P.p g 1 ⟪u₁, X k⟫ (βI k / 2) := fun k hk => by
    rw [inner_smul_u₁]; exact hspike k hk
  have hdec : ∀ k ≤ κ, ∀ j ∈ Finset.Icc 1 P.p, ∀ d,
      (ftaylorSeries ℝ f (X k)).taylorDecrement j d = βI k / 2 * ⟪u₁, d⟫ := fun k hk j hj d => by
    obtain ⟨hj1, hjp⟩ := Finset.mem_Icc.1 hj
    rw [taylorDecrement_ridge_spike (hgc.of_le (by exact_mod_cast hjp)) le_rfl hj1
      ⟨(hspX k hk).1, fun i h1 hi hne => (hspX k hk).2 i h1 (hi.trans hjp) hne⟩ d]
    simp
  have htk : ∀ k, (βI k / 2 * P.p ! / P.σ₀) ^ (1 / (P.p : ℝ)) = t k := fun k => by
    simp only [ht]
    congr 1
    rw [hσ]
    field_simp
  have hmin : ∀ k ≤ κ, IsMinOn (regularizedModel (ftaylorSeries ℝ f (X k)) P.p P.σ₀) univ
      (s k) := fun k hk => by
    obtain ⟨hm, -, -⟩ := isMinOn_neg_monomial_add_regularization le_rfl hp hσ₀
      (by have := hβ_pos k hk; positivity : 0 < βI k / 2)
    have e : (βI k / 2 / (P.σ₀ * ((1 - 1)! : ℕ) / P.p !)) ^ (1 / ((P.p - 1 + 1 : ℕ) : ℝ)) =
        t k := by
      rw [Nat.sub_add_cancel hp, ← htk]
      congr 1
      simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one]
      field_simp
    rw [e] at hm
    intro y _
    simp only [mem_ofPred_eq]
    rw [regularizedModel_ridge_spike norm_eq_abs_inner_u₁ hgc le_rfl hp (hspX k hk),
      ridge_apply, ridge_apply, show s k = t k • u₁ from rfl, inner_smul_u₁ (t k)]
    exact (add_le_add_iff_left _).2 (isMinOn_iff.1 hm _ (mem_univ _))
  have hmodel : ∀ k ≤ κ, ∀ ℓ ∈ Finset.Icc 1 P.q, ∀ d, ‖d‖ ≤ ε →
      (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f (X k)) P.p P.σ₀) (s k)).taylorDecrement
        ℓ d ≤ 0 := fun k hk ℓ hℓ d hd => by
    have h := taylorDecrement_regularizedModel_ridge_linear_nonpos norm_u₁ norm_eq_abs_inner_u₁ hp
      hgc (β := βI k / 2) (σ := P.σ₀) (δ := ε)
      (by have := hβ_pos k hk; positivity) hσ₀ (hspX k hk) (P.Icc_q_subset hℓ)
      (Or.inr (by rw [htk]; have := ht_ge k hk; nlinarith)) hd
    rwa [htk] at h
  have hdecs : ∀ k ≤ κ, (ftaylorSeries ℝ f (X k)).taylorDecrement P.p (s k) = βI k / 2 * t k :=
    fun k hk => by
      rw [hdec k hk _ (Finset.mem_Icc.2 ⟨hp, le_rfl⟩), show s k = t k • u₁ from rfl,
        inner_smul_u₁]
  have hfval : ∀ k < κ, f (X k) - f (X k + s k) =
      (ftaylorSeries ℝ f (X k)).taylorDecrement P.p (s k) := fun k hk => by
    rw [hdecs k hk.le, ← hXs, hfdef, ridge_apply, ridge_apply, hX, inner_smul_u₁, inner_smul_u₁,
      hval k hk, hxr1]
    ring
  have hdpos : ∀ k ≤ κ, 0 < (ftaylorSeries ℝ f (X k)).taylorDecrement P.p (s k) := fun k hk => by
    rw [hdecs k hk]
    have := hβ_pos k hk; have := hεt k hk
    have : 0 < t k := lt_of_lt_of_le hε this
    positivity
  have hσ54 : P.σ₀ / ((P.p + 1)! : ℝ) ≤ 1 / (4 * P.q !) := by
    have h1 : P.σ₀ ≤ 1 / 2 := by rw [hσ]; linarith
    have h2 : 2 * (P.q ! : ℝ) ≤ (P.p + 1)! := by
      have : (P.q ! : ℝ) ≤ P.p ! := by exact_mod_cast Nat.factorial_le P.q_le_p
      have e : ((P.p + 1)! : ℝ) = (P.p + 1) * P.p ! := by push_cast [Nat.factorial_succ]; ring
      rw [e]
      have : (1 : ℝ) ≤ P.p := by exact_mod_cast hp
      nlinarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  -- the Step-1 displacements
  choose w hw using fun k j => exists_slow_witness (ftaylorSeries ℝ f (X k)) j hε.le
    ⟨P.ς_pos.le, P.ς_le_one⟩
  set D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ :=
    fun i => ftaylorSeries ℝ f (X i) with hD
  set fx : ℕ → ℝ := fun k => f (X k) with hfx
  set fxs : ℕ → ℝ := fun k => f (X k + s k) with hfxs
  set ρ : ℕ → ℝ := edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) with hρ
  have hρ1 : ∀ k < κ, ρ k = 1 := fun k hk => by
    simp only [hρ, edaRatio, hfx, hfxs, hD]
    rw [hfval k hk, div_self (hdpos k hk.le).ne']
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have hdv : ∀ k ≤ κ, ∀ j ∈ Finset.Icc 1 P.q,
      (D k).taylorDecrement j (w k j) = P.ς * (βI k / 2 * ε) := fun k hk j hj =>
    slowGrad_dec_dd (D := D) (dd := w) hε (by have := hβ_pos k hk; positivity) (hdec k hk)
      (fun j _ => hw k j) hj
  have hstop : ∀ k ≤ κ, (edaStopAR P (fun _ => ε) D (fun _ => P.δ₀) (fun _ => P.h₀) w k ↔
      k = κ) := by
    intro k hk
    constructor
    · rintro ⟨hp', -⟩
      by_contra hne
      exact slowGrad_not_pass (δ₁ := fun _ => P.δ₀) hε (hβ_gt k (lt_of_le_of_ne hk hne))
        (hδ₀ _ hqm) (hdv k hk _ hqm) (hp' _ hqm)
    · rintro rfl
      refine ⟨fun j hj => ?_, fun j hj => by simp only [hδ₀ j hj]; exact hsum j hj⟩
      rw [arPass, hdv _ le_rfl j hj, hβ_eq, hδ₀ j hj]
      rcases (Finset.mem_Icc.1 hj).2.lt_or_eq with hjq | rfl
      · have h1 := slowGrad_pow_le hε.le hε2 hjq
        have h2 : ε ^ P.q / P.q ! / 2 * ε ≤ ε * ε ^ j / j ! / 2 := by
          rw [show ε * ε ^ j / j ! / 2 = ε ^ j / j ! / 2 * ε by ring]
          refine mul_le_mul_of_nonneg_right ?_ hε.le
          have : 0 ≤ ε ^ P.q / P.q ! := by positivity
          linarith
        have e : P.ς * ε * ε ^ j / j ! / 2 = P.ς * (ε * ε ^ j / j ! / 2) := by ring
        rw [e]
        exact mul_le_mul_of_nonneg_left h2 P.ς_pos.le
      · apply le_of_eq; ring
  have hnstop : ∀ k < κ, ¬ edaStopAR P (fun _ => ε) D (fun _ => P.δ₀) (fun _ => P.h₀) w k :=
    fun k hk hs' => hk.ne ((hstop k hk.le).1 hs')
  have hreach : ∀ k, (∀ j < k, ¬ edaStopAR P (fun _ => ε) D (fun _ => P.δ₀) (fun _ => P.h₀) w j) →
      k ≤ κ := fun k hk => by
    by_contra hge
    exact hk κ (not_le.1 hge) ((hstop κ le_rfl).2 rfl)
  have hstep : ∀ k < κ, ARqpDAStep univ P (fun _ => ε) X (fun _ => P.σ₀) (fun _ => P.δ₀)
      (fun _ => P.δ₀) (fun _ => P.δ₀) (fun _ => P.h₀) D w (fun _ => P.q) s (fun _ => False) ρ k :=
    fun k hk => slowGrad_arqpDAStep hε hε2 (hβ_gt k hk) (hβ_le k hk.le) hσ54 hδ₀ rfl rfl hδ₀ rfl
      (hdec k hk.le) (fun j _ => hw k j) (hmin k hk.le) (hmodel k hk.le)
      (by rw [show s k = t k • u₁ from rfl, norm_smul_u₁, abs_of_pos (lt_of_lt_of_le hε
        (hεt k hk.le))]; exact ht_lt k hk.le)
      (fun i hi => by
        rw [show s k = t k • u₁ from rfl, norm_smul_u₁, abs_of_pos (lt_of_lt_of_le hε
          (hεt k hk.le))]
        exact (hh₀ i hi).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hε.le (hεt k hk.le) _) P.κs_pos.le))
      not_false (hXs k) rfl P.σmin_le_σ₀ rfl (hρ1 k hk)
  have hrun : algorithm_13_3_2_feasible f univ P (fun _ => ε) 0 X (fun _ => P.σ₀)
      (fun _ => P.δ₀) (fun _ => P.δ₀) (fun _ => P.δ₀) (fun _ => P.h₀) D w (fun _ => P.q) s
      (fun _ => False) fx fxs (fun k => P.κs * (D k).taylorDecrement P.p (s k))
      (fun _ => True) := by
    refine ⟨hκs, fun _ _ => ⟨hε, hε1⟩, fun j hj => by rw [hδ₀ j hj], by simp [hX, hxr],
      mem_univ _, rfl, rfl, rfl, fun k _ => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · exact (jetApprox_self _ _).mono_err fun i hi => P.h₀_nonneg i hi
    · have hkκ := hreach k hk
      exact ⟨fun j hj => by simp only [hδ₀ j hj]; exact hε, fun _ _ => le_rfl,
        fun _ _ hlt => absurd hlt (lt_irrefl _), fun _ _ => ⟨0, by norm_num⟩,
        fun j hj => by simp only [hδ₀ j hj, setOf_add_mem_univ]; exact (hw k j).1⟩
    · have hkκ : k < κ := by
        rcases (hreach k fun j hj => hk j hj.le).lt_or_eq with hlt | rfl
        · exact hlt
        · exact absurd ((hstop _ le_rfl).2 rfl) (hk _ le_rfl)
      have hpos' : 0 < P.κs * (D k).taylorDecrement P.p (s k) :=
        mul_pos P.κs_pos (hdpos k hkκ.le)
      exact ⟨hstep k hkκ, fun _ => ⟨hpos', le_rfl, by simp [hfxs, hpos'.le],
        by simp [hfx, hpos'.le], fun h => absurd trivial h⟩⟩
  refine ⟨f, hb, hf, X, fun _ => P.σ₀, fun _ => P.δ₀, fun _ => P.δ₀, fun _ => P.δ₀, fun _ => P.h₀,
    D, w,
    fun _ => P.q, s, fun _ => False, fx, fxs, fun k => P.κs * (D k).taylorDecrement P.p (s k),
    fun _ => True, hrun, fun k => ⟨rfl, rfl, rfl⟩, fun Lb hLb k _ _ => ⟨fun h => h.elim,
      fun _ j hj => ?_⟩, ⟨(hstop κ le_rfl).2 rfl, hnstop⟩, ?_, ?_⟩
  · have hM : 1 ≤ max Lb P.σ₀ := hLb.trans (le_max_left _ _)
    change P.ς * P.θ * ε / (24 * max Lb P.σ₀) ≤ P.δ₀ j
    rw [hδ₀ j hj, div_le_iff₀ (by positivity)]
    have h0 : P.ς * P.θ ≤ 1 := mul_le_one_of_le_one P.ς_le_one P.θ_pos.le P.θ_lt_one.le
    have h1 : P.ς * P.θ * ε ≤ ε := mul_le_of_le_one_left hε.le h0
    have h2 : ε ≤ ε * (24 * max Lb P.σ₀) := le_mul_of_one_le_right hε.le
      (hM.trans (le_mul_of_one_le_left (zero_le_one.trans hM) (by norm_num)))
    exact h1.trans h2
  · rw [edaFunEvalCount, card_filter_range_of_forall fun _ _ => not_false,
      card_filter_range_of_forall fun _ _ => ⟨not_false, trivial⟩, Nat.cast_add]
    linarith only [hκge]
  · rw [derivEvalCount_of_forall fun i hi => Or.inr ⟨not_false, by
      rw [← hρ, hρ1 i hi]; exact P.η₁_le_η₂.trans P.η₂_lt_one.le⟩, Nat.cast_add, Nat.cast_one]
    linarith only [hκge]

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the ARqpIDA-SC row in the
lower-bound mode of the radii control for `q = p ≥ 3` (the "otherwise" order `ε^{-q(p+1)/p}`,
here `ε^{-(p+1)}`), with the (simple) feasible set `X = ℝ¹` (`univ`) and exact derivatives. There
are `f_low`, `L ≥ 1` and `ε₀ > 0` such that, for every `ε ∈ (0, ε₀]` (all `ε_j = ε`) and all
ARqpIDA constants with `q = p`, weight `σ₀ = p`, initial radii `δ₀ = ε` and initial accuracies
`0 < h_{0,i} ≤ κ_s ε^{p-i+1}`, there is `f` with f.bB and f.D0pL (all `L_{f,j} = L`) and an
ARqpIDA-SC run with exact derivatives from `x₀ = 0` satisfying the radii control in the lower-bound
mode (`Chapter13.RadiiControlOf False`), whose first iterate that is `(ε, δ)`-approximately
optimal for some radii `δ ∈ (0, 1]^q` (`Chapter13.arTest_feasible`) is `x_{k_ε}`,
`k_ε = ⌈ε^{-(p+1)}⌉`, after `k_ε + 1 ≥ ε^{-(p+1)} + 1` function and derivative evaluations. The
run follows the slow example of Theorem 12.2.15 with `q = p` (pure `p`-th order spikes
`f^{(p)}(x_k) = -(ε + ω_k)`, which fail the criterion at every radius; steps the global model
minimizers `t*_k = ε + ω_k`, `σ_k = σ₀`, `ρ_k = 1`) with Step-2 radii `δ_{s_k} = ε/p`, at which the
model measures at its minimizer vanish (`Optimization.taylorMeasure_topMonomialRegModel_eq_zero`),
and continues after `k_ε` as any ARqpIDA iteration from the state at `k_ε`
(`Chapter13.exists_arqpDA_steps`). -/
theorem theorem_14_2_4_sharp_arqpida_otherwise {p : ℕ} (hp : 3 ≤ p) :
    ∃ flow L ε₀ : ℝ, 1 ≤ L ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ P : ARqpIDAParams,
      P.p = p → P.q = p → P.σ₀ = p → (∀ j ∈ Finset.Icc 1 p, P.δ₀ j = ε) →
      (∀ i ∈ Finset.Icc 1 p, 0 < P.h₀ i ∧ P.h₀ i ≤ P.κs * ε ^ (p - i + 1)) →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, (∀ y, flow ≤ f y) ∧ AssumptionD0pL f p (fun _ => L) ∧
        ∃ (x : ℕ → EuclideanSpace ℝ (Fin 1)) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ)
          (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)
          (dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)) (jk : ℕ → ℕ)
          (s : ℕ → EuclideanSpace ℝ (Fin 1)) (acc : ℕ → Prop),
          algorithm_13_1_2_feasible f univ (fun _ => 0) P (fun _ => ε) 0 x σ δ δ₁ δs h D dd jk s
            acc ∧
          (∀ k, D k = ftaylorSeries ℝ f (x k)) ∧
          (∀ k, RadiiControlOf False P (fun _ => ε)
            (lipMax (fun _ => L) P.p + ordMax P.p (fun _ => 0) * P.κh) σ δs s acc k) ∧
          IsFirstHit (arTest_feasible f univ P (fun _ => ε) x) ⌈(ε ^ (p + 1))⁻¹⌉₊ ∧
          (ε ^ (p + 1))⁻¹ + 1 ≤ (derivEvalCount (fun i => ¬ acc i) ⌈(ε ^ (p + 1))⁻¹⌉₊ : ℝ) ∧
          (ε ^ (p + 1))⁻¹ + 1 ≤ (derivEvalCount
            (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i))
              ⌈(ε ^ (p + 1))⁻¹⌉₊ : ℝ) := by
  obtain ⟨flow, L, hL, H⟩ := exists_slowARqp_ridge (p := p) (q := p) (by omega) le_rfl
    (lam := 1) one_pos le_rfl
  refine ⟨flow, L, 1 / 4, hL, by norm_num, fun ε hε hε4 P hPp hPq hσ hδ₀ hh₀ => ?_⟩
  have hR1 : ((p - p + 1 : ℕ) : ℝ) = 1 := by simp
  have hκeq : ⌈ε ^ (-((p + 1 : ℝ) / ((p - p + 1 : ℕ) : ℝ)))⌉₊ = ⌈(ε ^ (p + 1))⁻¹⌉₊ := by
    rw [hR1, div_one, Real.rpow_neg hε.le,
      show ((p : ℝ) + 1) = ((p + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  set κ := ⌈(ε ^ (p + 1))⁻¹⌉₊ with hκ
  have hκge : (ε ^ (p + 1))⁻¹ ≤ κ := Nat.le_ceil _
  have hκ1 : 1 ≤ κ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hκpos : (0 : ℝ) < κ := by exact_mod_cast hκ1
  have hε1 : ε ≤ 1 := by linarith
  have hp1 : 1 ≤ p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp1
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  -- the levels, the steps and the points
  set a : ℕ → ℝ := fun k => 1 * (ε + ε * ((κ : ℝ) - k) / κ) with ha
  set t : ℕ → ℝ := fun k => a k ^ (1 / ((p - p + 1 : ℕ) : ℝ)) with ht
  have ht_eq : ∀ k, t k = a k := fun k => by simp only [ht, hR1, div_one, Real.rpow_one]
  set xr : ℕ → ℝ := fun k => ∑ i ∈ Finset.range k, t i with hxr
  have hxr1 : ∀ k, xr (k + 1) = xr k + t k := fun k => Finset.sum_range_succ _ _
  obtain ⟨g, hgc, hb, hf, hspike, hval⟩ := H ε hε hε1 xr fun k hk => by
    rw [hκeq] at hk; rw [hxr1, hκeq]
  rw [hκeq] at hspike hval
  have ha_ge : ∀ k ≤ κ, ε ≤ a k := fun k hk => by
    have : (0 : ℝ) ≤ ε * ((κ : ℝ) - k) / κ := by
      have : (k : ℝ) ≤ κ := by exact_mod_cast hk
      have : 0 ≤ (κ : ℝ) - k := by linarith
      positivity
    simp only [ha]; linarith
  have ha_gt : ∀ k < κ, ε < a k := fun k hk => by
    have : (0 : ℝ) < ε * ((κ : ℝ) - k) / κ := by
      have : (k : ℝ) < κ := by exact_mod_cast hk
      have : 0 < (κ : ℝ) - k := by linarith
      positivity
    simp only [ha]; linarith
  have ha_le : ∀ k ≤ κ, a k ≤ 2 * ε := fun k hk => by
    have : ε * ((κ : ℝ) - k) / κ ≤ ε := by
      rw [div_le_iff₀ hκpos]
      have : (0 : ℝ) ≤ k := k.cast_nonneg
      nlinarith
    simp only [ha]; linarith
  have ha0 : a 0 = 2 * ε := by
    simp only [ha, Nat.cast_zero, sub_zero]; rw [mul_div_assoc, div_self hκpos.ne']; ring
  have ha_eq : a κ = ε := by simp only [ha]; rw [sub_self, mul_zero, zero_div, add_zero, one_mul]
  -- the function and its Taylor data
  subst hPp
  set f : EuclideanSpace ℝ (Fin 1) → ℝ := ridge g u₁ with hfdef
  set X : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => xr k • u₁ with hX
  set s : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => t k • u₁ with hs
  have hXs : ∀ k, X (k + 1) = X k + s k := fun k => by simp only [hX, hs, hxr1, add_smul]
  have hspX : ∀ k ≤ κ, IsSpikeJetOf P.p g P.q ⟪u₁, X k⟫ (a k) := fun k hk => by
    rw [inner_smul_u₁, hPq]; exact hspike k hk
  have hgp : ContDiff ℝ P.p g := hgc
  have hqp : P.q = P.p := hPq
  have hdec : ∀ k ≤ κ, ∀ j ≤ P.q, ∀ d, (ftaylorSeries ℝ f (X k)).taylorDecrement j d =
      (if j = P.q then a k / P.q ! else 0) * ⟪u₁, d⟫ ^ P.q := fun k hk j hj d => by
    have hspXq : IsSpikeJetOf P.q g P.q ⟪u₁, X k⟫ (a k) := by rw [hqp]; rw [hqp] at hspX
                                                              exact hspX k hk
    have hgq : ContDiff ℝ P.q g := by rw [hqp]; exact hgp
    rcases hj.lt_or_eq with hjq | rfl
    · rw [ite_eq_right hjq.ne, zero_mul]
      exact taylorDecrement_ridge_of_lt hgq hjq hspXq d
    · rw [ite_eq_left rfl, taylorDecrement_ridge_spike hgq P.one_le_q le_rfl hspXq]
      ring
  have hdecp : ∀ k ≤ κ, ∀ d, (ftaylorSeries ℝ f (X k)).taylorDecrement P.p d =
      a k / P.q ! * ⟪u₁, d⟫ ^ P.q := fun k hk d => by
    rw [taylorDecrement_ridge_spike hgp P.one_le_q P.q_le_p (hspX k hk)]
    ring
  have hmeas : ∀ k ≤ κ, ∀ j ∈ Finset.Icc 1 P.q, ∀ t' : ℝ, 0 ≤ t' →
      taylorMeasure (ftaylorSeries ℝ f (X k)) j t' univ =
        (if j = P.q then a k / P.q ! else 0) * t' ^ P.q := fun k hk j hj t' ht' =>
    slowAR_measure (D := fun i => ftaylorSeries ℝ f (X i)) (by linarith [ha_ge k hk])
      (hdec k hk) (Finset.mem_Icc.1 hj).2 ht'
  have hσ₀ : 0 < P.σ₀ := P.σ₀_pos
  have hmin : ∀ k ≤ κ, IsMinOn (regularizedModel (ftaylorSeries ℝ f (X k)) P.p P.σ₀) univ
      (s k) := fun k hk => by
    obtain ⟨hm, -, -⟩ := isMinOn_neg_monomial_add_regularization P.one_le_q P.q_le_p hσ₀
      (by linarith [ha_ge k hk] : 0 < a k)
    have e : (a k / (P.σ₀ * (P.q - 1)! / P.p !)) ^ (1 / ((P.p - P.q + 1 : ℕ) : ℝ)) = t k := by
      rw [ht_eq, hqp, Nat.sub_self, zero_add, Nat.cast_one, div_one, Real.rpow_one, hσ]
      obtain ⟨n, hn⟩ : ∃ n, P.p = n + 1 := ⟨P.p - 1, by omega⟩
      rw [hn, Nat.add_sub_cancel, Nat.factorial_succ]
      push_cast
      field_simp
    rw [e] at hm
    intro y _
    simp only [mem_ofPred_eq]
    rw [regularizedModel_ridge_spike norm_eq_abs_inner_u₁ hgp P.one_le_q P.q_le_p (hspX k hk),
      ridge_apply, ridge_apply, show s k = t k • u₁ from rfl, inner_smul_u₁ (t k)]
    exact (add_le_add_iff_left _).2 (isMinOn_iff.1 hm _ (mem_univ _))
  have hmodel : ∀ k ≤ κ, ∀ ℓ ∈ Finset.Icc 1 P.q, ∀ d, ‖d‖ ≤ ε / P.p →
      (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f (X k)) P.p P.σ₀) (s k)).taylorDecrement
        ℓ d ≤ 0 := fun k hk ℓ hℓ d hd => by
    have hℓp : ℓ ≤ P.p := (Finset.mem_Icc.1 hℓ).2.trans P.q_le_p
    rw [show s k = t k • u₁ from rfl, taylorDecrement_regularizedModel_ridge_spike norm_u₁
      norm_eq_abs_inner_u₁ hgp P.one_le_q P.q_le_p (hspX k hk) hℓp, ht_eq, hσ, hqp]
    have h0 := taylorMeasure_topMonomialRegModel_eq_zero (p := P.p) (j := ℓ)
      ⟨(Finset.mem_Icc.1 hℓ).1, hℓp⟩ (a := a k) (δ := ε / P.p) (by linarith [ha_ge k hk])
      (by
        have : ((P.p : ℝ) - 1) * (ε / P.p) ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ hpR]; nlinarith
        linarith [ha_ge k hk])
    have hle := taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (negMonomialRegModel P.p P.p P.p (a k)) (a k)) ℓ
      (S := univ) (δ := ε / P.p) (d := ⟪u₁, d⟫)
      ⟨mem_closedBall_zero_iff.2 (show ‖⟪u₁, d⟫‖ ≤ ε / P.p by
        rw [Real.norm_eq_abs, ← norm_eq_abs_inner_u₁]; exact hd), mem_univ _⟩
    rw [h0] at hle
    exact hle
  have hnorm_s : ∀ k ≤ κ, ‖s k‖ = a k := fun k hk => by
    rw [show s k = t k • u₁ from rfl, norm_smul_u₁, ht_eq, abs_of_pos (by linarith [ha_ge k hk])]
  have hdecs : ∀ k ≤ κ, (ftaylorSeries ℝ f (X k)).taylorDecrement P.p (s k) =
      a k / P.q ! * t k ^ P.q := fun k hk => by rw [hdecp k hk, hs, inner_smul_u₁]
  have hfval : ∀ k < κ, f (X k) - f (X k + s k) =
      (ftaylorSeries ℝ f (X k)).taylorDecrement P.p (s k) := fun k hk => by
    rw [hdecs k hk.le, ← hXs, hfdef, ridge_apply, ridge_apply, hX, inner_smul_u₁, inner_smul_u₁,
      hval k hk, hxr1, hqp]
    ring
  have hdpos : ∀ k ≤ κ, 0 < (ftaylorSeries ℝ f (X k)).taylorDecrement P.p (s k) := fun k hk => by
    rw [hdecs k hk, ht_eq]
    have := ha_ge k hk
    have : 0 < a k := by linarith
    positivity
  -- the continuation from the state at `κ`
  have hεv : ∀ j ∈ Finset.Icc 1 P.q, (fun _ : ℕ => ε) j ∈ Set.Ioc 0 1 := fun _ _ => ⟨hε, hε1⟩
  have hεp : 0 < ε / P.p := div_pos hε hpR
  have hεp1 : ε / P.p ≤ 1 := (div_le_self hε.le (by linarith)).trans hε1
  have hεpε : ε / P.p ≤ ε := div_le_self hε.le (by linarith)
  obtain ⟨x', σ', δ', δ₁', δs', h', dd', jk', s', acc', hx'0, hσ'0, hδ'0, hh'0, -, hr, hrc'⟩ :=
    exists_arqpDA_steps (P := P) (ε := fun _ => ε)
      (fun y _ => ftaylorSeries ℝ f y) (κg := fun _ => 0) (L := fun _ => L) hf hεv
      (fun _ _ => le_rfl) (X κ) P.σmin_le_σ₀ (δ' := fun _ => ε / P.p)
      (fun _ _ => ⟨hεp, hεp1⟩) (fun i hi => ⟨(hh₀ i hi).1, P.h₀_le i hi⟩)
      fun _ _ _ => (jetApprox_self _ _).mono_err fun i _ => by simp
  -- the spliced run
  set rad : ℕ → ℝ := fun k => if k = 0 then ε else ε / P.p with hrad
  obtain ⟨Xv, hXv⟩ : ∃ Xv : ℕ → EuclideanSpace ℝ (Fin 1),
      ∀ k, Xv k = if k < κ then X k else x' (k - κ) := ⟨_, fun _ => rfl⟩
  obtain ⟨σv, hσv⟩ : ∃ σv : ℕ → ℝ, ∀ k, σv k = if k < κ then P.σ₀ else σ' (k - κ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨δv, hδv⟩ : ∃ δv : ℕ → ℕ → ℝ, ∀ k, δv k =
      if k < κ then (if k = 0 then P.δ₀ else fun _ => ε / P.p) else δ' (k - κ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨δ₁v, hδ₁v⟩ : ∃ δ₁v : ℕ → ℕ → ℝ, ∀ k, δ₁v k = if k < κ then δv k else δ₁' (k - κ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨δsv, hδsv⟩ : ∃ δsv : ℕ → ℕ → ℝ,
      ∀ k, δsv k = if k < κ then (fun _ => ε / P.p) else δs' (k - κ) := ⟨_, fun _ => rfl⟩
  obtain ⟨hv, hhv⟩ : ∃ hv : ℕ → ℕ → ℝ, ∀ k, hv k = if k < κ then P.h₀ else h' (k - κ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨ddv, hddv⟩ : ∃ ddv : ℕ → ℕ → EuclideanSpace ℝ (Fin 1),
      ∀ k, ddv k = if k < κ then (fun j => if j = P.q then rad k • u₁ else 0) else dd' (k - κ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨jkv, hjkv⟩ : ∃ jkv : ℕ → ℕ, ∀ k, jkv k = if k < κ then P.q else jk' (k - κ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨sv, hsv⟩ : ∃ sv : ℕ → EuclideanSpace ℝ (Fin 1),
      ∀ k, sv k = if k < κ then s k else s' (k - κ) := ⟨_, fun _ => rfl⟩
  obtain ⟨accv, haccv⟩ : ∃ accv : ℕ → Prop, ∀ k, accv k = if k < κ then False else acc' (k - κ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Dv, hDv⟩ : ∃ Dv : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ,
      ∀ k, Dv k = ftaylorSeries ℝ f (Xv k) := ⟨_, fun _ => rfl⟩
  have hXle : ∀ k ≤ κ, Xv k = X k := fun k hk => by
    rcases hk.lt_or_eq with hk | rfl
    · rw [hXv, ite_eq_left hk]
    · rw [hXv, ite_eq_right (lt_irrefl _), Nat.sub_self, hx'0]
  have hσle : ∀ k ≤ κ, σv k = P.σ₀ := fun k hk => by
    rcases hk.lt_or_eq with hk | rfl
    · rw [hσv, ite_eq_left hk]
    · rw [hσv, ite_eq_right (lt_irrefl _), Nat.sub_self, hσ'0]
  have hhle : ∀ k ≤ κ, hv k = P.h₀ := fun k hk => by
    rcases hk.lt_or_eq with hk | rfl
    · rw [hhv, ite_eq_left hk]
    · rw [hhv, ite_eq_right (lt_irrefl _), Nat.sub_self, hh'0]
  have hδrad : ∀ k < κ, ∀ j ∈ Finset.Icc 1 P.q, δv k j = rad k := fun k hk j hj => by
    rw [hδv, ite_eq_left hk]
    by_cases h0 : k = 0
    · simp only [h0, ite_true, hrad]; rw [← hPq] at hδ₀; exact hδ₀ j hj
    · simp only [h0, ite_false, hrad]
  have hδsucc : ∀ k < κ, δv (k + 1) = δsv k := fun k hk => by
    rw [hδsv, ite_eq_left hk]
    rcases (Nat.succ_le_of_lt hk).lt_or_eq with hk1 | hk1
    · rw [hδv, ite_eq_left hk1, ite_eq_right (Nat.succ_ne_zero k)]
    · rw [hδv, ← hk1, ite_eq_right (lt_irrefl _), Nat.sub_self, hδ'0]
  have hnacc : ∀ k < κ, ¬ accv k := fun k hk => by rw [haccv, ite_eq_left hk]; exact not_false
  have hρ1 : ∀ k < κ, arqpIDARatio f P Dv Xv sv k = 1 := fun k hk => by
    rw [arqpIDARatio, reductionRatio_def, hDv, hXle k hk.le, hsv, ite_eq_left hk, hfval k hk,
      div_self (hdpos k hk.le).ne']
  have hrad_pos : ∀ k, 0 < rad k := fun k => by
    simp only [hrad]; split_ifs <;> positivity
  have hstep : ∀ k, ARqpDAStep univ P (fun _ => ε) Xv σv δv δ₁v δsv hv Dv ddv jkv sv accv
      (arqpIDARatio f P Dv Xv sv) k := by
    intro k
    by_cases hk : k < κ
    · have hk1 : k + 1 ≤ κ := hk
      have hrk : rad k ≤ a k - ε / 4 := by
        simp only [hrad]
        split_ifs with h0
        · rw [h0, ha0]; linarith
        · have := ha_ge k hk.le
          have : ε / P.p ≤ ε / 3 := div_le_div_of_nonneg_left hε.le (by norm_num) hp3
          linarith
      refine slowTop_arqpDAStep (r := rad k) (r' := ε / P.p) (a := a k) hε
        (by linarith [ha_ge k hk.le]) (hrad_pos k) hεp hεp1 ?_ (hδrad k hk) (hδsucc k hk)
        (by rw [hδ₁v, ite_eq_left hk]) (fun j _ => by rw [hδsv, ite_eq_left hk])
        (by rw [hddv, ite_eq_left hk]) (by rw [hjkv, ite_eq_left hk])
        (fun j hj d => by rw [hDv, hXle k hk.le]; exact hdec k hk.le j hj d)
        (fun d => by rw [hDv, hXle k hk.le]; exact hdecp k hk.le d)
        (by rw [hDv, hXle k hk.le, hσle k hk.le, hsv, ite_eq_left hk]; exact hmin k hk.le)
        (fun ℓ hℓ d hd => by
          rw [hDv, hXle k hk.le, hσle k hk.le, hsv, ite_eq_left hk]
          exact hmodel k hk.le ℓ hℓ d hd)
        (by rw [hsv, ite_eq_left hk, hnorm_s k hk.le]; linarith [ha_le k hk.le])
        (fun i hi => ?_) (hnacc k hk)
        (by rw [hXle k hk.le, hXle (k + 1) hk1, hsv, ite_eq_left hk, hXs])
        (by rw [hσle k hk.le, hσle (k + 1) hk1]) (by rw [hσle k hk.le]; exact P.σmin_le_σ₀)
        (by rw [hhle k hk.le, hhle (k + 1) hk1]) (hρ1 k hk)
      · rw [hσle k hk.le, hσ, hqp]
        have hrk0 := (hrad_pos k).le
        have hf1 : ((P.p + 1)! : ℝ) = (P.p + 1) * P.p ! := by push_cast [Nat.factorial_succ]; ring
        have hpf : (0 : ℝ) < P.p ! := by positivity
        rw [pow_succ, hf1]
        have hrk' : rad k ≤ a k - P.ς * ε / 4 := by
          have := P.ς_le_one; nlinarith
        have h1 : (P.p : ℝ) / ((P.p + 1) * P.p !) * (rad k ^ P.p * rad k) =
            rad k ^ P.p / P.p ! * (P.p / (P.p + 1) * rad k) := by field_simp
        rw [h1]
        have h2 : (P.p : ℝ) / (P.p + 1) * rad k ≤ rad k := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
        calc rad k ^ P.p / P.p ! * (P.p / (P.p + 1) * rad k) ≤ rad k ^ P.p / P.p ! * rad k :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ ≤ rad k ^ P.p / P.p ! * (a k - P.ς * ε / 4) :=
              mul_le_mul_of_nonneg_left hrk' (by positivity)
          _ = (a k - P.ς * ε / 4) / P.p ! * rad k ^ P.p := by ring
      · rw [hhle k hk.le, hsv, ite_eq_left hk, hnorm_s k hk.le]
        refine (hh₀ i hi).2.trans (mul_le_mul_of_nonneg_left ?_ P.κs_pos.le)
        exact pow_le_pow_left₀ hε.le (ha_ge k hk.le) _
    · have hk' : κ ≤ k := not_lt.1 hk
      have hk1 : ¬ k + 1 < κ := by omega
      have hsub : k + 1 - κ = k - κ + 1 := by omega
      refine (hr (k - κ)).congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rw [hXv, ite_eq_right hk]
      · rw [hXv, ite_eq_right hk1, hsub]
      · rw [hσv, ite_eq_right hk]
      · rw [hσv, ite_eq_right hk1, hsub]
      · rw [hδv, ite_eq_right hk]
      · rw [hδv, ite_eq_right hk1, hsub]
      · rw [hδ₁v, ite_eq_right hk]
      · rw [hδsv, ite_eq_right hk]
      · rw [hhv, ite_eq_right hk]
      · rw [hhv, ite_eq_right hk1, hsub]
      · rw [hDv, hXv, ite_eq_right hk]
      · rw [hDv, hXv, ite_eq_right hk1, hsub]
      · rw [hddv, ite_eq_right hk]
      · rw [hjkv, ite_eq_right hk]
      · rw [hsv, ite_eq_right hk]
      · rw [haccv, ite_eq_right hk]
      · rw [arqpIDARatio, arqpIDARatio, hDv, hXv, ite_eq_right hk, hsv, ite_eq_right hk]
  have hrun' : algorithm_13_1_2_feasible f univ (fun _ => 0) P (fun _ => ε) 0 Xv σv δv δ₁v δsv
      hv Dv ddv jkv sv accv :=
    ⟨hεv, fun j hj => by rw [← hPq] at hδ₀; rw [hδ₀ j hj], fun _ _ => le_rfl,
      by rw [hXle 0 (Nat.zero_le _)]; simp [hX, hxr], mem_univ _,
      hσle 0 (Nat.zero_le _), by rw [hδv, ite_eq_left (by omega), ite_eq_left rfl],
      hhle 0 (Nat.zero_le _),
      fun k => by rw [hDv]; exact (jetApprox_self _ _).mono_err fun i _ => by simp, hstep⟩
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have hqf : (0 : ℝ) < P.q ! := by positivity
  have htest : ∀ k ≤ κ, (arTest_feasible f univ P (fun _ => ε) Xv k ↔ k = κ) := by
    intro k hk
    rw [arTest_feasible, setOf_add_mem_univ, hXle k hk]
    constructor
    · rintro ⟨δ', hδ', ht'⟩
      by_contra hne
      have h1 := ht' P.q hqm
      have hδq := (hδ' P.q hqm).1
      rw [hmeas k hk P.q hqm _ hδq.le, ite_eq_left rfl] at h1
      have h2 := ha_gt k (lt_of_le_of_ne hk hne)
      have h3 : 0 < δ' P.q ^ P.q := by positivity
      have : a k / P.q ! * δ' P.q ^ P.q > ε * δ' P.q ^ P.q / P.q ! := by
        rw [div_mul_eq_mul_div]
        exact div_lt_div_of_pos_right (by nlinarith) hqf
      linarith
    · rintro rfl
      refine ⟨fun _ => 1, fun _ _ => ⟨one_pos, le_rfl⟩, fun j hj => ?_⟩
      rw [hmeas _ hk j hj 1 zero_le_one, one_pow, mul_one, one_pow, mul_one]
      split_ifs with hjq
      · subst hjq; rw [ha_eq]
      · positivity
  refine ⟨f, hb, hf, Xv, σv, δv, δ₁v, δsv, hv, Dv, ddv, jkv, sv, accv, hrun', hDv,
    fun k hk' hs1 => ⟨fun h => h.elim, fun _ j hj => ?_⟩,
    ⟨(htest κ le_rfl).2 rfl, fun i hi ht' => hi.ne ((htest i hi.le).1 ht')⟩, ?_, ?_⟩
  · by_cases hkκ : k < κ
    · rw [hδsv, ite_eq_left hkκ, hσv, ite_eq_left hkκ, hσ]
      have hM : (P.p : ℝ) ≤ max (lipMax (fun _ => L) P.p + ordMax P.p (fun _ => 0) * P.κh) P.p :=
        le_max_right _ _
      have hM0 : (0 : ℝ) < max (lipMax (fun _ => L) P.p + ordMax P.p (fun _ => 0) * P.κh) P.p :=
        hpR.trans_le hM
      have h0 : P.ς * P.θ ≤ 1 := mul_le_one_of_le_one P.ς_le_one P.θ_pos.le P.θ_lt_one.le
      rw [div_le_div_iff₀ (by positivity) hpR]
      have h1 : P.ς * P.θ * ε ≤ ε := mul_le_of_le_one_left hε.le h0
      have h3 : (P.p : ℝ) ≤ 24 * max (lipMax (fun _ => L) P.p +
          ordMax P.p (fun _ => 0) * P.κh) P.p := hM.trans (le_mul_of_one_le_left hM0.le
            (by norm_num))
      calc P.ς * P.θ * ε * P.p ≤ ε * P.p := mul_le_mul_of_nonneg_right h1 hpR.le
        _ ≤ ε * (24 * max (lipMax (fun _ => L) P.p + ordMax P.p (fun _ => 0) * P.κh) P.p) :=
          mul_le_mul_of_nonneg_left h3 hε.le
    · rw [hδsv, ite_eq_right hkκ]
      rw [haccv, ite_eq_right hkκ] at hk'
      rw [hsv, ite_eq_right hkκ] at hs1
      rw [hσv, ite_eq_right hkκ]
      exact (hrc' (k - κ) hk' hs1).2 (by rw [hPq]; omega) j hj
  · rw [derivEvalCount_of_forall hnacc, Nat.cast_add, Nat.cast_one]; linarith only [hκge]
  · rw [derivEvalCount_of_forall fun i hi => Or.inr ⟨hnacc i hi, by
      rw [hρ1 i hi]; exact P.η₁_le_η₂.trans P.η₂_lt_one.le⟩, Nat.cast_add, Nat.cast_one]
    linarith only [hκge]

end ARqpDASharp

/-! ### Sharpness of the ARqpIDA-SC row in the lower-bound mode with a constrained feasible set

The order `ε^{-q(p+1)/p}` of the lower-bound mode of the ARqpIDA-SC row is attained for every
`1 ≤ q ≤ p` with the closed feasible set `X = {v 1 = 0} ∪ {ρ ≤ v 1}` of `ℝ²` (a line and a parallel
half-plane at distance `ρ ∈ (ε, 2ε]`), by the slow example of Theorem 12.2.17 on the line. The
half-plane makes the criterion `Chapter13.arTest_feasible` ("approximately optimal for some radii
in `(0, 1]^q`") fail at the large radii, which the line alone cannot do. -/

section ARqpIDAConstrained

open Chapter13 Optimization
open scoped RealInnerProductSpace

/-- The first unit vector of `ℝ²`. -/
private noncomputable def e₁ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1

/-- The second unit vector of `ℝ²`. -/
private noncomputable def e₂ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1

private theorem inner_e₁ (v : EuclideanSpace ℝ (Fin 2)) : ⟪e₁, v⟫ = v 0 := by
  simp [e₁, EuclideanSpace.inner_single_left]

private theorem inner_e₂ (v : EuclideanSpace ℝ (Fin 2)) : ⟪e₂, v⟫ = v 1 := by
  simp [e₂, EuclideanSpace.inner_single_left]

private theorem norm_e₁ : ‖e₁‖ = 1 := by simp [e₁]

private theorem norm_e₂ : ‖e₂‖ = 1 := by simp [e₂]

private theorem inner_e₁_smul (c : ℝ) : ⟪e₁, c • e₁⟫ = c := by
  rw [inner_e₁]; simp [e₁]

private theorem inner_e₂_smul_e₁ (c : ℝ) : ⟪e₂, c • e₁⟫ = 0 := by
  rw [inner_e₂]; simp [e₁]

private theorem inner_e₁_smul_e₂ (c : ℝ) : ⟪e₁, c • e₂⟫ = 0 := by
  rw [inner_e₁]; simp [e₂]

private theorem inner_e₂_smul (c : ℝ) : ⟪e₂, c • e₂⟫ = c := by
  rw [inner_e₂]; simp [e₂]

private theorem norm_smul_e₁ (c : ℝ) : ‖c • e₁‖ = |c| := by
  rw [norm_smul, norm_e₁, mul_one, Real.norm_eq_abs]

private theorem norm_smul_e₂ (c : ℝ) : ‖c • e₂‖ = |c| := by
  rw [norm_smul, norm_e₂, mul_one, Real.norm_eq_abs]

/-- A vector orthogonal to `e₂` is a multiple of `e₁`. -/
private theorem eq_smul_e₁ {v : EuclideanSpace ℝ (Fin 2)} (hv : ⟪e₂, v⟫ = 0) :
    v = ⟪e₁, v⟫ • e₁ := by
  rw [inner_e₂] at hv
  rw [inner_e₁]
  ext i
  fin_cases i <;> simp [e₁, hv]

private theorem abs_inner_e₁_le (v : EuclideanSpace ℝ (Fin 2)) : |⟪e₁, v⟫| ≤ ‖v‖ := by
  simpa [norm_e₁] using abs_real_inner_le_norm e₁ v

private theorem inner_e₂_le (v : EuclideanSpace ℝ (Fin 2)) : ⟪e₂, v⟫ ≤ ‖v‖ := by
  simpa [norm_e₂] using real_inner_le_norm e₂ v

section Slit

variable {p : ℕ} {G H : ℝ → ℝ} {x : EuclideanSpace ℝ (Fin 2)} {α γ : ℝ}

/-- A spike jet of order `p` restricts to a spike jet of order `j ≤ p`. -/
private theorem isSpikeJetOf_restrict {q j : ℕ} {a : ℝ} (hd : IsSpikeJetOf p G q a α) (hj : j ≤ p) :
    IsSpikeJetOf j G q a α :=
  ⟨hd.1, fun i hi1 hij hiq => hd.2 i hi1 (hij.trans hj) hiq⟩

/-- The Taylor polynomials of `G(⟪e₁, ·⟫) + H(⟪e₂, ·⟫)` at a point where `G` and `H` have gradient
spikes `-α` and `-γ`: `T_j(x, w) = G(⟪e₁, x⟫) + H(⟪e₂, x⟫) - α ⟪e₁, w⟫ - γ ⟪e₂, w⟫`
(`1 ≤ j ≤ p`). -/
private theorem taylorPolynomial_slit (hG : ContDiff ℝ p G) (hH : ContDiff ℝ p H)
    (hdG : IsSpikeJetOf p G 1 ⟪e₁, x⟫ α) (hdH : IsSpikeJetOf p H 1 ⟪e₂, x⟫ γ) {j : ℕ}
    (hj1 : 1 ≤ j) (hjp : j ≤ p) (w : EuclideanSpace ℝ (Fin 2)) :
    taylorPolynomial (ridge G e₁ + ridge H e₂) j x w =
      G ⟪e₁, x⟫ + H ⟪e₂, x⟫ - α * ⟪e₁, w⟫ - γ * ⟪e₂, w⟫ := by
  have hGj : ContDiff ℝ j G := hG.of_le (by exact_mod_cast hjp)
  have hHj : ContDiff ℝ j H := hH.of_le (by exact_mod_cast hjp)
  have hsum : taylorPolynomial (ridge G e₁ + ridge H e₂) j x w =
      taylorPolynomial (ridge G e₁) j x w + taylorPolynomial (ridge H e₂) j x w := by
    rw [taylorPolynomial_apply, taylorPolynomial_apply, taylorPolynomial_apply,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : (i : WithTop ℕ∞) ≤ j := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [iteratedFDeriv_add_apply ((contDiff_ridge hGj).contDiffAt.of_le hij)
      ((contDiff_ridge hHj).contDiffAt.of_le hij), add_apply, smul_add]
  rw [hsum, taylorPolynomial_ridge_spike hGj le_rfl hj1 (isSpikeJetOf_restrict hdG hjp),
    taylorPolynomial_ridge_spike hHj le_rfl hj1 (isSpikeJetOf_restrict hdH hjp)]
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
  ring

/-- The Taylor decrements of `G(⟪e₁, ·⟫) + H(⟪e₂, ·⟫)` at a point with gradient spikes:
`ΔT_j(x, w) = α ⟪e₁, w⟫ + γ ⟪e₂, w⟫` (`1 ≤ j ≤ p`). -/
private theorem taylorDecrement_slit (hG : ContDiff ℝ p G) (hH : ContDiff ℝ p H)
    (hdG : IsSpikeJetOf p G 1 ⟪e₁, x⟫ α) (hdH : IsSpikeJetOf p H 1 ⟪e₂, x⟫ γ) {j : ℕ}
    (hj1 : 1 ≤ j) (hjp : j ≤ p) (w : EuclideanSpace ℝ (Fin 2)) :
    (ftaylorSeries ℝ (ridge G e₁ + ridge H e₂) x).taylorDecrement j w =
      α * ⟪e₁, w⟫ + γ * ⟪e₂, w⟫ := by
  rw [ftaylorSeries_taylorDecrement_eq, taylorPolynomial_slit hG hH hdG hdH hj1 hjp,
    Pi.add_apply, ridge_apply, ridge_apply]
  ring

/-- The model (13.1.45) of `G(⟪e₁, ·⟫) + H(⟪e₂, ·⟫)` at a point with gradient spikes, on the
line `⟪e₂, w⟫ = 0`: `m(w) = G(⟪e₁, x⟫) + H(⟪e₂, x⟫) + m₁(⟪e₁, w⟫)` with the one-dimensional model
`m₁ t = -α t + σ |t|^{p+1}/(p+1)!`. -/
private theorem regularizedModel_slit_line (hp : 1 ≤ p) (hG : ContDiff ℝ p G)
    (hH : ContDiff ℝ p H) (hdG : IsSpikeJetOf p G 1 ⟪e₁, x⟫ α)
    (hdH : IsSpikeJetOf p H 1 ⟪e₂, x⟫ γ) (σ : ℝ) {w : EuclideanSpace ℝ (Fin 2)}
    (hw : ⟪e₂, w⟫ = 0) :
    regularizedModel (ftaylorSeries ℝ (ridge G e₁ + ridge H e₂) x) p σ w =
      G ⟪e₁, x⟫ + H ⟪e₂, x⟫ + negMonomialRegModel p 1 σ α ⟪e₁, w⟫ := by
  have hn : ‖w‖ = |⟪e₁, w⟫| := by rw [eq_smul_e₁ hw, inner_e₁_smul, norm_smul_e₁]
  rw [regularizedModel_def, ← taylorPolynomial_eq_taylorSum,
    taylorPolynomial_slit hG hH hdG hdH hp le_rfl, hw, hn, negMonomialRegModel]
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
  ring

/-- The Taylor decrements of the model at a point `t e₁` of the line, along a direction `d` of
the line, are those of the one-dimensional model `m₁` at `t` along `⟪e₁, d⟫` (orders `ℓ ≤ p`). -/
private theorem taylorDecrement_regularizedModel_slit (hp : 1 ≤ p) (hG : ContDiff ℝ p G)
    (hH : ContDiff ℝ p H) (hdG : IsSpikeJetOf p G 1 ⟪e₁, x⟫ α)
    (hdH : IsSpikeJetOf p H 1 ⟪e₂, x⟫ γ) (σ t : ℝ) {d : EuclideanSpace ℝ (Fin 2)}
    (hd : ⟪e₂, d⟫ = 0) {ℓ : ℕ} (hℓ : ℓ ≤ p) :
    (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ (ridge G e₁ + ridge H e₂) x) p σ)
      (t • e₁)).taylorDecrement ℓ d =
      (ftaylorSeries ℝ (negMonomialRegModel p 1 σ α) t).taylorDecrement ℓ ⟪e₁, d⟫ := by
  set C := G ⟪e₁, x⟫ + H ⟪e₂, x⟫
  have hline : ∀ τ : ℝ, regularizedModel (ftaylorSeries ℝ (ridge G e₁ + ridge H e₂) x) p σ
      (t • e₁ + τ • d) = C + negMonomialRegModel p 1 σ α (t + τ * ⟪e₁, d⟫) := fun τ => by
    have h1 : ⟪e₂, t • e₁ + τ • d⟫ = 0 := by
      rw [inner_add_right, inner_e₂_smul_e₁, inner_smul_right, hd]; ring
    rw [regularizedModel_slit_line hp hG hH hdG hdH σ h1, inner_add_right, inner_e₁_smul,
      inner_smul_right]
  rw [taylorDecrement_eq_of_line contDiff_regularizedModel
    (contDiff_const.add (contDiff_negMonomialRegModel p 1 σ α)) hline hℓ, taylorDecrement_real,
    taylorDecrement_real]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [iteratedDeriv_const_add (by have := (Finset.mem_Icc.1 hi).1; omega)]

/-- The feasible set of the slit example: the line `{⟪e₂, v⟫ = 0}` and the half-plane
`{⟪e₂, v⟫ ≥ ρ}` at distance `ρ` from it. -/
private def slitSet (ρ : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {v | ⟪e₂, v⟫ = 0} ∪ {v | ρ ≤ ⟪e₂, v⟫}

private theorem add_mem_slitSet_iff {ρ : ℝ} {x e : EuclideanSpace ℝ (Fin 2)} (hx : ⟪e₂, x⟫ = 0) :
    x + e ∈ slitSet ρ ↔ ⟪e₂, e⟫ = 0 ∨ ρ ≤ ⟪e₂, e⟫ := by
  simp only [slitSet, mem_union, mem_ofPred_eq, inner_add_right, hx, zero_add]

/-- Near a point of the line, the slit set is the line: feasible displacements shorter than `ρ`
are orthogonal to `e₂`. -/
private theorem inner_e₂_eq_zero_of_mem {ρ : ℝ} {x e : EuclideanSpace ℝ (Fin 2)}
    (hx : ⟪e₂, x⟫ = 0) (he : x + e ∈ slitSet ρ) (hρ : ‖e‖ < ρ) : ⟪e₂, e⟫ = 0 := by
  rcases (add_mem_slitSet_iff hx).1 he with h | h
  · exact h
  · exact absurd (h.trans (inner_e₂_le e)) (not_le.2 hρ)

private theorem smul_e₁_mem_slitSet {ρ : ℝ} {x : EuclideanSpace ℝ (Fin 2)} (hx : ⟪e₂, x⟫ = 0)
    (c : ℝ) : x + c • e₁ ∈ slitSet ρ :=
  (add_mem_slitSet_iff hx).2 (Or.inl (inner_e₂_smul_e₁ c))

/-- **The slow gradient interpolant with a flat endpoint** (the data of Theorem 12.2.17 with
`r = p`, followed by one more point). For `1 ≤ q ≤ p` and `σ > 0` there are `L, B ≥ 0` depending
only on `p, q, σ` such that: for every `ε ∈ (0, 1]`, with `k_ε = ⌈ε^{-q(p+1)/p}⌉₊`,
`β_k = (ε^q + ε^q (k_ε - k)/k_ε)/q!` and points `ξ_{k+1} = ξ_k + (p! β_k/σ)^{1/p}` (`k ≤ k_ε`),
there is a `C^p` function `G` with `L`-Lipschitz `p`-th derivative, `|G^{(j)}| ≤ B` (`j ≤ p`),
gradient spikes `G'(ξ_k) = -β_k` (other derivatives of orders `2, …, p` zero) for `k ≤ k_ε`, all
derivatives of orders `1, …, p` zero at `ξ_{k_ε+1}`, and `G(ξ_{k+1}) = G(ξ_k) - β_k (ξ_{k+1} - ξ_k)`
for `k ≤ k_ε`. -/
private theorem exists_slitGrad_interpolant {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) {σ : ℝ}
    (hσ : 0 < σ) :
    ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧ ∀ (ε : ℝ) (κ : ℕ) (ξ β : ℕ → ℝ), 0 < ε → ε ≤ 1 →
      κ = ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ →
      (∀ k, β k = (ε ^ q + ε ^ q * ((κ : ℝ) - k) / κ) / q !) →
      (∀ k ≤ κ, ξ (k + 1) = ξ k + (p ! * β k / σ) ^ (1 / (p : ℝ))) →
      ∃ G : ℝ → ℝ, ContDiff ℝ p G ∧
        (∀ s t, |iteratedDeriv p G s - iteratedDeriv p G t| ≤ L * |s - t|) ∧
        (∀ j ≤ p, ∀ t, |iteratedDeriv j G t| ≤ B) ∧
        (∀ k ≤ κ, IsSpikeJetOf p G 1 (ξ k) (β k)) ∧ IsSpikeJetOf p G 1 (ξ (κ + 1)) 0 ∧
        ∀ k ≤ κ, G (ξ (k + 1)) = G (ξ k) - β k * (ξ (k + 1) - ξ k) := by
  have hp1 : 1 ≤ p := hq.trans hqp
  have hp0 : p ≠ 0 := by omega
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp1
  have hqf : (0 : ℝ) < q ! := by positivity
  have hqf1 : (1 : ℝ) ≤ q ! := by exact_mod_cast Nat.factorial_pos q
  have hpf : (0 : ℝ) < p ! := by positivity
  set M : ℝ := 2 / q ! * (2 * p ! / (q ! * σ)) ^ (1 / (p : ℝ)) with hM
  have hM0 : 0 ≤ M := by positivity
  set κH : ℝ := max (3 * M) (max 2 (max ((2 * p ! / σ) ^ (1 / (p : ℝ))) (σ / p !))) with hκH
  have hκM : 3 * M ≤ κH := le_max_left _ _
  have hκ2 : 2 ≤ κH := (le_max_left _ _).trans (le_max_right _ _)
  have hκs : (2 * p ! / σ) ^ (1 / (p : ℝ)) ≤ κH :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hκσ : σ / p ! ≤ κH :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hκ0 : 0 ≤ κH := by linarith
  obtain ⟨L, B, hL, hB, hH⟩ := Hermite.exists_contDiff_interpolating_jets_bounded_of_forall_le p hκ0
  refine ⟨L, B, hL, hB, fun ε κ ξ β hε hε1 hκdef hβ hξ => ?_⟩
  set e : ℝ := (q : ℝ) * (p + 1) / p with he
  have he0 : 0 ≤ e := by positivity
  obtain ⟨hκ1, hκ2'⟩ := one_le_ceil_rpow_neg_and_mul_le hε hε1 he0
  rw [← hκdef] at hκ1 hκ2'
  have hκpos : (0 : ℝ) < κ := by exact_mod_cast hκ1
  have hεq : 0 < ε ^ q := pow_pos hε q
  have hεq1 : ε ^ q ≤ 1 := pow_le_one₀ hε.le hε1
  have hεe1 : ε ^ e ≤ 1 := Real.rpow_le_one hε.le hε1 he0
  have hqe : ε ^ q * (ε ^ q) ^ (1 / (p : ℝ)) = ε ^ e := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le, ← Real.rpow_add hε, he]
    congr 1
    field_simp
  have hβb : ∀ k ≤ κ, ε ^ q / q ! ≤ β k ∧ β k ≤ 2 * ε ^ q / q ! := fun k hk => by
    have hk' : (k : ℝ) ≤ κ := by exact_mod_cast hk
    have h0 : 0 ≤ ε ^ q * ((κ : ℝ) - k) / κ := div_nonneg (mul_nonneg hεq.le (by linarith)) hκpos.le
    have h1 : ε ^ q * ((κ : ℝ) - k) / κ ≤ ε ^ q := by
      rw [div_le_iff₀ hκpos]; nlinarith [Nat.cast_nonneg (α := ℝ) k]
    rw [hβ k]
    constructor
    · exact div_le_div_of_nonneg_right (by linarith) hqf.le
    · exact div_le_div_of_nonneg_right (by linarith) hqf.le
  have hβs : ∀ k, β k - β (k + 1) = ε ^ q / κ / q ! := fun k => by
    rw [hβ, hβ]; push_cast; field_simp; ring
  have hβpos : ∀ k ≤ κ, 0 < β k := fun k hk => lt_of_lt_of_le (by positivity) (hβb k hk).1
  set β' : ℕ → ℝ := fun k => if k ≤ κ then β k else 0 with hβ'
  set ts : ℕ → ℝ := fun k => (p ! * β k / σ) ^ (1 / (p : ℝ)) with hts
  have hgap : ∀ k ≤ κ, ξ (k + 1) - ξ k = ts k := fun k hk => by rw [hξ k hk]; ring
  have hspos : ∀ k ≤ κ, 0 < ts k := fun k hk => by
    have := hβpos k hk
    exact Real.rpow_pos_of_pos (by positivity) _
  have htsp : ∀ k ≤ κ, ts k ^ p = p ! * β k / σ := fun k hk => by
    have := hβpos k hk
    simp only [hts]
    rw [one_div, Real.rpow_inv_natCast_pow (by positivity) hp0]
  have hsle : ∀ k ≤ κ, ts k ≤ (2 * p ! / σ) ^ (1 / (p : ℝ)) := fun k hk => by
    have hb := (hβb k hk).2
    have := hβpos k hk
    refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    have : β k ≤ 2 := hb.trans (by rw [div_le_iff₀ hqf]; nlinarith)
    exact div_le_div_of_nonneg_right (by nlinarith) hσ.le
  set fv : ℕ → ℝ := fun k => -∑ i ∈ Finset.range k, β' i * ts i with hfv
  set dv : ℕ → ℝ := fun k => -β' k with hdv
  have hfs : ∀ k, fv (k + 1) = fv k - β' k * ts k := fun k => by
    simp only [fv, Finset.sum_range_succ]; ring
  have hdec : ∀ i < κ + 1, 0 ≤ β' i * ts i ∧ β' i * ts i ≤ M * ε ^ e := fun i hi => by
    have hi' : i ≤ κ := by omega
    obtain ⟨hb1, hb2⟩ := hβb i hi'
    have hβ0 := hβpos i hi'
    have hs0 := (hspos i hi').le
    simp only [β', ite_eq_left hi']
    refine ⟨by positivity, ?_⟩
    have hsb : ts i ≤ (2 * p ! / (q ! * σ)) ^ (1 / (p : ℝ)) * (ε ^ q) ^ (1 / (p : ℝ)) := by
      rw [← Real.mul_rpow (by positivity) hεq.le]
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      calc p ! * β i / σ ≤ p ! * (2 * ε ^ q / q !) / σ := by gcongr
        _ = 2 * p ! / (q ! * σ) * ε ^ q := by field_simp
    calc β i * ts i ≤ 2 * ε ^ q / q ! *
          ((2 * p ! / (q ! * σ)) ^ (1 / (p : ℝ)) * (ε ^ q) ^ (1 / (p : ℝ))) :=
          mul_le_mul hb2 hsb hs0 (by positivity)
      _ = M * (ε ^ q * (ε ^ q) ^ (1 / (p : ℝ))) := by rw [hM]; ring
      _ = M * ε ^ e := by rw [hqe]
  have hfb : ∀ k ≤ κ + 1, |fv k| ≤ 3 * M := fun k hk => by
    simp only [fv, abs_neg]
    refine abs_sum_range_le_of_le hdec ?_ hk
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hεe1 hM0, mul_le_mul_of_nonneg_left hκ2' hM0]
  have hβ'2 : ∀ k, |β' k| ≤ 2 := fun k => by
    simp only [β']
    split_ifs with hk
    · rw [abs_of_pos (hβpos k hk)]
      exact (hβb k hk).2.trans (by rw [div_le_iff₀ hqf]; nlinarith)
    · simp
  obtain ⟨G, hGc, hGL, hGB, hGj, -, -⟩ := hH (κ + 1) ξ (spikeJet fv dv 1)
    (fun k hk => by rw [← sub_pos, hgap k (by omega)]; exact hspos k (by omega))
    (fun k hk => by rw [hgap k (by omega)]; exact (hsle k (by omega)).trans hκs)
    (fun k hk j _ => by
      unfold spikeJet
      split_ifs
      · exact (hfb k hk).trans hκM
      · simp only [dv, abs_neg]; linarith [hβ'2 k]
      · simpa using hκ0)
    (fun k hk => by
      have hk' : k ≤ κ := by omega
      rw [hgap k hk']
      have hs0 := (hspos k hk').le
      refine hermite_consistency_spike le_rfl hp1 hs0 hκ0 ?_
        (fun h => absurd h (lt_irrefl 1)) ?_
      · rw [hfs]
        simp only [dv]
        have : fv k - β' k * ts k - (fv k + -β' k * ts k ^ 1 / (Nat.factorial 1 : ℝ)) = 0 := by
          simp; ring
        rw [this, abs_zero]
        positivity
      · rw [Nat.sub_add_cancel hp1, htsp k hk']
        have hb : |dv (k + 1) - dv k| ≤ β k := by
          simp only [dv, β', ite_eq_left hk']
          rcases hk'.lt_or_eq with hlt | rfl
          · rw [ite_eq_left (show k + 1 ≤ κ by omega),
              show -β (k + 1) - -β k = β k - β (k + 1) by ring,
              hβs, abs_of_nonneg (by positivity)]
            calc ε ^ q / κ / q ! ≤ ε ^ q / q ! := by
                  gcongr; exact div_le_self hεq.le (by exact_mod_cast hκ1)
              _ ≤ β k := (hβb k hk').1
          · rw [ite_eq_right (by omega), neg_zero, zero_sub, neg_neg, abs_of_pos (hβpos _ le_rfl)]
        refine hb.trans ?_
        have := hβpos k hk'
        calc β k = σ / p ! * (p ! * β k / σ) := by field_simp
          _ ≤ κH * (p ! * β k / σ) := mul_le_mul_of_nonneg_right hκσ (by positivity))
  refine ⟨G, hGc, hGL, hGB, fun k hk => ⟨?_, fun j hj1 hjp hj => ?_⟩, ⟨?_, fun j hj1 hjp hj => ?_⟩,
    fun k hk => ?_⟩
  · obtain ⟨-, h1, -⟩ := iteratedDeriv_eq_of_spikeJet one_ne_zero hp1 hGj (k := k) (by omega)
    rw [h1]; simp only [dv, β', ite_eq_left hk]
  · obtain ⟨-, -, h2⟩ := iteratedDeriv_eq_of_spikeJet one_ne_zero hp1 hGj (k := k) (by omega)
    exact h2 j hj1 hjp hj
  · obtain ⟨-, h1, -⟩ := iteratedDeriv_eq_of_spikeJet one_ne_zero hp1 hGj (k := κ + 1) le_rfl
    rw [h1]; simp only [dv, β', ite_eq_right (show ¬ κ + 1 ≤ κ by omega), neg_zero]
  · obtain ⟨-, -, h2⟩ := iteratedDeriv_eq_of_spikeJet one_ne_zero hp1 hGj (k := κ + 1) le_rfl
    exact h2 j hj1 hjp hj
  · obtain ⟨h0, -, -⟩ := iteratedDeriv_eq_of_spikeJet one_ne_zero hp1 hGj (k := k) (by omega)
    obtain ⟨h0', -, -⟩ := iteratedDeriv_eq_of_spikeJet one_ne_zero hp1 hGj (k := k + 1) (by omega)
    rw [h0, h0', hfs, hgap k hk]
    simp only [β', ite_eq_left hk]

/-- **The wall of the slit example**: a `C^p` function `H` with Lipschitz `p`-th derivative and
bounded derivatives (constants depending only on `p`) with `H'(0) = -1` and `H^{(j)}(0) = 0` for
`2 ≤ j ≤ p`. -/
private theorem exists_slitWall (p : ℕ) (hp : 1 ≤ p) :
    ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧ ∃ H : ℝ → ℝ, ContDiff ℝ p H ∧
      (∀ s t, |iteratedDeriv p H s - iteratedDeriv p H t| ≤ L * |s - t|) ∧
      (∀ j ≤ p, ∀ t, |iteratedDeriv j H t| ≤ B) ∧ IsSpikeJetOf p H 1 0 1 := by
  obtain ⟨L, B, hL, hB, hH⟩ :=
    Hermite.exists_contDiff_interpolating_jets_bounded_of_forall_le p zero_le_one
  set fv : ℕ → ℝ := fun k => -(k : ℝ)
  set dv : ℕ → ℝ := fun k => if k = 0 then -1 else 0
  obtain ⟨H, hHc, hHL, hHB, hHj, -, -⟩ := hH 1 (fun k => (k : ℝ)) (spikeJet fv dv 1)
    (fun k hk => by push_cast; linarith) (fun k hk => by push_cast; linarith)
    (fun k hk j _ => by
      interval_cases k <;> (unfold spikeJet; split_ifs <;> simp [fv, dv]))
    (fun k hk => by
      obtain rfl : k = 0 := by omega
      refine hermite_consistency_spike le_rfl hp (by norm_num) zero_le_one ?_
        (fun h => absurd h (lt_irrefl 1)) ?_
      · simp [fv, dv]
      · simp [dv])
  obtain ⟨-, h1, h2⟩ := iteratedDeriv_eq_of_spikeJet (x := fun k => (k : ℝ)) one_ne_zero hp hHj
    (k := 0) (Nat.zero_le 1)
  refine ⟨L, B, hL, hB, H, hHc, hHL, hHB, ?_, fun j hj1 hjp hj => ?_⟩
  · simpa [dv] using h1
  · simpa using h2 j hj1 hjp hj

section SlitMeasure

variable {D : FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 2)) ℝ} {j : ℕ} {β ρ δ : ℝ}
  {x : EuclideanSpace ℝ (Fin 2)}

/-- On radii `δ < ρ` the measure of the decrement `β ⟪e₁, d⟫ + ⟪e₂, d⟫` (`β ≥ 0`) at a point of
the line is `β δ`. -/
private theorem slit_measure_lt (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hδρ : δ < ρ) (hx : ⟪e₂, x⟫ = 0)
    (hdec : ∀ d, D.taylorDecrement j d = β * ⟪e₁, d⟫ + ⟪e₂, d⟫) :
    taylorMeasure D j δ {e | x + e ∈ slitSet ρ} = β * δ := by
  refine le_antisymm (decrementMeasure_le ⟨0, mem_closedBall_self hδ, by
    simpa using smul_e₁_mem_slitSet (ρ := ρ) hx 0⟩ fun d hd => ?_) ?_
  · have hdn : ‖d‖ ≤ δ := mem_closedBall_zero_iff.1 hd.1
    rw [hdec, inner_e₂_eq_zero_of_mem hx hd.2 (hdn.trans_lt hδρ), add_zero]
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans ((abs_inner_e₁_le d).trans hdn)) hβ
  · have := taylorDecrement_le_taylorMeasure D j (S := {e | x + e ∈ slitSet ρ}) (δ := δ)
      (d := δ • e₁) ⟨by rw [mem_closedBall_zero_iff, norm_smul_e₁, abs_of_nonneg hδ],
        smul_e₁_mem_slitSet hx δ⟩
    rwa [hdec, inner_e₁_smul, inner_e₂_smul_e₁, add_zero] at this

/-- On radii `δ ≥ ρ ≥ 0` the half-plane is reached: the measure of the decrement
`β ⟪e₁, d⟫ + ⟪e₂, d⟫` at a point of the line is at least `ρ`. -/
private theorem slit_measure_ge (hρ : 0 ≤ ρ) (hρδ : ρ ≤ δ) (hx : ⟪e₂, x⟫ = 0)
    (hdec : ∀ d, D.taylorDecrement j d = β * ⟪e₁, d⟫ + ⟪e₂, d⟫) :
    ρ ≤ taylorMeasure D j δ {e | x + e ∈ slitSet ρ} := by
  have := taylorDecrement_le_taylorMeasure D j (S := {e | x + e ∈ slitSet ρ}) (δ := δ)
    (d := ρ • e₂) ⟨by rw [mem_closedBall_zero_iff, norm_smul_e₂, abs_of_nonneg hρ]; exact hρδ,
      (add_mem_slitSet_iff hx).2 (Or.inr (by rw [inner_e₂_smul]))⟩
  rwa [hdec, inner_e₁_smul_e₂, inner_e₂_smul, mul_zero, zero_add] at this

end SlitMeasure

section SlitTest

variable {D : FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 2)) ℝ} {q : ℕ} {ε β ρ c : ℝ}
  {x : EuclideanSpace ℝ (Fin 2)}

/-- **The slit example fails the criterion at every radius** when `q ≥ 1`, `c > 0`, the radius
of the half-plane is `ρ = ε (1 + c)^{1/n}` with `n = max(q - 1, 1)` and the gradient is
`β ≥ ε^q (1 + c)/q!`: on radii `δ < ρ` the measure of order `q` is `β δ > ε δ^q/q!`, and on radii
`δ ≥ ρ` it is at least `ρ > ε`. -/
private theorem slit_not_approx (hε : 0 < ε) (hερ : ε < ρ)
    (hρpow : ρ ^ max (q - 1) 1 = ε ^ max (q - 1) 1 * (1 + c)) (hc : 0 < c) (hβ0 : 0 ≤ β)
    (hβ : ε ^ q * (1 + c) / q ! ≤ β) (hx : ⟪e₂, x⟫ = 0) (hq : 1 ≤ q)
    (hdec : ∀ j ∈ Finset.Icc 1 q, ∀ d, D.taylorDecrement j d = β * ⟪e₁, d⟫ + ⟪e₂, d⟫)
    (δ' : ℕ → ℝ) (hδ' : ∀ j ∈ Finset.Icc 1 q, δ' j ∈ Set.Ioc 0 1)
    (ht : IsEpsDeltaApprox D {e | x + e ∈ slitSet ρ} q (fun _ => ε) δ') : False := by
  have hqm : q ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨by omega, le_rfl⟩
  have h1 := ht q hqm
  obtain ⟨hδ0, hδ1⟩ := hδ' q hqm
  have hqf : (0 : ℝ) < q ! := by positivity
  set δq := δ' q
  rcases lt_or_ge δq ρ with hδρ | hδρ
  · rw [slit_measure_lt hβ0 hδ0.le hδρ hx (hdec q hqm)] at h1
    rcases hq.eq_or_lt with rfl | hq2
    · have h2 : ε ^ 1 * (1 + c) / (1 : ℕ)! * δq ≤ ε * δq ^ 1 / (1 : ℕ)! :=
        (mul_le_mul_of_nonneg_right hβ hδ0.le).trans h1
      simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h2
      nlinarith [mul_pos (mul_pos hε hδ0) hc]
    have hq0 : q - 1 ≠ 0 := by omega
    have hmax : max (q - 1) 1 = q - 1 := max_eq_left (by omega)
    rw [hmax] at hρpow
    have hqq : q = (q - 1) + 1 := by omega
    have e1 : ε ^ q = ε ^ (q - 1) * ε := by rw [← pow_succ, ← hqq]
    have e2 : δq ^ q = δq ^ (q - 1) * δq := by rw [← pow_succ, ← hqq]
    have h2 : ε ^ q * (1 + c) / q ! * δq ≤ ε * δq ^ q / q ! :=
      (mul_le_mul_of_nonneg_right hβ hδ0.le).trans h1
    have h3 : ε ^ (q - 1) * (1 + c) * (ε * δq) ≤ δq ^ (q - 1) * (ε * δq) := by
      rw [e1, e2] at h2
      calc ε ^ (q - 1) * (1 + c) * (ε * δq) =
            ε ^ (q - 1) * ε * (1 + c) / q ! * δq * q ! := by field_simp
        _ ≤ ε * (δq ^ (q - 1) * δq) / q ! * q ! := mul_le_mul_of_nonneg_right h2 hqf.le
        _ = δq ^ (q - 1) * (ε * δq) := by field_simp
    have h4 := le_of_mul_le_mul_right h3 (mul_pos hε hδ0)
    rw [← hρpow] at h4
    exact absurd h4 (not_le.2 (pow_lt_pow_left₀ hδρ hδ0.le hq0))
  · have h2 := slit_measure_ge (hε.trans hερ).le hδρ hx (hdec q hqm)
    have h3 : ε * δq ^ q / q ! ≤ ε := by
      have hδq : δq ^ q ≤ 1 := pow_le_one₀ hδ0.le hδ1
      have : (1 : ℝ) ≤ q ! := by exact_mod_cast Nat.factorial_pos _
      calc ε * δq ^ q / q ! ≤ ε * δq ^ q := div_le_self (by positivity) this
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hδq hε.le
        _ = ε := mul_one ε
    exact absurd (h2.trans (h1.trans h3)) (not_le.2 hερ)

/-- **The slit example meets the criterion with radii `ε`** when `ε < ρ` and the gradient is
`β ≤ ε^q/q!`: the measures at radius `ε` are `β ε ≤ ε ε^j/j!`. -/
private theorem slit_approx (hε : 0 < ε) (hε1 : ε ≤ 1) (hερ : ε < ρ) (hβ0 : 0 ≤ β)
    (hβ : β ≤ ε ^ q / q !) (hx : ⟪e₂, x⟫ = 0)
    (hdec : ∀ j ∈ Finset.Icc 1 q, ∀ d, D.taylorDecrement j d = β * ⟪e₁, d⟫ + ⟪e₂, d⟫) :
    IsEpsDeltaApprox D {e | x + e ∈ slitSet ρ} q (fun _ => ε) (fun _ => ε) := by
  intro j hj
  rw [slit_measure_lt hβ0 hε.le hερ hx (hdec j hj)]
  have hj := Finset.mem_Icc.1 hj
  have h1 : ε ^ q ≤ ε ^ j := pow_le_pow_of_le_one hε.le hε1 hj.2
  have h2 : (j ! : ℝ) ≤ q ! := by exact_mod_cast Nat.factorial_le hj.2
  have h3 : ε ^ q / q ! ≤ ε ^ j / j ! := div_le_div₀ (by positivity) h1 (by positivity) h2
  calc β * ε ≤ ε ^ j / j ! * ε := mul_le_mul_of_nonneg_right (hβ.trans h3) hε.le
    _ = ε * ε ^ j / j ! := by ring

end SlitTest

section SlitStep

variable {P : ARqpIDAParams} {ε β ρ t : ℝ} {x : ℕ → EuclideanSpace ℝ (Fin 2)} {σ : ℕ → ℝ}
  {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ}
  {D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 2)) ℝ}
  {dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 2)} {jk : ℕ → ℕ} {s : ℕ → EuclideanSpace ℝ (Fin 2)}
  {acc : ℕ → Prop} {ρr : ℕ → ℝ} {k : ℕ}

/-- `ε^q/q! ≤ ε^j/(4 j!)` for `j < q` and `0 ≤ ε ≤ 1/4`. -/
private theorem slit_pow_le {j q : ℕ} (hε : 0 ≤ ε) (hε4 : ε ≤ 1 / 4) (hjq : j < q) :
    ε ^ q / q ! ≤ ε ^ j / j ! / 4 := by
  have h1 : ε ^ q ≤ ε ^ j / 4 := by
    have e : ε ^ q = ε ^ j * ε ^ (q - j) := by rw [← pow_add]; congr 1; omega
    have h2 : ε ^ (q - j) ≤ ε := pow_le_of_le_one hε (by linarith) (by omega)
    rw [e]
    have := pow_nonneg hε j
    nlinarith
  have hjf : (j ! : ℝ) ≤ q ! := by exact_mod_cast Nat.factorial_le hjq.le
  have hj0 : (0 : ℝ) < j ! := by positivity
  calc ε ^ q / q ! ≤ ε ^ j / 4 / q ! := div_le_div_of_nonneg_right h1 (by positivity)
    _ ≤ ε ^ j / 4 / j ! := div_le_div_of_nonneg_left (by positivity) hj0 hjf
    _ = ε ^ j / j ! / 4 := by ring

/-- **One trial iteration of the slit example is an ARqpIDA-SC step** on `X = slitSet ρ`
(tolerances `ε_j = ε ≤ 1/4`, `ε < ρ`): at a point of the line with Taylor decrements
`β ⟪e₁, d⟫ + ⟪e₂, d⟫` at all orders `1, …, p`, `ε^q/q! < β ≤ 2 ε^q/q!`, radii
`δ_k = δ^{(1)}_k = δ_{s_k} = ε` (no halving), Step-1 displacements `ς ε e₁` (the fraction `ς` of
the measures `β ε`), a weight with `σ_k/(p+1)! ≤ 1/(2 q!)`, a short step `s_k = t e₁` minimizing
the model on the line, whose model decrements of orders `1, …, q` along the line are nonpositive
on the ball of radius `ε`, accuracies passing (13.1.46), and the ratio `ρ_k = 1`. -/
private theorem slit_arqpDAStep (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (hερ : ε < ρ)
    (hβ : ε ^ P.q / P.q ! ≤ β) (hβ1 : β ≤ 2 * ε ^ P.q / P.q !)
    (hσ54 : σ k / ((P.p + 1)! : ℝ) ≤ 1 / (2 * P.q !)) (hx : ⟪e₂, x k⟫ = 0)
    (hδ : ∀ j ∈ Finset.Icc 1 P.q, δ k j = ε) (hδ1 : δ (k + 1) = δs k) (hδ₁ : δ₁ k = δ k)
    (hδs : ∀ j ∈ Finset.Icc 1 P.q, δs k j = ε) (hdd : ∀ j, dd k j = (P.ς * ε) • e₁)
    (hjk : jk k = P.q)
    (hdec : ∀ j ∈ Finset.Icc 1 P.p, ∀ d, (D k).taylorDecrement j d = β * ⟪e₁, d⟫ + ⟪e₂, d⟫)
    (hs : s k = t • e₁)
    (hmin : ∀ c : ℝ, regularizedModel (D k) P.p (σ k) (s k) ≤
      regularizedModel (D k) P.p (σ k) (c • e₁))
    (hmodel : ∀ ℓ ∈ Finset.Icc 1 P.q, ∀ d, ‖d‖ ≤ ε → ⟪e₂, d⟫ = 0 →
      (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ d ≤ 0)
    (hs1 : ‖s k‖ < 1) (hhk : ∀ i ∈ Finset.Icc 1 P.p, h k i ≤ P.κs * ‖s k‖ ^ (P.p - i + 1))
    (hacc : ¬ acc k) (hx1 : x (k + 1) = x k + s k) (hσ1 : σ (k + 1) = σ k)
    (hσk : P.σmin ≤ σ k) (hh1 : h (k + 1) = h k) (hρ : ρr k = 1) :
    ARqpDAStep (slitSet ρ) P (fun _ => ε) x σ δ δ₁ δs h D dd jk s acc ρr k := by
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  have hqf : (0 : ℝ) < P.q ! := by positivity
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have hσ0 : 0 ≤ σ k := P.σmin_pos.le.trans hσk
  have hη : P.η₁ ≤ 1 := P.η₁_le_η₂.trans P.η₂_lt_one.le
  have hdv : ∀ j ∈ Finset.Icc 1 P.q, (D k).taylorDecrement j (dd k j) = P.ς * (β * ε) :=
    fun j hj => by
      rw [hdd, hdec j (P.Icc_q_subset hj), inner_e₁_smul, inner_e₂_smul_e₁]; ring
  have hfail : ¬ arPass P (fun _ => ε) D δ₁ dd k P.q := by
    rw [arPass, hdv _ hqm, hδ₁, hδ _ hqm, not_le]
    have : ε * ε ^ P.q / P.q ! / 2 < β * ε := by
      rw [show ε * ε ^ P.q / P.q ! / 2 = ε ^ P.q / P.q ! / 2 * ε by ring]
      exact mul_lt_mul_of_pos_right (by linarith [div_pos (pow_pos hε P.q) hqf]) hε
    rw [show P.ς * ε * ε ^ P.q / P.q ! / 2 = P.ς * (ε * ε ^ P.q / P.q ! / 2) by ring]
    exact mul_lt_mul_of_pos_left this hς
  have hpass_lt : ∀ j ∈ Finset.Icc 1 P.q, j < P.q → arPass P (fun _ => ε) D δ₁ dd k j := by
    intro j hj hlt
    rw [arPass, hdv j hj, hδ₁, hδ j hj]
    have h1 := slit_pow_le hε.le hε4 hlt
    have h2 : β * ε ≤ ε * ε ^ j / j ! / 2 := by
      rw [show ε * ε ^ j / j ! / 2 = ε ^ j / j ! / 2 * ε by ring]
      have e : 2 * ε ^ P.q / P.q ! = 2 * (ε ^ P.q / P.q !) := by ring
      exact mul_le_mul_of_nonneg_right (by linarith) hε.le
    rw [show P.ς * ε * ε ^ j / j ! / 2 = P.ς * (ε * ε ^ j / j ! / 2) by ring]
    exact mul_le_mul_of_nonneg_left h2 hς.le
  have hxs : ⟪e₂, x k + s k⟫ = 0 := by rw [inner_add_right, hx, hs, inner_e₂_smul_e₁, add_zero]
  refine ⟨⟨fun j hj => by rw [hδ₁, hδ j hj]; exact hε, fun j _ => by rw [hδ₁],
    fun j _ hlt => by rw [hδ₁] at hlt; exact absurd hlt (lt_irrefl _),
    fun j _ => ⟨0, by rw [hδ₁]; norm_num⟩, fun j hj => ?_⟩,
    fun hp => absurd (hp _ hqm) hfail, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => hh1,
    fun _ hr' => absurd hr' (by rw [hρ]; exact not_lt.2 hη), fun ha' => absurd ha' hacc,
    fun ha' => absurd ha' hacc, fun ha' => absurd ha' hacc, fun ha' => absurd ha' hacc⟩
  · -- the Step-1 displacements
    rw [hδ₁, hδ j hj]
    have hn : dd k j ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) ε := by
      rw [hdd, mem_closedBall_zero_iff, norm_smul_e₁, abs_of_pos (by positivity)]
      nlinarith
    refine ⟨⟨hn, by rw [hdd]; exact smul_e₁_mem_slitSet hx _⟩, ?_⟩
    rw [hdv j hj]
    change P.ς * taylorMeasure (D k) j ε _ ≤ _
    rw [slit_measure_lt hβ0.le hε.le hερ hx (hdec j (P.Icc_q_subset hj))]
  · -- Step 2
    refine ⟨by rw [hjk]; exact hqm, by rw [hjk]; exact hfail,
      fun j hj hlt => hpass_lt j hj (by rw [hjk] at hlt; exact hlt),
      fun j hj hlt => absurd (Finset.mem_Icc.1 hj).2 (by rw [hjk] at hlt; omega), ?_,
      Or.inl hxs, ?_, Or.inr fun ℓ hℓ => ?_, iff_of_false hacc ?_⟩
    · -- (13.1.54)
      rw [hjk, hδ₁, hδ _ hqm, arModelDec_eq, hdec _ (Finset.mem_Icc.2 ⟨P.one_le_p, le_rfl⟩),
        hdd, inner_e₁_smul, inner_e₂_smul_e₁, norm_smul_e₁, abs_of_pos (by positivity)]
      have hpow : (P.ς * ε) ^ (P.p + 1) ≤ P.ς * ε ^ (P.q + 1) := by
        rw [mul_pow]
        exact mul_le_mul (pow_le_of_le_one hς.le hς1 (by omega))
          (pow_le_pow_of_le_one hε.le (by linarith) (by have := P.q_le_p; omega))
          (by positivity) hς.le
      have h3 : σ k / ((P.p + 1)! : ℝ) * (P.ς * ε) ^ (P.p + 1) ≤
          1 / (2 * P.q !) * (P.ς * ε ^ (P.q + 1)) :=
        mul_le_mul hσ54 hpow (by positivity) (by positivity)
      have h2 : P.ς * (ε ^ P.q / P.q ! * ε) ≤ P.ς * (β * ε) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hβ hε.le) hς.le
      have e1 : P.ς * ε * ε ^ P.q / P.q ! / 4 = 1 / (4 * P.q !) * (P.ς * ε ^ (P.q + 1)) := by
        rw [pow_succ]; field_simp
      have e2 : P.ς * (ε ^ P.q / P.q ! * ε) = 4 * (1 / (4 * P.q !) * (P.ς * ε ^ (P.q + 1))) := by
        rw [pow_succ]; field_simp
      have e3 : 1 / (2 * P.q !) * (P.ς * ε ^ (P.q + 1)) =
          2 * (1 / (4 * P.q !) * (P.ς * ε ^ (P.q + 1))) := by field_simp; ring
      have : 0 ≤ 1 / (4 * P.q !) * (P.ς * ε ^ (P.q + 1)) := by positivity
      have h4 : P.ς * (β * ε) - σ k / ((P.p + 1)! : ℝ) * (P.ς * ε) ^ (P.p + 1) =
          β * (P.ς * ε) + 0 - σ k / ((P.p + 1)! : ℝ) * (P.ς * ε) ^ (P.p + 1) := by ring
      linarith
    · simp only [arModelDec]
      have := hmin (P.ς * ε)
      rw [hdd]
      linarith
    · have hℓ' : ∀ d ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) ε ∩
          {e | x k + s k + e ∈ slitSet ρ},
          (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ d ≤ 0 :=
        fun d hd => hmodel ℓ hℓ d (mem_closedBall_zero_iff.1 hd.1)
          (inner_e₂_eq_zero_of_mem hxs hd.2 ((mem_closedBall_zero_iff.1 hd.1).trans_lt hερ))
      rw [hδs ℓ hℓ]
      have h0 : (0 : EuclideanSpace ℝ (Fin 2)) ∈ closedBall 0 ε ∩
          {e | x k + s k + e ∈ slitSet ρ} :=
        ⟨mem_closedBall_self hε.le, by simpa using smul_e₁_mem_slitSet (ρ := ρ) hxs 0⟩
      refine ⟨⟨hε, by linarith⟩, 0, ⟨h0, ?_⟩, ?_⟩
      · rw [FormalMultilinearSeries.taylorDecrement_zero_right]
        exact mul_nonpos_of_nonneg_of_nonpos hς.le (decrementMeasure_le ⟨0, h0⟩ hℓ')
      · rw [FormalMultilinearSeries.taylorDecrement_zero_right]
        have := P.θ_pos
        positivity
    · rintro ⟨-, i, hi, hlt⟩
      linarith [hhk i hi]
  · rw [hρ, hx1, hσ1]
    exact arAcceptance_of_one_le P.toARParams le_rfl _ _ hσk hσ0
  · rw [hδ1, hρ, ite_eq_left ⟨hη, hs1⟩]

/-- **An accuracy-improving iteration at a flat point of the line** (the continuation of the slit
example): at a point of the line where the Taylor decrements are `⟪e₂, d⟫` at all orders
`1, …, p`, with radii `δ_k = δ^{(1)}_k = ε < ρ` and zero Step-1 displacements, the test (13.1.53)
holds at every order, and Step 5 keeps the iterate, the weight and the radii and multiplies the
accuracies by `γ_h`. -/
private theorem slit_acc_step (hε : 0 < ε) (hερ : ε < ρ) (hx : ⟪e₂, x k⟫ = 0)
    (hδ : ∀ j ∈ Finset.Icc 1 P.q, δ k j = ε) (hδ₁ : δ₁ k = δ k) (hdd : ∀ j, dd k j = 0)
    (hdec : ∀ j ∈ Finset.Icc 1 P.p, ∀ d, (D k).taylorDecrement j d = ⟪e₂, d⟫)
    (hacc : acc k) (hx1 : x (k + 1) = x k) (hδ1 : δ (k + 1) = δ k) (hσ1 : σ (k + 1) = σ k)
    (hh1 : ∀ i, h (k + 1) i = P.γh * h k i) :
    ARqpDAStep (slitSet ρ) P (fun _ => ε) x σ δ δ₁ δs h D dd jk s acc ρr k := by
  have hς := P.ς_pos
  have hpass : ∀ j ∈ Finset.Icc 1 P.q, arPass P (fun _ => ε) D δ₁ dd k j := fun j hj => by
    rw [arPass, hdd, FormalMultilinearSeries.taylorDecrement_zero_right, hδ₁, hδ j hj]
    positivity
  refine ⟨⟨fun j hj => by rw [hδ₁, hδ j hj]; exact hε, fun j _ => by rw [hδ₁],
    fun j _ hlt => by rw [hδ₁] at hlt; exact absurd hlt (lt_irrefl _),
    fun j _ => ⟨0, by rw [hδ₁]; norm_num⟩, fun j hj => ?_⟩,
    fun _ => hacc, fun ⟨j, hj, hj'⟩ => absurd (hpass j hj) hj', fun h' => absurd hacc h',
    fun h' => absurd hacc h', fun h' => absurd hacc h', fun h' => absurd hacc h',
    fun _ => hx1, fun _ => hδ1, fun _ => hσ1, fun _ => hh1⟩
  rw [hδ₁, hδ j hj, hdd]
  have h0 : (0 : EuclideanSpace ℝ (Fin 2)) ∈ closedBall 0 ε ∩ {e | x k + e ∈ slitSet ρ} :=
    ⟨mem_closedBall_self hε.le, by simpa using smul_e₁_mem_slitSet (ρ := ρ) hx 0⟩
  refine ⟨h0, ?_⟩
  rw [FormalMultilinearSeries.taylorDecrement_zero_right]
  refine mul_nonpos_of_nonneg_of_nonpos hς.le (decrementMeasure_le ⟨0, h0⟩ fun d hd => ?_)
  rw [hdec j (P.Icc_q_subset hj), inner_e₂_eq_zero_of_mem hx hd.2
    ((mem_closedBall_zero_iff.1 hd.1).trans_lt hερ)]

/-- The weight `σ = (3/(p+2))^p` of the slit example satisfies `σ/(p+1)! ≤ 1/(2 q!)` for
`q ≤ p`. -/
private theorem slit_sigma_le {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    (3 / ((p : ℝ) + 2)) ^ p / ((p + 1)! : ℝ) ≤ 1 / (2 * q !) := by
  have hσ1 : (3 / ((p : ℝ) + 2)) ^ p ≤ 1 := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    exact pow_le_one₀ (by positivity) (by rw [div_le_one (by positivity)]; linarith)
  have hσ0 : 0 ≤ (3 / ((p : ℝ) + 2)) ^ p := by positivity
  have h2 : (2 * q ! : ℝ) ≤ (p + 1)! := by
    have h1 : 2 * q ! ≤ (q + 1)! := by
      rw [Nat.factorial_succ]; exact Nat.mul_le_mul_right _ (by omega)
    exact_mod_cast h1.trans (Nat.factorial_le (by omega))
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  nlinarith

end SlitStep

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the ARqpIDA-SC row in the
lower-bound mode of the radii control (the "otherwise" order `ε^{-q(p+1)/p}`) for every
`1 ≤ q ≤ p`, with a closed nonconvex feasible set in `ℝ²` and exact derivatives. There are
`f_low`, `L ≥ 1` and `ε₀ > 0` such that, for every `ε ∈ (0, ε₀]` (all `ε_j = ε`) and all ARqpIDA
constants with orders `p, q`, weight `σ₀ = (3/(p+2))^p`, initial radii `δ₀ = ε` and initial
accuracies `h_{0,i} ≤ κ_s ε^{p-i+1}`, there are `ρ ∈ (ε, 2ε]`, the feasible set
`X = {v | v 1 = 0} ∪ {v | ρ ≤ v 1}` (`v 1` is the second coordinate; a line and a parallel
half-plane at distance `ρ`), `f` with
f.bB and f.D0pL (all `L_{f,j} = L`) and an ARqpIDA-SC run on `X` with exact derivatives from
`x₀ = 0` satisfying the radii control in the lower-bound mode (`Chapter13.RadiiControlOf False`
for every `L̄ ≥ 1`; all radii are `ε`), whose first iterate that is `(ε, δ)`-approximately optimal
on `X` for some radii `δ ∈ (0, 1]^q` (`Chapter13.arTest_feasible`) is `x_{k_ε}`,
`k_ε = ⌈ε^{-q(p+1)/p}⌉`, after `k_ε + 1 ≥ ε^{-q(p+1)/p} + 1` function and derivative evaluations.

The run follows the slow example of Theorem 12.2.17 (`r = p`) on the line `v 1 = 0`:
`f(v) = G(v 0) + H(v 1)` with gradient spikes `G'(x_k) = -β_k`,
`β_k = (ε^q + ε^q (k_ε - k)/k_ε)/q!`, steps the minimizers of the model on the line (admissible
Step-2 steps, since (13.1.55)–(13.1.57) are local conditions, but not global minimizers of the
model on `X`, which are in the half-plane), `σ_k = σ₀`, `ρ_k = 1`, and `H'(0) = -1`, so that the
half-plane lowers the Taylor models by at least `ρ > ε`. Radii `δ < ρ` only see the line, where
the measure of order `q` is `β_k δ`; with `ρ^n = ε^n (1 + 1/k_ε)`, `n = max(q - 1, 1)`, this
exceeds `ε δ^q/q!` for every `δ < ρ` exactly when `k < k_ε`, and radii `δ ≥ ρ` reach the
half-plane. So the criterion fails at every radius before `k_ε`, while the Step-1 and Step-2 radii
`ε < ρ` only see the line, where the model measures at the steps vanish (Example 12.1.3). After
`k_ε` one more step reaches a point where all derivatives of `G` vanish, and the run continues with
accuracy-improving iterations there. For `q = 1` this is the "otherwise" entry with a nonconvex
`X` (its order `ε^{-(p+1)/p}` coincides with that of the convex entry). The cases `q = 2 < p`
(with `X ≠ ℝⁿ`) and `3 ≤ q < p` are not reached by the book's reduction to unconstrained
problems: on `ℝⁿ` the order is not attained for `q = 2 < p` (`theorem_14_2_4_arqpida_le_two`), and
for `3 ≤ q < p` the case `X = ℝⁿ` is open (see the module doc). -/
theorem theorem_14_2_4_sharp_arqpida_otherwise_constrained {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    ∃ flow L ε₀ : ℝ, 1 ≤ L ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ P : ARqpIDAParams,
      P.p = p → P.q = q → P.σ₀ = (3 / ((p : ℝ) + 2)) ^ p → (∀ j ∈ Finset.Icc 1 q, P.δ₀ j = ε) →
      (∀ i ∈ Finset.Icc 1 p, P.h₀ i ≤ P.κs * ε ^ (p - i + 1)) →
      ∃ (ρ : ℝ) (X : Set (EuclideanSpace ℝ (Fin 2))) (f : EuclideanSpace ℝ (Fin 2) → ℝ),
        ε < ρ ∧ ρ ≤ 2 * ε ∧ X = {v | v 1 = 0} ∪ {v | ρ ≤ v 1} ∧ IsClosed X ∧
        (∀ y, flow ≤ f y) ∧ AssumptionD0pL f p (fun _ => L) ∧
        ∃ (x : ℕ → EuclideanSpace ℝ (Fin 2)) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ)
          (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 2)) ℝ)
          (dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 2)) (jk : ℕ → ℕ)
          (s : ℕ → EuclideanSpace ℝ (Fin 2)) (acc : ℕ → Prop),
          algorithm_13_1_2_feasible f X (fun _ => 0) P (fun _ => ε) 0 x σ δ δ₁ δs h D dd jk s
            acc ∧
          (∀ k, D k = ftaylorSeries ℝ f (x k)) ∧
          (∀ Lb : ℝ, 1 ≤ Lb → ∀ k, RadiiControlOf False P (fun _ => ε) Lb σ δs s acc k) ∧
          IsFirstHit (arTest_feasible f X P (fun _ => ε) x)
            ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ ∧
          ε ^ (-((q : ℝ) * (p + 1) / p)) + 1 ≤
            (derivEvalCount (fun i => ¬ acc i) ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ : ℝ) ∧
          ε ^ (-((q : ℝ) * (p + 1) / p)) + 1 ≤ (derivEvalCount
            (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i))
              ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ : ℝ) := by
  have hq1 : 1 ≤ q := hq
  have hp1 : 1 ≤ p := hq1.trans hqp
  have hp0 : p ≠ 0 := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp1
  set σI : ℝ := (3 / ((p : ℝ) + 2)) ^ p with hσI
  have hσI0 : 0 < σI := by positivity
  have hσI1 : σI ≤ 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp1
    exact pow_le_one₀ (by positivity) (by rw [div_le_one (by positivity)]; linarith)
  have hpf : (0 : ℝ) < p ! := by positivity
  have hqf : (0 : ℝ) < q ! := by positivity
  obtain ⟨LG, BG, hLG, hBG, hGint⟩ := exists_slitGrad_interpolant hq1 hqp hσI0
  obtain ⟨LH, BH, hLH, hBH, H, hHc, hHL, hHB, hHd⟩ := exists_slitWall p hp1
  set L : ℝ := max 1 (max LG BG) + max 1 (max LH BH) with hL
  refine ⟨-(BG + BH), L, min (1 / 4) (σI / (4 * p !)), ?_, by positivity,
    fun ε hε hε0 P hPp hPq hσ hδ₀ hh₀ => ?_⟩
  · have := le_max_left 1 (max LG BG); have := le_max_left 1 (max LH BH); linarith
  have hε4 : ε ≤ 1 / 4 := hε0.trans (min_le_left _ _)
  have hεσ : ε ≤ σI / (4 * p !) := hε0.trans (min_le_right _ _)
  have hε1 : ε ≤ 1 := by linarith
  -- the data of the slow gradient example
  set e : ℝ := (q : ℝ) * (p + 1) / p with he
  set κ : ℕ := ⌈ε ^ (-e)⌉₊ with hκ
  have hκge : ε ^ (-e) ≤ κ := Nat.le_ceil _
  have hκ1 : 1 ≤ κ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hε _)).ne'
  have hκpos : (0 : ℝ) < κ := by exact_mod_cast hκ1
  set β : ℕ → ℝ := fun k => (ε ^ q + ε ^ q * ((κ : ℝ) - k) / κ) / q ! with hβ
  set ts : ℕ → ℝ := fun k => (p ! * β k / σI) ^ (1 / (p : ℝ)) with hts
  set ξ : ℕ → ℝ := fun k => ∑ i ∈ Finset.range k, ts i with hξ
  have hξ1 : ∀ k, ξ (k + 1) = ξ k + ts k := fun k => Finset.sum_range_succ _ _
  obtain ⟨G, hGc, hGL, hGB, hGs, hGz, hGv⟩ :=
    hGint ε κ ξ β hε hε1 rfl (fun _ => rfl) fun k _ => hξ1 k
  have hβb : ∀ k ≤ κ, ε ^ q / q ! ≤ β k ∧ β k ≤ 2 * ε ^ q / q ! := fun k hk => by
    have hk' : (k : ℝ) ≤ κ := by exact_mod_cast hk
    have h0 : 0 ≤ ε ^ q * ((κ : ℝ) - k) / κ :=
      div_nonneg (mul_nonneg (by positivity) (by linarith)) hκpos.le
    have h1 : ε ^ q * ((κ : ℝ) - k) / κ ≤ ε ^ q := by
      rw [div_le_iff₀ hκpos]; nlinarith [Nat.cast_nonneg (α := ℝ) k, pow_pos hε q]
    exact ⟨div_le_div_of_nonneg_right (by linarith) hqf.le,
      div_le_div_of_nonneg_right (by linarith) hqf.le⟩
  have hβlt : ∀ k < κ, ε ^ q * (1 + 1 / κ) / q ! ≤ β k := fun k hk => by
    have hk' : (k : ℝ) + 1 ≤ κ := by exact_mod_cast hk
    refine div_le_div_of_nonneg_right ?_ hqf.le
    have : ε ^ q * (1 / κ) ≤ ε ^ q * ((κ : ℝ) - k) / κ := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hκpos.le)
        (by positivity)
    nlinarith
  have hβκ : β κ = ε ^ q / q ! := by simp only [hβ, sub_self, mul_zero, zero_div, add_zero]
  have hβpos : ∀ k ≤ κ, 0 < β k := fun k hk => lt_of_lt_of_le (by positivity) (hβb k hk).1
  -- the steps
  have htsp : ∀ k ≤ κ, ts k ^ p = p ! * β k / σI := fun k hk => by
    have := hβpos k hk
    simp only [hts]
    rw [one_div, Real.rpow_inv_natCast_pow (by positivity) hp0]
  have hts0 : ∀ k ≤ κ, 0 < ts k := fun k hk => by
    have := hβpos k hk
    exact Real.rpow_pos_of_pos (by positivity) _
  have hts_ge : ∀ k ≤ κ, ε * ((p : ℝ) + 2) / 3 ≤ ts k := fun k hk => by
    have h1 : (ε * ((p : ℝ) + 2) / 3) ^ p = ε ^ p / σI := by
      rw [hσI, div_pow, mul_pow, div_pow, div_div_eq_mul_div]
    have h2 : ε ^ p ≤ p ! * β k := by
      have hεpq : ε ^ p ≤ ε ^ q := pow_le_pow_of_le_one hε.le hε1 hqp
      have hfq : (q ! : ℝ) ≤ p ! := by exact_mod_cast Nat.factorial_le hqp
      have := (hβb k hk).1
      calc ε ^ p ≤ ε ^ q := hεpq
        _ = q ! * (ε ^ q / q !) := by field_simp
        _ ≤ p ! * β k := mul_le_mul hfq this (by positivity) hpf.le
    have h3 : (ε * ((p : ℝ) + 2) / 3) ^ p ≤ ts k ^ p := by
      rw [h1, htsp k hk]; exact div_le_div_of_nonneg_right h2 hσI0.le
    exact (pow_le_pow_iff_left₀ (by positivity) (hts0 k hk).le hp0).1 h3
  have hts_ge' : ∀ k ≤ κ, ε ≤ ts k := fun k hk => by
    have := hts_ge k hk
    have : ε ≤ ε * ((p : ℝ) + 2) / 3 := by
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp1
      rw [le_div_iff₀ (by norm_num)]; nlinarith
    linarith
  have hts1 : ∀ k ≤ κ, ts k < 1 := fun k hk => by
    by_contra hcon
    have h1 : 1 ≤ ts k ^ p := one_le_pow₀ (not_lt.1 hcon)
    rw [htsp k hk] at h1
    have h2 : p ! * β k / σI ≤ 1 / 2 := by
      rw [div_le_iff₀ hσI0]
      have hb := (hβb k hk).2
      have hεq : ε ^ q ≤ ε := pow_le_of_le_one hε.le hε1 (by omega)
      have : β k ≤ 2 * ε := hb.trans (by
        rw [div_le_iff₀ hqf]
        have : (1 : ℝ) ≤ q ! := by exact_mod_cast Nat.factorial_pos q
        nlinarith)
      have h4 : 4 * p ! * ε ≤ σI := by
        rw [le_div_iff₀ (by positivity)] at hεσ; linarith
      nlinarith
    linarith
  -- the function
  have hG1 : (fun t => 1 * G t) = G := funext fun t => one_mul _
  have hH1 : (fun t => 1 * H t) = H := funext fun t => one_mul _
  obtain ⟨hGr, hGb, hGl⟩ := ridge_const_mul_slow_bounds (G := G) (lam := 1) (e := e₁) hGc hBG
    hGL hGB one_pos le_rfl norm_e₁.le
  obtain ⟨hHr, hHb, hHl⟩ := ridge_const_mul_slow_bounds (G := H) (lam := 1) (e := e₂) hHc hBH
    hHL hHB one_pos le_rfl norm_e₂.le
  rw [hG1] at hGr hGb hGl
  rw [hH1] at hHr hHb hHl
  set f : EuclideanSpace ℝ (Fin 2) → ℝ := ridge G e₁ + ridge H e₂ with hfdef
  have hfc : ContDiff ℝ p f := hGr.add hHr
  have hf : AssumptionD0pL f p (fun _ => L) := by
    refine ⟨hfc, fun j hj => ⟨?_, ?_⟩⟩
    · have := le_max_left 1 (max LG BG); have := le_max_left 1 (max LH BH); linarith
    · exact (hGl j hj).add (hHl j hj)
        (fun y _ => (hGr.of_le (by exact_mod_cast hj)).contDiffAt)
        (fun y _ => (hHr.of_le (by exact_mod_cast hj)).contDiffAt)
  have hfb : ∀ y, -(BG + BH) ≤ f y := fun y => by
    have := hGb y; have := hHb y; simp only [hfdef, Pi.add_apply]; linarith
  -- the feasible set
  set ρ : ℝ := ε * (1 + 1 / κ) ^ (((max (q - 1) 1 : ℕ) : ℝ)⁻¹) with hρ
  have hq0 : max (q - 1) 1 ≠ 0 := by omega
  have hqR : (0 : ℝ) < ((max (q - 1) 1 : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have ha1 : 1 < 1 + 1 / (κ : ℝ) := by
    have : 0 < 1 / (κ : ℝ) := by positivity
    linarith
  have ha2 : 1 + 1 / (κ : ℝ) ≤ 2 := by
    have : 1 / (κ : ℝ) ≤ 1 := by rw [div_le_one hκpos]; exact_mod_cast hκ1
    linarith
  have hερ : ε < ρ := lt_mul_of_one_lt_right hε (Real.one_lt_rpow ha1 (inv_pos.2 hqR))
  have hρ2 : ρ ≤ 2 * ε := by
    rw [hρ, mul_comm 2]
    refine mul_le_mul_of_nonneg_left ?_ hε.le
    calc (1 + 1 / (κ : ℝ)) ^ (((max (q - 1) 1 : ℕ) : ℝ)⁻¹) ≤ (1 + 1 / (κ : ℝ)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le ha1.le (inv_le_one_of_one_le₀ (by
            exact_mod_cast Nat.one_le_iff_ne_zero.2 hq0))
      _ ≤ 2 := by rw [Real.rpow_one]; exact ha2
  have hρpow : ρ ^ max (q - 1) 1 = ε ^ max (q - 1) 1 * (1 + 1 / κ) := by
    rw [hρ, mul_pow, Real.rpow_inv_natCast_pow (by positivity) hq0]
  have hρ0 : 0 < ρ := hε.trans hερ
  set X : Set (EuclideanSpace ℝ (Fin 2)) := slitSet ρ with hX
  have hXeq : X = {v | v 1 = 0} ∪ {v | ρ ≤ v 1} := by
    ext v; simp only [hX, slitSet, inner_e₂]
  have hXc : IsClosed X := by
    rw [hXeq]
    exact (isClosed_eq (by fun_prop) continuous_const).union (isClosed_le continuous_const
      (by fun_prop))
  -- the run
  subst hPp hPq
  obtain ⟨xv, hxv⟩ : ∃ xv : ℕ → EuclideanSpace ℝ (Fin 2), ∀ k, xv k = ξ (min k (κ + 1)) • e₁ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨δv, hδv⟩ : ∃ δv : ℕ → ℕ → ℝ, ∀ k, δv k = if k = 0 then P.δ₀ else fun _ => ε :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨hv, hhv⟩ : ∃ hv : ℕ → ℕ → ℝ, ∀ k, hv k = fun i => P.γh ^ (k - (κ + 1)) * P.h₀ i :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Dv, hDv⟩ : ∃ Dv : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 2)) ℝ,
      ∀ k, Dv k = ftaylorSeries ℝ f (xv k) := ⟨_, fun _ => rfl⟩
  obtain ⟨ddv, hddv⟩ : ∃ ddv : ℕ → ℕ → EuclideanSpace ℝ (Fin 2),
      ∀ k, ddv k = fun _ => if k ≤ κ then (P.ς * ε) • e₁ else 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨sv, hsv⟩ : ∃ sv : ℕ → EuclideanSpace ℝ (Fin 2),
      ∀ k, sv k = if k ≤ κ then ts k • e₁ else 0 := ⟨_, fun _ => rfl⟩
  have hxle : ∀ k ≤ κ + 1, xv k = ξ k • e₁ := fun k hk => by rw [hxv, min_eq_left hk]
  have hxgt : ∀ k, κ + 1 ≤ k → xv k = ξ (κ + 1) • e₁ := fun k hk => by rw [hxv, min_eq_right hk]
  have hx1 : ∀ k, ⟪e₂, xv k⟫ = 0 := fun k => by rw [hxv, inner_e₂_smul_e₁]
  have hHk : ∀ k, IsSpikeJetOf P.p H 1 ⟪e₂, xv k⟫ 1 := fun k => by rw [hx1]; exact hHd
  have hGk : ∀ k ≤ κ, IsSpikeJetOf P.p G 1 ⟪e₁, xv k⟫ (β k) := fun k hk => by
    rw [hxle k (by omega), inner_e₁_smul]; exact hGs k hk
  have hGz' : ∀ k, κ < k → IsSpikeJetOf P.p G 1 ⟪e₁, xv k⟫ 0 := fun k hk => by
    rw [hxgt k hk, inner_e₁_smul]; exact hGz
  have hdecT : ∀ k ≤ κ, ∀ j ∈ Finset.Icc 1 P.p, ∀ d,
      (Dv k).taylorDecrement j d = β k * ⟪e₁, d⟫ + ⟪e₂, d⟫ := fun k hk j hj d => by
    rw [hDv, taylorDecrement_slit hGc hHc (hGk k hk) (hHk k) (Finset.mem_Icc.1 hj).1
      (Finset.mem_Icc.1 hj).2, one_mul]
  have hdecZ : ∀ k, κ < k → ∀ j ∈ Finset.Icc 1 P.p, ∀ d,
      (Dv k).taylorDecrement j d = ⟪e₂, d⟫ := fun k hk j hj d => by
    rw [hDv, taylorDecrement_slit hGc hHc (hGz' k hk) (hHk k) (Finset.mem_Icc.1 hj).1
      (Finset.mem_Icc.1 hj).2, one_mul, zero_mul, zero_add]
  have hfline : ∀ c : ℝ, f (c • e₁) = G c + H 0 := fun c => by
    simp only [hfdef, Pi.add_apply, ridge_apply, inner_e₁_smul, inner_e₂_smul_e₁]
  have hxs : ∀ k ≤ κ, xv (k + 1) = xv k + sv k := fun k hk => by
    rw [hxle (k + 1) (by omega), hxle k (by omega), hsv, ite_eq_left hk, hξ1, add_smul]
  have hdecs : ∀ k ≤ κ, (Dv k).taylorDecrement P.p (sv k) = β k * ts k := fun k hk => by
    rw [hdecT k hk _ (Finset.mem_Icc.2 ⟨hp1, le_rfl⟩), hsv, ite_eq_left hk, inner_e₁_smul,
      inner_e₂_smul_e₁, add_zero]
  have hρ1 : ∀ k ≤ κ, arqpIDARatio f P Dv xv sv k = 1 := fun k hk => by
    have hpos : 0 < β k * ts k := mul_pos (hβpos k hk) (hts0 k hk)
    rw [arqpIDARatio, reductionRatio_def, hdecs k hk, ← hxs k hk, hxle k (by omega),
      hxle (k + 1) (by omega), hfline, hfline, hGv k hk, hξ1]
    rw [show G (ξ k) + H 0 - (G (ξ k) - β k * (ξ k + ts k - ξ k) + H 0) = β k * ts k by ring,
      div_self hpos.ne']
  -- the model along the line
  have hmin : ∀ k ≤ κ, ∀ c : ℝ, regularizedModel (Dv k) P.p P.σ₀ (sv k) ≤
      regularizedModel (Dv k) P.p P.σ₀ (c • e₁) := fun k hk c => by
    obtain ⟨hm, -, -⟩ := isMinOn_neg_monomial_add_regularization le_rfl hp1 (σ := P.σ₀)
      (by rw [hσ]; exact hσI0) (hβpos k hk)
    have e : (β k / (P.σ₀ * (1 - 1)! / P.p !)) ^ (1 / ((P.p - 1 + 1 : ℕ) : ℝ)) = ts k := by
      rw [Nat.sub_add_cancel hp1, hσ]
      simp only [hts, Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one]
      congr 1; field_simp
    rw [e] at hm
    rw [hsv, ite_eq_left hk, hDv, regularizedModel_slit_line hp1 hGc hHc (hGk k hk) (hHk k) _
      (inner_e₂_smul_e₁ _), regularizedModel_slit_line hp1 hGc hHc (hGk k hk) (hHk k) _
      (inner_e₂_smul_e₁ _), inner_e₁_smul, inner_e₁_smul]
    exact (add_le_add_iff_left _).2 (isMinOn_iff.1 hm _ (mem_univ _))
  have hmodel : ∀ k ≤ κ, ∀ ℓ ∈ Finset.Icc 1 P.q, ∀ d, ‖d‖ ≤ ε → ⟪e₂, d⟫ = 0 →
      (ftaylorSeries ℝ (regularizedModel (Dv k) P.p P.σ₀) (sv k)).taylorDecrement ℓ d ≤ 0 :=
    fun k hk ℓ hℓ d hd hd1 => by
      have hℓp : ℓ ≤ P.p := (Finset.mem_Icc.1 hℓ).2.trans P.q_le_p
      have hσ0 : 0 < P.σ₀ := by rw [hσ]; exact hσI0
      rw [hsv, ite_eq_left hk, hDv, taylorDecrement_regularizedModel_slit hp1 hGc hHc (hGk k hk)
        (hHk k) P.σ₀ (ts k) hd1 hℓp]
      have hm : negMonomialRegModel P.p 1 P.σ₀ (β k) =
          fun t : ℝ => -β k * t + P.σ₀ * |t| ^ (P.p + 1) / (P.p + 1)! := by
        funext t; simp [negMonomialRegModel]
      have ht : ts k = (β k * P.p ! / P.σ₀) ^ (1 / (P.p : ℝ)) := by
        simp only [hts, hσ]; ring_nf
      have h0 := taylorMeasure_linearRegModel_eq_zero (p := P.p) (j := ℓ)
        ⟨(Finset.mem_Icc.1 hℓ).1, hℓp⟩ (hβpos k hk) hσ0 (δ := ε) (Or.inr (by
          rw [← ht]
          have := hts_ge k hk
          nlinarith))
      have hle := taylorDecrement_le_taylorMeasure
        (ftaylorSeries ℝ (fun t : ℝ => -β k * t + P.σ₀ * |t| ^ (P.p + 1) / (P.p + 1)!)
          ((β k * P.p ! / P.σ₀) ^ (1 / (P.p : ℝ)))) ℓ (S := univ) (δ := ε) (d := ⟪e₁, d⟫)
        ⟨mem_closedBall_zero_iff.2 (by rw [Real.norm_eq_abs]; exact (abs_inner_e₁_le d).trans hd),
          mem_univ _⟩
      rw [h0] at hle
      rw [hm, ht]
      exact hle
  -- the iterations
  have hσ54 : P.σ₀ / ((P.p + 1)! : ℝ) ≤ 1 / (2 * P.q !) := by
    rw [hσ]; exact slit_sigma_le P.one_le_q P.q_le_p
  have hstep : ∀ k, ARqpDAStep X P (fun _ => ε) xv (fun _ => P.σ₀) δv δv (fun _ _ => ε) hv Dv
      ddv (fun _ => P.q) sv (fun k => κ < k) (arqpIDARatio f P Dv xv sv) k := by
    intro k
    have hδk : ∀ j ∈ Finset.Icc 1 P.q, δv k j = ε := fun j hj => by
      rw [hδv]
      split_ifs
      · exact hδ₀ j hj
      · rfl
    by_cases hk : k ≤ κ
    · refine slit_arqpDAStep (t := ts k) hε hε4 hερ (hβb k hk).1 (hβb k hk).2 hσ54 (hx1 k) hδk
        (by rw [hδv, ite_eq_right (Nat.succ_ne_zero k)]) rfl (fun _ _ => rfl)
        (fun j => by rw [hddv, ite_eq_left hk]) rfl (hdecT k hk)
        (by rw [hsv, ite_eq_left hk]) (hmin k hk) (hmodel k hk)
        (by rw [hsv, ite_eq_left hk, norm_smul_e₁, abs_of_pos (hts0 k hk)]; exact hts1 k hk)
        (fun i hi => ?_) (not_lt.2 hk) (hxs k hk) rfl P.σmin_le_σ₀
        (by rw [hhv, hhv, Nat.sub_eq_zero_of_le (by omega), Nat.sub_eq_zero_of_le (by omega)])
        (hρ1 k hk)
      rw [hhv]
      dsimp only
      rw [Nat.sub_eq_zero_of_le (by omega), pow_zero, one_mul, hsv, ite_eq_left hk,
        norm_smul_e₁, abs_of_pos (hts0 k hk)]
      exact (hh₀ i hi).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hε.le (hts_ge' k hk) _) P.κs_pos.le)
    · have hk' : κ < k := not_le.1 hk
      refine slit_acc_step hε hερ (hx1 k) hδk rfl (fun j => by rw [hddv, ite_eq_right hk])
        (hdecZ k hk') hk' (by rw [hxgt k hk', hxgt (k + 1) (by omega)])
        (by rw [hδv, hδv, ite_eq_right (Nat.succ_ne_zero k), ite_eq_right (by omega)]) rfl
        fun i => ?_
      rw [hhv, hhv, show k + 1 - (κ + 1) = k - (κ + 1) + 1 by omega, pow_succ]
      ring
  have hrun : algorithm_13_1_2_feasible f X (fun _ => 0) P (fun _ => ε) 0 xv (fun _ => P.σ₀) δv
      δv (fun _ _ => ε) hv Dv ddv (fun _ => P.q) sv (fun k => κ < k) :=
    ⟨fun _ _ => ⟨hε, hε1⟩, fun j hj => by rw [hδ₀ j hj], fun _ _ => le_rfl,
      by rw [hxle 0 (Nat.zero_le _)]; simp [hξ], Or.inl (inner_zero_right _), rfl,
      by rw [hδv, ite_eq_left rfl], by funext i; rw [hhv]; simp,
      fun k => by rw [hDv]; exact (jetApprox_self _ _).mono_err fun i _ => by simp, hstep⟩
  -- the criterion
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have htest : ∀ k ≤ κ, (arTest_feasible f X P (fun _ => ε) xv k ↔ k = κ) := by
    intro k hk
    have hdk : ∀ j ∈ Finset.Icc 1 P.q, ∀ d,
        (ftaylorSeries ℝ f (xv k)).taylorDecrement j d = β k * ⟪e₁, d⟫ + ⟪e₂, d⟫ :=
      fun j hj d => by rw [← hDv]; exact hdecT k hk j (P.Icc_q_subset hj) d
    constructor
    · rintro ⟨δ', hδ', ht'⟩
      by_contra hne
      exact slit_not_approx hε hερ hρpow (by positivity) (hβpos k hk).le
        (hβlt k (lt_of_le_of_ne hk hne)) (hx1 k) hq hdk δ' hδ' ht'
    · rintro rfl
      exact ⟨fun _ => ε, fun _ _ => ⟨hε, hε1⟩,
        slit_approx hε hε1 hερ (hβpos _ hk).le hβκ.le (hx1 _) hdk⟩
  refine ⟨ρ, X, f, hερ, hρ2, hXeq, hXc, hfb, hf, xv, fun _ => P.σ₀, δv, δv, fun _ _ => ε, hv,
    Dv, ddv, fun _ => P.q, sv, fun k => κ < k, hrun, hDv, fun Lb hLb k _ _ => ⟨fun h => h.elim,
      fun _ j _ => ?_⟩, ⟨(htest κ le_rfl).2 rfl, fun i hi ht' => hi.ne ((htest i hi.le).1 ht')⟩,
    ?_, ?_⟩
  · have hM : 1 ≤ max Lb P.σ₀ := hLb.trans (le_max_left _ _)
    have h0 : P.ς * P.θ ≤ 1 := mul_le_one_of_le_one P.ς_le_one P.θ_pos.le P.θ_lt_one.le
    rw [div_le_iff₀ (by positivity)]
    have h1 : P.ς * P.θ * ε ≤ ε := mul_le_of_le_one_left hε.le h0
    exact h1.trans (le_mul_of_one_le_right hε.le (by linarith only [hM]))
  · rw [derivEvalCount_of_forall fun i hi => not_lt.2 hi.le, Nat.cast_add, Nat.cast_one]
    linarith only [hκge]
  · rw [derivEvalCount_of_forall fun i hi => Or.inr ⟨not_lt.2 hi.le, by
      rw [hρ1 i hi.le]; exact P.η₁_le_η₂.trans P.η₂_lt_one.le⟩, Nat.cast_add, Nat.cast_one]
    linarith only [hκge]

end Slit

end ARqpIDAConstrained


end CartisGouldToint.Chapter14
