import Numlib.Optimization.ModelBased.ARRun
import Numlib.Optimization.ModelBased.HighOrderModel

/-!
# The high-order adaptive-regularization method ARqp

The ARqp algorithm ([cartis2022evaluation], Algorithm 12.2.2) looks for `(ε, δ)`-approximate
`q`-th order minimizers by approximately minimizing the regularized `p`-th order model
(`p ≥ q`). It is an adaptive-regularization method (`Optimization.IsARRun`) whose Step-1 test and
Step-2 conditions are expressed with decrement measures (`Optimization.decrementMeasure`).

The run predicate `Optimization.IsARqpRun` is generic in

* the **model data** of each iteration, bundled in `Optimization.ARqpData`: the Step-1 decrements
  of the objective's model at `x_k`, the regularized model `m_k`, its decrements at a trial step,
  and the predicted decrease of the ratio. Exact ARqp uses `ARqpData.ofTaylor (ftaylorSeries ℝ f
  (x k)) p (σ k)`; inexact derivatives (Chapter 13) `ARqpData.ofTaylor (D k) p (σ k)`; the
  composite method ARqpC (Algorithm 14.1.1) `ARqpData.ofComposite …` with objective `w = f + h ∘ c`;
* the **feasible set** `X` (§14.2): Step-1 measures are taken over `{e | x_k + e ∈ X}`, steps
  satisfy `x_k + s_k ∈ X`, and model measures are taken over `{e | x_k + s_k + e ∈ X}`;
  unconstrained ARqp is `X = univ`.

## Design of the run predicate

* The Step-1 test stops when every decrease `ΔT_j(x_k, d_{k,j})` is at most `ς ε_j δ_{k,j}^j/j!`
  (`Optimization.MeasureTestPasses`), as in the test (12.2.2) of TRq.
* Step 2 asks (12.2.27) and either the long-step branch `‖s_k‖ ≥ 1` (radii arbitrary in `(0, 1]`;
  this covers (12.2.28) and Algorithm 12.2.3) or (12.2.29) with witnesses
  `d^m_{k,j}`.
* Termination in Step 2 (`m_k(s_k) = m_k(0)`) is allowed only if `0` then globally minimizes the
  model over the feasible steps, as guaranteed by Algorithm 12.2.3 (12.2.34); without it
  termination in Step 2 would not certify anything (Lemma 12.2.10).
* Step 1 is skipped after an unsuccessful iteration: the run keeps `x`, `δ` and the Step-1
  witnesses. For Taylor data (`ARqpData.ofTaylor`, whose decrements do not depend on `σ`) the test
  outcome is then unchanged; for model data that change with the iteration in other ways (e.g.
  re-evaluated inexact derivatives) the Step-1 test is re-evaluated with the kept witnesses, which
  must still be approximate optimality displacements (the `witness` field).
* Long steps (`‖s_k‖ ≥ 1`) only constrain the radii to `(0, 1]`; lower bounds on the radii such as
  (12.2.45), (12.2.50) are not part of the run and are carried separately (as in
  `exists_isARqpRun`).
* `ARqpParams` asks `θ ∈ (0, 1)`; the complexity analysis with `ς < 1` needs `θ < ς`, imposed
  where used.

## Main definitions and results

* `Optimization.ARqpParams`, `Optimization.ARqpData` (with `ARqpData.ofTaylor`,
  `ARqpData.ofComposite`), `Optimization.ARqpStep` (the Step-2 conditions),
  `Optimization.IsARqpRun`;
* `Optimization.IsARqpRun.mem`, `.model_lt`, `.delta_mem`: iterates stay feasible, the model
  decreases strictly before termination, and the radii stay in `(0, 1]`;
* `Optimization.exists_isARqpRun`: runs of exact ARqp exist in finite dimension, with the radii
  of Lemma 12.2.9.
-/

open Set Metric Finset
open scoped Nat

namespace Optimization

/-- The constants of ARqp and ARqpC ([cartis2022evaluation], Algorithms 12.2.2, 14.1.1, Step 0): the
adaptive-regularization constants and `θ ∈ (0, 1)`, `ς ∈ (0, 1]`. (The complexity analysis also
needs `θ < ς`, which is imposed where used; for `ς = 1` it is `θ < 1`.) -/
structure ARqpParams extends ARParams where
  /-- The model-optimality tolerance factor of (12.2.29). -/
  θ : ℝ
  /-- The accuracy factor of approximate measure evaluations ((12.2.26), (12.2.29)). -/
  ς : ℝ
  /-- `θ > 0`. -/
  θ_pos : 0 < θ
  /-- `θ < 1`. -/
  θ_lt_one : θ < 1
  /-- `ς > 0`. -/
  ς_pos : 0 < ς
  /-- `ς ≤ 1`. -/
  ς_le_one : ς ≤ 1

/-- The model data of one high-order adaptive-regularization iteration: `dec j` is the order-`j`
decrement `ΔT_j(x_k, ·)` of the objective's (generalized) Taylor model at the iterate (Step 1),
`model` is the regularized model `m_k`, `modelDec j s` is the order-`j` decrement
`ΔT_{m_k,j}(s, ·)` of the model at a trial step `s` (Step 2), and `pred s` is the predicted
decrease `ΔT_p(x_k, s)` used in the ratio ((12.2.23), (12.2.26)–(12.2.30), (14.1.10)–(14.1.15)). -/
structure ARqpData (E : Type*) where
  /-- The order-`j` decrement of the objective's model at the iterate. -/
  dec : ℕ → E → ℝ
  /-- The regularized model. -/
  model : E → ℝ
  /-- The order-`j` decrement of the model at a trial step. -/
  modelDec : ℕ → E → E → ℝ
  /-- The predicted decrease of the ratio. -/
  pred : E → ℝ

section Data

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The model data of ARqp for (exact or inexact) Taylor data `D` ([cartis2022evaluation],
(12.2.23), (12.2.26)–(12.2.30), and (13.1.45) for inexact data): decrements of `D`, the regularized
model `regularizedModel D p σ` and its decrements, and the predicted decrease `ΔT_p`. -/
@[simps]
noncomputable def ARqpData.ofTaylor (D : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (σ : ℝ) :
    ARqpData E where
  dec j := D.taylorDecrement j
  model := regularizedModel D p σ
  modelDec j s := (ftaylorSeries ℝ (regularizedModel D p σ) s).taylorDecrement j
  pred := D.taylorDecrement p

/-- The model data of ARqpC ([cartis2022evaluation], (14.1.10)–(14.1.15)): composite decrements,
the composite model `compositeRegularizedModel Df Dc h p σ` and its decrements (14.1.14), and the
predicted decrease `ΔT_{w,p}`. -/
@[simps]
noncomputable def ARqpData.ofComposite (Df : FormalMultilinearSeries ℝ E ℝ)
    (Dc : FormalMultilinearSeries ℝ E F) (h : F → ℝ) (p : ℕ) (σ : ℝ) : ARqpData E where
  dec j := compositeTaylorDecrement Df Dc h j
  model := compositeRegularizedModel Df Dc h p σ
  modelDec j s := compositeModelDecrement Df Dc h p σ j s
  pred := compositeTaylorDecrement Df Dc h p

/-- With `h = 0` the composite model data are the Taylor model data. -/
theorem ARqpData.ofComposite_zero_fun (Df : FormalMultilinearSeries ℝ E ℝ)
    (Dc : FormalMultilinearSeries ℝ E F) (p : ℕ) (σ : ℝ) :
    ARqpData.ofComposite Df Dc (0 : F → ℝ) p σ = ARqpData.ofTaylor Df p σ := by
  simp only [ARqpData.ofComposite, ARqpData.ofTaylor, compositeTaylorDecrement_zero_fun,
    compositeRegularizedModel_zero_fun, compositeModelDecrement_zero_fun]

end Data

variable {E : Type*} [NormedAddCommGroup E]

/-- **The Step-2 conditions of ARqp** ([cartis2022evaluation], (12.2.27)–(12.2.29), (14.1.12)–
(14.1.13)) for model data `M` at the iterate `x`, on the feasible set `X`: the trial point
`x + s` is feasible, the model does not increase, `m(s) = m(0)` only if `0` minimizes the model on
the feasible steps, the radii `δs j` lie in `(0, 1]`, and either `‖s‖ ≥ 1` or every `dm j` is a
`ς`-approximate optimality displacement of the model at `s` over `{e | x + s + e ∈ X}` with
decrease at most `ς θ ε_j δs_j^j/j!`. -/
structure ARqpStep (X : Set E) (P : ARqpParams) (q : ℕ) (ε : ℕ → ℝ) (M : ARqpData E)
    (x s : E) (δs : ℕ → ℝ) (dm : ℕ → E) : Prop where
  /-- The trial point is feasible. -/
  mem : x + s ∈ X
  /-- The model does not increase (12.2.27). -/
  model_le : M.model s ≤ M.model 0
  /-- Termination in Step 2 only at a global model minimizer `0`. -/
  isMinOn_of_eq : M.model s = M.model 0 → IsMinOn M.model {e | x + e ∈ X} 0
  /-- The radii are positive. -/
  radius_pos : ∀ j ∈ Finset.Icc 1 q, 0 < δs j
  /-- The radii are at most `1`. -/
  radius_le_one : ∀ j ∈ Finset.Icc 1 q, δs j ≤ 1
  /-- The long-step branch or the approximate model optimality (12.2.29). -/
  branch : 1 ≤ ‖s‖ ∨ ∀ j ∈ Finset.Icc 1 q,
    IsApproxMeasureStep (M.modelDec j s) (δs j) {e | x + s + e ∈ X} P.ς (dm j) ∧
      M.modelDec j s (dm j) ≤ P.ς * P.θ * ε j * δs j ^ j / j !

/-- The Step-1 test of ARqp at iteration `k` ([cartis2022evaluation], Algorithm 12.2.2, Step 1,
normalized): every order-`j` decrease along the witness `d k j` is at most
`ς ε_j δ_{k,j}^j/j!`. -/
abbrev arqpStop₁ (P : ARqpParams) (q : ℕ) (ε : ℕ → ℝ) (M : ℕ → ARqpData E)
    (δ : ℕ → ℕ → ℝ) (d : ℕ → ℕ → E) (k : ℕ) : Prop :=
  MeasureTestPasses (M k).dec q P.ς ε (δ k) (d k)

/-- The Step-2 termination test of ARqp at iteration `k`: `m_k(s_k) = m_k(0)`. -/
abbrev arqpStop₂ (M : ℕ → ARqpData E) (s : ℕ → E) (k : ℕ) : Prop :=
  (M k).model (s k) = (M k).model 0

/-- The ratio (12.2.30), (14.1.15) of ARqp at iteration `k` for the objective `w`. -/
noncomputable abbrev arqpRatio (w : E → ℝ) (M : ℕ → ARqpData E) (x s : ℕ → E) (k : ℕ) : ℝ :=
  reductionRatio w (x k) (s k) ((M k).pred (s k))

omit [NormedAddCommGroup E] in
theorem arqpStop₁_iff {P : ARqpParams} {q : ℕ} {ε : ℕ → ℝ} {M : ℕ → ARqpData E}
    {δ : ℕ → ℕ → ℝ} {d : ℕ → ℕ → E} {k : ℕ} :
    arqpStop₁ P q ε M δ d k ↔
      ∀ j ∈ Finset.Icc 1 q, (M k).dec j (d k j) ≤ P.ς * ε j * δ k j ^ j / j ! :=
  Iff.rfl

theorem arqpStop₂_iff {M : ℕ → ARqpData E} {s : ℕ → E} {k : ℕ} :
    arqpStop₂ M s k ↔ (M k).model (s k) = (M k).model 0 :=
  Iff.rfl

theorem arqpRatio_eq (w : E → ℝ) (M : ℕ → ARqpData E) (x s : ℕ → E) (k : ℕ) :
    arqpRatio w M x s k = reductionRatio w (x k) (s k) ((M k).pred (s k)) :=
  rfl

/-- **A run of ARqp** ([cartis2022evaluation], Algorithm 12.2.2; with composite data Algorithm
14.1.1; with a general feasible set the -SC variants of §14.2) for the objective `w`, the closed
feasible set `X`, constants `P`, criticality order `q`, accuracies `ε`, initial radii `δ₀`, and
model data `M k` at each iteration. The sequences are the iterates `x`, steps `s`, weights `σ`,
Step-1 radii `δ` and witnesses `d`, and Step-2 radii `δs` and witnesses `dm`. The run terminates
at the first `k` with `arqpStop₁ … k ∨ arqpStop₂ … k`. -/
structure IsARqpRun (w : E → ℝ) (X : Set E) (P : ARqpParams) (q : ℕ) (ε δ₀ : ℕ → ℝ)
    (M : ℕ → ARqpData E) (x s : ℕ → E) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E) :
    Prop where
  /-- Steps 2–4: the generic adaptive-regularization run. -/
  toIsARRun : IsARRun P.toARParams (arqpStop₁ P q ε M δ d)
    (fun k => ARqpStep X P q ε (M k) (x k) (s k) (δs k) (dm k)) (arqpStop₂ M s)
    (arqpRatio w M x s) x s σ
  /-- The initial point is feasible. -/
  mem_zero : x 0 ∈ X
  /-- The initial radii. -/
  delta_zero : δ 0 = δ₀
  /-- Step 1 ((12.2.26), (14.1.10)): the witnesses are `ς`-approximate optimality displacements
  over the feasible displacements, at every iteration reached (including the last one). -/
  witness : ∀ k, (∀ i < k, ¬ IsARRun.Stop (arqpStop₁ P q ε M δ d) (arqpStop₂ M s) i) →
    ∀ j ∈ Finset.Icc 1 q, IsApproxMeasureStep ((M k).dec j) (δ k j) {e | x k + e ∈ X} P.ς (d k j)
  /-- Step 3: successful iterations inherit the Step-2 radii; unsuccessful ones keep the radii
  and the Step-1 witnesses. -/
  radii : UntilHit (IsARRun.Stop (arqpStop₁ P q ε M δ d) (arqpStop₂ M s)) fun k =>
    (P.η₁ ≤ arqpRatio w M x s k → δ (k + 1) = δs k) ∧
      (¬ P.η₁ ≤ arqpRatio w M x s k → δ (k + 1) = δ k ∧ d (k + 1) = d k)

namespace IsARqpRun

variable {w : E → ℝ} {X : Set E} {P : ARqpParams} {q : ℕ} {ε δ₀ : ℕ → ℝ}
  {M : ℕ → ARqpData E} {x s : ℕ → E} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → E}

/-- The Step-2 conditions hold at every iteration reached at which the Step-1 test fails. -/
theorem step (h : IsARqpRun w X P q ε δ₀ M x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i < k, ¬ IsARRun.Stop (arqpStop₁ P q ε M δ d) (arqpStop₂ M s) i)
    (h1 : ¬ arqpStop₁ P q ε M δ d k) : ARqpStep X P q ε (M k) (x k) (s k) (δs k) (dm k) :=
  h.toIsARRun.step k hk h1

/-- **Iterates stay feasible**: `x_k ∈ X` for every iteration reached. -/
theorem mem (h : IsARqpRun w X P q ε δ₀ M x s σ δ δs d dm) :
    ∀ k, (∀ i < k, ¬ IsARRun.Stop (arqpStop₁ P q ε M δ d) (arqpStop₂ M s) i) → x k ∈ X := by
  intro k
  induction k with
  | zero => exact fun _ => h.mem_zero
  | succ k ih =>
    intro hk
    have hk' : ∀ i ≤ k, ¬ IsARRun.Stop (arqpStop₁ P q ε M δ d) (arqpStop₂ M s) i :=
      fun i hi => hk i (Nat.lt_succ_of_le hi)
    have hacc := h.toIsARRun.accept k hk'
    rcases hacc.eq_add_or_eq_self with h' | h'
    · rw [h']
      exact (h.step (fun i hi => hk' i hi.le) fun h1 => hk' k le_rfl (Or.inl h1)).mem
    · rw [h']
      exact ih fun i hi => hk' i hi.le

/-- **Strict model decrease before termination**: `m_k(s_k) < m_k(0)` at every iteration before
termination (from (12.2.27) and the failed Step-2 test); this is the hypothesis of the generic
`IsARRun.sigma_le`. -/
theorem model_lt (h : IsARqpRun w X P q ε δ₀ M x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ IsARRun.Stop (arqpStop₁ P q ε M δ d) (arqpStop₂ M s) i) :
    (M k).model (s k) < (M k).model 0 := by
  have hstep := h.step (fun i hi => hk i hi.le) fun h1 => hk k le_rfl (Or.inl h1)
  exact lt_of_le_of_ne hstep.model_le fun h2 => hk k le_rfl (Or.inr h2)

/-- **The radii stay in `(0, 1]`**: if `δ₀ j ∈ (0, 1]` for `j = 1, …, q`, then so is `δ_{k,j}` at
every iteration reached. -/
theorem delta_mem (h : IsARqpRun w X P q ε δ₀ M x s σ δ δs d dm)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) :
    ∀ k, (∀ i < k, ¬ IsARRun.Stop (arqpStop₁ P q ε M δ d) (arqpStop₂ M s) i) →
      ∀ j ∈ Finset.Icc 1 q, 0 < δ k j ∧ δ k j ≤ 1 := by
  intro k
  induction k with
  | zero => exact fun _ => by rw [h.delta_zero]; exact hδ₀
  | succ k ih =>
    intro hk j hj
    have hk' : ∀ i ≤ k, ¬ IsARRun.Stop (arqpStop₁ P q ε M δ d) (arqpStop₂ M s) i :=
      fun i hi => hk i (Nat.lt_succ_of_le hi)
    obtain ⟨hs, hu⟩ := h.radii k hk'
    by_cases hρ : P.η₁ ≤ arqpRatio w M x s k
    · have hstep := h.step (fun i hi => hk' i hi.le) fun h1 => hk' k le_rfl (Or.inl h1)
      rw [hs hρ]
      exact ⟨hstep.radius_pos j hj, hstep.radius_le_one j hj⟩
    · rw [(hu hρ).1]
      exact ih (fun i hi => hk' i hi.le) j hj

/-- **Restricting an unconstrained run to a feasible set**: an ARqp run on `univ` is a run on `X`
if its iterates reached, their Step-1 displacements, and the trial points and Step-2
displacements of its short steps lie in `X`, and the decrements are bounded above on balls (as
for Taylor data). -/
theorem of_univ (h : IsARqpRun w univ P q ε δ₀ M x s σ δ δs d dm) {X : Set E}
    (hdec : ∀ k j r, BddAbove ((M k).dec j '' (closedBall 0 r ∩ {e | x k + e ∈ univ})))
    (hmdec : ∀ k j r, BddAbove
      ((M k).modelDec j (s k) '' (closedBall 0 r ∩ {e | x k + s k + e ∈ univ})))
    (hX : ∀ k, (∀ i < k, ¬ IsARRun.Stop (arqpStop₁ P q ε M δ d) (arqpStop₂ M s) i) →
      x k ∈ X ∧ (∀ j ∈ Finset.Icc 1 q, x k + d k j ∈ X) ∧ x k + s k ∈ X ∧
        (‖s k‖ < 1 → ∀ j ∈ Finset.Icc 1 q, x k + s k + dm k j ∈ X)) :
    IsARqpRun w X P q ε δ₀ M x s σ δ δs d dm := by
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
    · exact Or.inr fun j hj => ⟨(hb j hj).1.mono_set hς (hmdec k j _) (fun _ _ => mem_univ _)
        (hdm hl j hj), (hb j hj).2⟩
  · exact (h.witness k hk j hj).mono_set hς (hdec k j _) (fun _ _ => mem_univ _)
      ((hX k hk).2.1 j hj)

end IsARqpRun

/-! ### Existence of runs -/

section Existence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Existence of an ARqp step** ([cartis2022evaluation], Lemma 12.2.9, in the form of the
Step-2 conditions, unconstrained): in finite dimension, for data `D` with `‖D_i‖ ≤ L` for
`i = 2, …, p` (`L ≥ 0`), `1 ≤ p`, `q ≤ p`, `σ > 0` and `ε_j > 0`, there are a step, radii and
witnesses satisfying `ARqpStep univ P q ε (ARqpData.ofTaylor D p σ) x …`, with `δs_j = 1` for
`j ≤ 2` (12.2.44) and `δs_j = min(1, ς θ ε_j/(4 (3 L + σ)))` for `j ≥ 3` (12.2.45). -/
theorem exists_arqpStep_ofTaylor [FiniteDimensional ℝ E] (P : ARqpParams) {p q : ℕ}
    (hp : 1 ≤ p) (hq : q ≤ p) {ε : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j)
    {D : FormalMultilinearSeries ℝ E ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hD : ∀ i ∈ Finset.Icc 2 p, ‖D i‖ ≤ L) {σ : ℝ} (hσ : 0 < σ) (x : E) :
    ∃ s : E, ∃ δs : ℕ → ℝ, ∃ dm : ℕ → E,
      ARqpStep univ P q ε (ARqpData.ofTaylor D p σ) x s δs dm ∧
      (∀ j ∈ Finset.Icc 1 q, j ≤ 2 → δs j = 1) ∧
      ∀ j ∈ Finset.Icc 3 q, δs j = min 1 (P.ς * P.θ * ε j / (4 * (3 * L + σ))) := by
  obtain ⟨s, δs, dm, hmin, hrad, h12, h3, hbranch⟩ :=
    exists_highOrderStep (D := D) (σ := σ) hp hq hσ hL hD P.θ_pos P.ς_pos P.ς_le_one hε
  have hU : ∀ y : E, {e : E | y + e ∈ (univ : Set E)} = univ := fun y => by ext; simp
  refine ⟨s, δs, dm, ⟨mem_univ _, hmin (mem_univ 0), fun heq => ?_,
    fun j hj => (hrad j hj).1, fun j hj => (hrad j hj).2, ?_⟩, h12, h3⟩
  · refine isMinOn_iff.2 fun e _ => ?_
    change regularizedModel D p σ 0 ≤ regularizedModel D p σ e
    change regularizedModel D p σ s = regularizedModel D p σ 0 at heq
    rw [← heq]
    exact hmin (mem_univ e)
  · rw [hU]
    exact hbranch

/-- One ARqp iteration's state in the existence proof: iterate, weight, Step-1 radii and
witnesses, and the Step-2 step, radii and witnesses. -/
private structure ARqpState (E : Type*) where
  x : E
  σ : ℝ
  δ : ℕ → ℝ
  d : ℕ → E
  s : E
  δs : ℕ → ℝ
  dm : ℕ → E

omit [InnerProductSpace ℝ E] in
/-- **Existence of ARqp runs from the existence of the steps** (the conceptual algorithm is well
defined as soon as its steps are): let `M y σ` be model data at the point `y` with weight `σ`,
let every feasible `y` and radii `δ ∈ (0, 1]^q` admit Step-1 witnesses (`ς`-approximate
optimality displacements of the decrements `(M y σ).dec j` over `{e | y + e ∈ X}`, valid for
every weight `σ`), and let every feasible `y` and `σ > 0` admit a Step-2 triple `(s, δs, dm)`
(`ARqpStep`) with a further property `Q y σ s δs dm`. Then from every `x₀ ∈ X` there is an ARqp
run with model data `M (x k) (σ k)` whose Step-2 triples satisfy `Q` at every iteration
reached. -/
theorem exists_isARqpRun_of_forall (w : E → ℝ) (X : Set E) (P : ARqpParams) {q : ℕ}
    {ε δ₀ : ℕ → ℝ} (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) (M : E → ℝ → ARqpData E)
    (Q : E → ℝ → E → (ℕ → ℝ) → (ℕ → E) → Prop)
    (hwit : ∀ y ∈ X, ∀ δ : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δ j ∧ δ j ≤ 1) →
      ∃ d : ℕ → E, ∀ σ, ∀ j ∈ Finset.Icc 1 q,
        IsApproxMeasureStep ((M y σ).dec j) (δ j) {e | y + e ∈ X} P.ς (d j))
    (hstep : ∀ y ∈ X, ∀ σ, 0 < σ → ∃ (s : E) (δs : ℕ → ℝ) (dm : ℕ → E),
      ARqpStep X P q ε (M y σ) y s δs dm ∧ Q y σ s δs dm)
    {x₀ : E} (hx₀ : x₀ ∈ X) :
    ∃ (x s : ℕ → E) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E), x 0 = x₀ ∧
      IsARqpRun w X P q ε δ₀ (fun k => M (x k) (σ k)) x s σ δ δs d dm ∧
      ∀ k, (∀ i < k, ¬ IsARRun.Stop (arqpStop₁ P q ε (fun k => M (x k) (σ k)) δ d)
          (arqpStop₂ (fun k => M (x k) (σ k)) s) i) →
        Q (x k) (σ k) (s k) (δs k) (dm k) := by
  classical
  -- Step-1 witnesses
  have hwit' : ∀ (y : E) (δ : ℕ → ℝ), ∃ d : ℕ → E, y ∈ X →
      (∀ j ∈ Finset.Icc 1 q, 0 < δ j ∧ δ j ≤ 1) → ∀ σ, ∀ j ∈ Finset.Icc 1 q,
        IsApproxMeasureStep ((M y σ).dec j) (δ j) {e | y + e ∈ X} P.ς (d j) := by
    intro y δ
    by_cases h : y ∈ X ∧ ∀ j ∈ Finset.Icc 1 q, 0 < δ j ∧ δ j ≤ 1
    · obtain ⟨d, hd⟩ := hwit y h.1 δ h.2
      exact ⟨d, fun _ _ => hd⟩
    · exact ⟨0, fun hy hδ => absurd ⟨hy, hδ⟩ h⟩
  choose wit hwit using hwit'
  -- Step-2 steps
  have hstp : ∀ (y : E) (σ : ℝ), ∃ t : E × (ℕ → ℝ) × (ℕ → E), y ∈ X → 0 < σ →
      ARqpStep X P q ε (M y σ) y t.1 t.2.1 t.2.2 ∧ Q y σ t.1 t.2.1 t.2.2 := by
    intro y σ
    by_cases h : y ∈ X ∧ 0 < σ
    · obtain ⟨s, δs, dm, h'⟩ := hstep y h.1 σ h.2
      exact ⟨(s, δs, dm), fun _ _ => h'⟩
    · exact ⟨(0, 0, 0), fun hy hσ => absurd ⟨hy, hσ⟩ h⟩
  choose stp hstp using hstp
  -- the states and their invariant
  let mk : E → ℝ → (ℕ → ℝ) → (ℕ → E) → ARqpState E := fun y σ δ d =>
    ⟨y, σ, δ, d, (stp y σ).1, (stp y σ).2.1, (stp y σ).2.2⟩
  let Good : ARqpState E → Prop := fun a =>
    a.x ∈ X ∧ P.σmin ≤ a.σ ∧ 0 < a.σ ∧ (∀ j ∈ Finset.Icc 1 q, 0 < a.δ j ∧ a.δ j ≤ 1) ∧
      (∀ σ, ∀ j ∈ Finset.Icc 1 q,
        IsApproxMeasureStep ((M a.x σ).dec j) (a.δ j) {e | a.x + e ∈ X} P.ς (a.d j)) ∧
      ARqpStep X P q ε (M a.x a.σ) a.x a.s a.δs a.dm ∧ Q a.x a.σ a.s a.δs a.dm
  have hmk : ∀ y σ δ d, y ∈ X → P.σmin ≤ σ → 0 < σ →
      (∀ j ∈ Finset.Icc 1 q, 0 < δ j ∧ δ j ≤ 1) →
      (∀ σ, ∀ j ∈ Finset.Icc 1 q,
        IsApproxMeasureStep ((M y σ).dec j) (δ j) {e | y + e ∈ X} P.ς (d j)) →
      Good (mk y σ δ d) := fun y σ δ d hy h1 h2 h3 h4 => ⟨hy, h1, h2, h3, h4, hstp y σ hy h2⟩
  let stopS : ARqpState E → Prop := fun a =>
    MeasureTestPasses (M a.x a.σ).dec q P.ς ε a.δ a.d ∨ (M a.x a.σ).model a.s = (M a.x a.σ).model 0
  let ratio : ARqpState E → ℝ := fun a => reductionRatio w a.x a.s ((M a.x a.σ).pred a.s)
  let Trans : ARqpState E → ARqpState E → Prop := fun a b =>
    ARAcceptance P.toARParams (ratio a) a.x a.s b.x a.σ b.σ ∧
      (P.η₁ ≤ ratio a → b.δ = a.δs) ∧ (¬ P.η₁ ≤ ratio a → b.δ = a.δ ∧ b.d = a.d)
  have hnext : ∀ a, Good a → ∃ b, Good b ∧ Trans a b := by
    rintro a ⟨hx, hmin, hpos, hδ, hw, hst, -⟩
    obtain ⟨σ', hacc, hmin', hpos'⟩ := exists_arAcceptance P.toARParams (ratio a) a.x a.s hmin
    by_cases hρ : P.η₁ ≤ ratio a
    · simp only [hρ, ↓reduceIte] at hacc
      have hδs : ∀ j ∈ Finset.Icc 1 q, 0 < a.δs j ∧ a.δs j ≤ 1 :=
        fun j hj => ⟨hst.radius_pos j hj, hst.radius_le_one j hj⟩
      refine ⟨mk (a.x + a.s) σ' a.δs (wit (a.x + a.s) a.δs), hmk _ _ _ _ hst.mem hmin'
        (hpos' hpos) hδs (hwit _ _ hst.mem hδs), hacc, fun _ => rfl,
        fun h => absurd hρ h⟩
    · simp only [hρ, ↓reduceIte] at hacc
      exact ⟨mk a.x σ' a.δ a.d, hmk _ _ _ _ hx hmin' (hpos' hpos) hδ hw, hacc,
        fun h => absurd h hρ, fun _ => ⟨rfl, rfl⟩⟩
  -- the initial state
  set a₀ := mk x₀ P.σ₀ δ₀ (wit x₀ δ₀) with ha₀
  have hgood₀ : Good a₀ := hmk _ _ _ _ hx₀ P.σmin_le_σ₀ P.σ₀_pos hδ₀ (hwit _ _ hx₀ hδ₀)
  obtain ⟨r, hr0, hr⟩ := exists_run_of_forall_exists_of_invariant
    (init := fun a => a = a₀) (inv := fun _ a => Good a) (stop := fun _ a => stopS a)
    (step := fun _ a b => Trans a b ∧ Good b) ⟨a₀, rfl⟩ (fun a ha => ha ▸ hgood₀)
    (fun _ a ha _ => by
      obtain ⟨b, hb, hab⟩ := hnext a ha
      exact ⟨b, hb, hab, hb⟩)
  have hgood : ∀ k, (∀ i < k, ¬ stopS (r i)) → Good (r k) := by
    intro k hk
    cases k with
    | zero => rw [hr0]; exact hgood₀
    | succ k => exact (hr k fun j hj => hk j (Nat.lt_succ_of_le hj)).2.2
  refine ⟨fun k => (r k).x, fun k => (r k).s, fun k => (r k).σ, fun k => (r k).δ,
    fun k => (r k).δs, fun k => (r k).d, fun k => (r k).dm, by simp [hr0, ha₀, mk], ?_,
    fun k hk => (hgood k hk).2.2.2.2.2.2⟩
  exact ⟨⟨by simp [hr0, ha₀, mk], fun k hk _ => (hgood k hk).2.2.2.2.2.1,
    fun k hk => (hr k hk).2.1.1⟩, (hgood 0 fun _ h => absurd h (Nat.not_lt_zero _)).1,
    by simp [hr0, ha₀, mk], fun k hk => (hgood k hk).2.2.2.2.1 (r k).σ,
    fun k hk => (hr k hk).2.1.2⟩

/-- **Existence of ARqp runs** ([cartis2022evaluation], Lemmas 12.2.9–12.2.10: the conceptual
ARqp algorithm is well defined). Let `E` be finite-dimensional, `f : E → ℝ`, `1 ≤ p`, `q ≤ p`,
`ε_j > 0` and `δ₀_j ∈ (0, 1]` for `j = 1, …, q`, and `L : E → ℝ` a nonnegative bound
`‖∇^i f(y)‖ ≤ L(y)` for `i = 2, …, p` (a constant under f.D1pL, (12.2.24); any `f` has one, e.g.
`L(y) = ∑_{i=2}^p ‖∇^i f(y)‖`). Then from every `x₀` there is a run of exact ARqp
(`X = univ`, `M k = ARqpData.ofTaylor (ftaylorSeries ℝ f (x k)) p (σ k)`) whose Step-2 radii
satisfy (12.2.44)–(12.2.45) with `L(x_k)` at every iteration reached: `δs_{k,j} = 1` for `j ≤ 2`
and `δs_{k,j} = min(1, ς θ ε_j/(4 (3 L(x_k) + σ_k)))` for `j ≥ 3`. -/
theorem exists_isARqpRun [FiniteDimensional ℝ E] (f : E → ℝ) (P : ARqpParams) {p q : ℕ}
    (hp : 1 ≤ p) (hq : q ≤ p) {ε δ₀ : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) (L : E → ℝ) (hL0 : ∀ y, 0 ≤ L y)
    (hL : ∀ y, ∀ i ∈ Finset.Icc 2 p, ‖iteratedFDeriv ℝ i f y‖ ≤ L y) (x₀ : E) :
    ∃ (x s : ℕ → E) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E), x 0 = x₀ ∧
      IsARqpRun f univ P q ε δ₀ (fun k => ARqpData.ofTaylor (ftaylorSeries ℝ f (x k)) p (σ k))
        x s σ δ δs d dm ∧
      ∀ k, (∀ i < k, ¬ IsARRun.Stop
          (arqpStop₁ P q ε (fun k => ARqpData.ofTaylor (ftaylorSeries ℝ f (x k)) p (σ k)) δ d)
          (arqpStop₂ (fun k => ARqpData.ofTaylor (ftaylorSeries ℝ f (x k)) p (σ k)) s) i) →
        (∀ j ∈ Finset.Icc 1 q, j ≤ 2 → δs k j = 1) ∧
        ∀ j ∈ Finset.Icc 3 q, δs k j = min 1 (P.ς * P.θ * ε j / (4 * (3 * L (x k) + σ k))) := by
  refine exists_isARqpRun_of_forall f univ P hδ₀
    (fun y σ => ARqpData.ofTaylor (ftaylorSeries ℝ f y) p σ)
    (fun y σ _ δs _ => (∀ j ∈ Finset.Icc 1 q, j ≤ 2 → δs j = 1) ∧
      ∀ j ∈ Finset.Icc 3 q, δs j = min 1 (P.ς * P.θ * ε j / (4 * (3 * L y + σ))))
    (fun y _ δ hδ => ?_) (fun y _ σ hσ => ?_) (mem_univ x₀)
  · have h : ∀ j, ∃ dj : E, j ∈ Finset.Icc 1 q → IsApproxMeasureStep
        ((ftaylorSeries ℝ f y).taylorDecrement j) (δ j) {e | y + e ∈ (univ : Set E)} P.ς dj := by
      intro j
      by_cases hj : j ∈ Finset.Icc 1 q
      · obtain ⟨dj, hdj⟩ := exists_isApproxMeasureStep_taylorDecrement (ftaylorSeries ℝ f y) j
          (S := {e | y + e ∈ (univ : Set E)}) (by simp) (by simp) (hδ j hj).1.le P.ς_le_one
        exact ⟨dj, fun _ => hdj⟩
      · exact ⟨0, fun h' => absurd h' hj⟩
    choose d hd using h
    exact ⟨d, fun _ j hj => hd j hj⟩
  · obtain ⟨s, δs, dm, h⟩ := exists_arqpStep_ofTaylor P hp hq hε (hL0 y) (hL y) hσ y
      (D := ftaylorSeries ℝ f y)
    exact ⟨s, δs, dm, h⟩

end Existence

end Optimization
