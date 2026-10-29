import Numlib.Optimization.ModelBased.HighOrder.ARqpCComplexity
import Numlib.Optimization.ModelBased.HighOrder.ARqpDetailedStep
import Numlib.Optimization.ModelBased.HighOrder.TRqCall

/-!
# ARqpC runs as inner solvers

The inner solver INNER of adaptive-regularization type of the two-phase method TPqp-GC
([cartis2022evaluation], §14.3) is ARqp-SC: the high-order regularization method on `f` over a
closed feasible set `X`, whose Step 2 is the detailed Step 2 of Algorithm 14.1.2. It is the
ARqpC run (`IsARqpCRun`) with zero composite part `c = 0 : E → G`, `h = 0` (any normed space `G`
serves as the codomain of `c`), with the book's halving set `compositeHalvingSet 0 X`
(`j ≥ 2`, and `j = 1` when `X` is not convex). Each call starts afresh from the radii `1` at a
point given by the outer method, and is cut either at its own termination or earlier by a test
of the outer method. This file collects what an outer analysis needs about one call, with
constants that depend on `f` only through the constants `L` of its derivatives on a set
containing the sublevel set of the start of the call, so that they are uniform over all calls
(symmetric with the trust-region inner solver of
`Numlib.Optimization.ModelBased.HighOrder.TRqCall`).

For `c = 0`, `h = 0` the model data are those of ARqp (`arqpcData_zero`), so such a run is an ARqp
run with exact data (`IsARqpCRun.isARqpRun_zero`): both the composite analysis (decreases of order
`ε_j^{j+1}`, the ARqpC-SC row of (14.2.12)) and the ARqp analysis (decreases of order `ε_j^{π_j}`,
`π_j = arqpPiOf u p j`, the ARqp-SC row in radii mode `u`) apply.

## Main definitions

* `Optimization.arqpKappaUns`, `arqpCallKappaDecr`, `arqpCallKappaUnc`, `arqpCallKappaRad`: the
  constants of Lemmas 14.2.2, 14.2.3 and of the radius policy for a call;
* `Optimization.arqpJetBound`: the jet bound `max(1, max_{i ∈ [2, p]} ‖∇^i f(y)‖)`;
* `Optimization.IsARqpOutput`, `IsARqpOutputCost`: a terminating call, with its evaluation counts;
* `Optimization.IsARqpCallOut`: a call cut at any iteration up to its termination, with its
  iterates, successful iterations and returned radii.

## Main results

* `Optimization.IsARqpCRun.isARqpRun_zero`, `arqpcStop_zero_iff`, `arqpRatio_zero`: the reduction
  of `c = 0` to ARqp;
* `Optimization.IsARqpCRun.radii_zero`, `decrease_zero`, `decrease_composite_zero`,
  `radius_ge_zero`, `exists_cert_zero`: the radii, decreases and certificates of such runs;
* `Optimization.exists_isARqpOutputCost`, `IsARqpOutputCost.cost_le`,
  `IsARqpOutputCost.cost_le_arqp`: existence and cost of terminating calls, in both rows of
  (14.2.12);
* `Optimization.IsARqpCallOut.eq_of_not_succ`, `IsARqpCallOut.le_count`,
  `IsARqpCallOut.decrease`, `IsARqpCallOut.decrease_arqp`, `IsARqpCallOut.radius_ge` and their
  bundle `IsARqpCallOut.contract`: the contract of one call (Lemmas 14.2.2–14.2.3 and the radius
  policy);
* `Optimization.exists_isARqpRun_unit`, `IsARqpUnitOutputCost.cost_le`,
  `IsARqpUnitCallOut.contract`, `exists_isARqpUnitCallOut_of_stop`: the calls of ARqp on the whole
  space with unit radii (`q ≤ 2`);
* `Optimization.exists_isARqpCallOut_of_stop`: calls stopped at the first iterate satisfying an
  external test, or at termination, exist.

## Design notes

The call predicates `IsARqpOutput`, `IsARqpOutputCost` and `IsARqpCallOut` take the codomain `G`
of the zero constraint map as an explicit argument, so that they are literally the predicates of
the ARqpC runs with `c = 0 : E → G` (in applications `G` is the codomain of the constraints of the
composite problem, e.g. `ℝ⁰`); every result holds for every `G`. The detailed Step 2 of such a run
is that of the ARqp model `regularizedModel` (`isARqpCDetailedStep_zero_iff`), and the runs are
the ARqp runs with that Step 2 (`IsARqpCRun.isARqpRun_zero`, `IsARqpCRun.of_isARqpRun_zero`).
-/

open Set Metric
open scoped Nat

namespace Optimization

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-! ### ARqpC with `c = 0` and `h = 0` -/

section Zero

variable {f : E → ℝ} {X : Set E} {p q : ℕ} {P : ARqpParams} {J : Set ℕ} {ε δ₀ : ℕ → ℝ}
  {x s : ℕ → E} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → E}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedSpace ℝ G] in
/-- The objective `f + 0 ∘ 0` is `f`. -/
theorem add_zero_comp_zero (f : E → ℝ) :
    (fun y => f y + (0 : G → ℝ) ((0 : E → G) y)) = f :=
  funext fun _ => by simp

/-- The model data of ARqpC with `c = 0`, `h = 0` are those of ARqp. -/
@[simp] theorem arqpcData_zero (f : E → ℝ) (p : ℕ) (x : ℕ → E) (σ : ℕ → ℝ) :
    arqpcData f (0 : E → G) (0 : G → ℝ) p x σ = arqpData f p x σ :=
  funext fun _ => ARqpData.ofComposite_zero_fun _ _ _ _

/-- The termination test of ARqpC with `c = 0`, `h = 0` is that of ARqp. -/
theorem arqpcStop_zero_iff {k : ℕ} :
    arqpcStop f (0 : E → G) 0 P p q ε x s σ δ d k ↔ arqpStop f P p q ε x s σ δ d k := by
  rw [arqpcStop_iff, arqpcData_zero]

/-- The Step-1 test of ARqpC with `c = 0`, `h = 0` is that of ARqp. -/
theorem arqpStop₁_arqpcData_zero_iff {k : ℕ} :
    arqpStop₁ P q ε (arqpcData f (0 : E → G) 0 p x σ) δ d k ↔
      arqpStop₁ P q ε (arqpData f p x σ) δ d k := by
  rw [arqpcData_zero]

/-- The ratio of ARqpC with `c = 0`, `h = 0` is that of ARqp. -/
theorem arqpRatio_zero {k : ℕ} :
    arqpRatio (fun y => f y + (0 : G → ℝ) ((0 : E → G) y)) (arqpcData f (0 : E → G) 0 p x σ) x s k =
      arqpRho f p x s σ k := by
  rw [add_zero_comp_zero, arqpcData_zero]

/-- For `h = 0` the halving set is `{j ≥ 2}`, together with `j = 1` when `X` is not convex. -/
theorem one_notMem_compositeHalvingSet_zero (hX : Convex ℝ X) :
    1 ∉ compositeHalvingSet (0 : G → ℝ) X :=
  one_notMem_compositeHalvingSet (convexOn_const 0 convex_univ) hX

/-- The detailed Step 2 of ARqpC with `c = 0`, `h = 0` is the detailed Step 2 for the ARqp model
`regularizedModel (ftaylorSeries ℝ f x) p σ` and its Taylor decrements. -/
theorem isARqpCDetailedStep_zero_iff {σ : ℝ} {x s : E} {δs : ℕ → ℝ} :
    IsARqpCDetailedStep f (0 : E → G) 0 X p q P ε J σ x s δs ↔
      IsDetailedStepOutput (regularizedModel (ftaylorSeries ℝ f x) p σ) {s | x + s ∈ X}
        (fun s => {d | x + s + d ∈ X}) (arqpDetailedModelDec (ftaylorSeries ℝ f x) p σ) q P.ς
        P.θ ε J s δs := by
  have em := compositeRegularizedModel_zero_fun (ftaylorSeries ℝ f x)
    (ftaylorSeries ℝ (0 : E → G) x) p σ
  have eΔ : (fun j s d => compositeModelDecrement (ftaylorSeries ℝ f x)
      (ftaylorSeries ℝ (0 : E → G) x) (0 : G → ℝ) p σ j s d) =
      arqpDetailedModelDec (ftaylorSeries ℝ f x) p σ := by
    funext j s d
    exact congrFun (compositeModelDecrement_zero_fun _ _ _ _ j s) d
  change IsDetailedStepOutput _ _ _ _ _ _ _ _ _ _ _ ↔ _
  rw [em, eΔ]

/-- **ARqp runs with the detailed Step 2 are ARqpC runs with `c = 0`, `h = 0`**: an ARqp run with
exact data on `X` whose Step-2 pairs are outputs of the detailed Step 2 for the ARqp model at every
iteration reaching Step 2. -/
theorem IsARqpCRun.of_isARqpRun_zero (hq : 1 ≤ q) (hqp : q ≤ p)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1)
    (hrun : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm)
    (hdet : ∀ k, (∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i) →
      ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d k →
      IsDetailedStepOutput (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k))
        {t | x k + t ∈ X} (fun t => {e | x k + t + e ∈ X})
        (arqpDetailedModelDec (ftaylorSeries ℝ f (x k)) p (σ k)) q P.ς P.θ ε J (s k) (δs k)) :
    IsARqpCRun f (0 : E → G) 0 X p q P J ε δ₀ x s σ δ δs d dm := by
  refine ⟨hq, hqp, hε, hδ₀, ?_, fun k hk h1 => isARqpCDetailedStep_zero_iff.2
    (hdet k (fun i hi => arqpcStop_zero_iff.not.1 (hk i hi))
      (arqpStop₁_arqpcData_zero_iff.not.1 h1))⟩
  rwa [add_zero_comp_zero, arqpcData_zero]

namespace IsARqpCRun

variable {C A : Set E} {L : ℕ → ℝ}

/-- **ARqpC with `c = 0`, `h = 0` is ARqp**: such a run is an ARqp run with exact data on `X`. -/
theorem isARqpRun_zero (hr : IsARqpCRun f (0 : E → G) 0 X p q P J ε δ₀ x s σ δ δs d dm) :
    IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm := by
  have h := hr.run
  rwa [add_zero_comp_zero, arqpcData_zero] at h

/-- `f` does not increase along the run up to its first termination index. -/
theorem antitone_zero (hr : IsARqpCRun f (0 : E → G) 0 X p q P J ε δ₀ x s σ δ δs d dm)
    {kε : ℕ} (hhit : IsFirstHit (arqpcStop f (0 : E → G) 0 P p q ε x s σ δ d) kε) :
    ∀ i j, i ≤ j → j ≤ kε → f (x j) ≤ f (x i) := by
  intro i j hij hj
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    exact (hr.isARqpRun_zero.objective_le fun l hl =>
      arqpcStop_zero_iff.not.1 (hhit.2 l (by omega))).trans (ih (by omega))

/-- The radius policy for `c = 0`: under `LipschitzDerivsAnchored f C A p p L` with jet bounds
`finMax 1 L p` on `A ⊇ {y ∈ X | f(y) ≤ f(x₀)}`, at every iteration reaching Step 2,
`δ_{s_k,j} ≥ κ_δ(σ_max) ε_j` for `j ∈ [1, q]` (`σ_max = arSigmaMax P (L p)`). -/
theorem arqpKappaDelta_mul_le_radius_zero
    (hr : IsARqpCRun f (0 : E → G) 0 X p q P J ε δ₀ x s σ δ δs d dm)
    (hf : LipschitzDerivsAnchored f C A p p L)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i)
    (h1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d k) :
    ∀ j ∈ Finset.Icc 1 q,
      arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ δs k j :=
  hr.arqpKappaDelta_mul_le_radius (Lw := L p) (Kw := finMax 1 L p) (Kf := finMax 1 L p)
    (Kc := 0) hf (LipschitzDerivsAnchored.zero_fun hf.isOpen hf.convex hf.subset)
    hasLipschitzConst_zero isSubadditive_zero rfl (by simp) (zero_le_one.trans one_le_finMax)
    le_rfl (by simp) one_le_finMax hjet (fun _ _ _ _ => by simp) hXC
    (fun y hy hy' => hA y hy (by simpa using hy'))
    (fun i hi => arqpcStop_zero_iff.not.2 (hk i hi)) (arqpStop₁_arqpcData_zero_iff.not.2 h1)

/-- **The radii after a successful iteration in either radii mode** (the hypothesis of
`IsARqpRun.decrease`): in mode `u` with `u → q = 1 ∧ 1 ∉ J` the radius of order `1` stays `1`;
in every case the radii are at least `κ_δ(σ_max) ε_j`. -/
theorem radii_zero (hr : IsARqpCRun f (0 : E → G) 0 X p q P J ε δ₀ x s σ δ δs d dm)
    (hf : LipschitzDerivsAnchored f C A p p L)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A) {u : Prop}
    (hu : u → q = 1 ∧ 1 ∉ J) {k : ℕ} (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i)
    (hs : P.η₁ ≤ arqpRho f p x s σ k) :
    (u → ∀ j ∈ Finset.Icc 1 q, δ (k + 1) j = 1) ∧
      (¬ u → 1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q,
        arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ δ (k + 1) j) := by
  have hrad : δ (k + 1) = δs k := (hr.isARqpRun_zero.radii k hk).1 hs
  have hk' : ∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i := fun i hi => hk i hi.le
  have h1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d k := fun h' => hk k le_rfl (Or.inl h')
  refine ⟨fun hu' j hj => ?_, fun _ => Or.inr fun j hj => ?_⟩
  · obtain ⟨hq1, h1J⟩ := hu hu'
    obtain rfl : j = 1 := by have := Finset.mem_Icc.1 hj; omega
    rw [hrad]
    exact hr.radius_eq_one (fun i hi => arqpcStop_zero_iff.not.2 (hk' i hi))
      (arqpStop₁_arqpcData_zero_iff.not.2 h1) h1J
  · rw [hrad]
    exact hr.arqpKappaDelta_mul_le_radius_zero hf hjet hXC hA hk' h1 j hj

/-- **Decrease with the exponents of the ARqp-SC row of (14.2.12)** ([cartis2022evaluation],
Lemma 14.2.2): under the hypotheses of `radii_zero`, `L_p ≥ 1` and `θ < ς`, every successful
iteration `k` not followed by termination decreases `f` by at least
`η₁ κ_{Δm} min_j ε_j^{π_j}`, `κ_{Δm} = arqpKappaDmOf u P L p q`, `π_j = arqpPiOf u p j`. -/
theorem decrease_zero (hr : IsARqpCRun f (0 : E → G) 0 X p q P J ε δ₀ x s σ δ δs d dm)
    (hf : LipschitzDerivsAnchored f C A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A) (hθς : P.θ < P.ς) {u : Prop}
    [Decidable u] (hu : u → q = 1 ∧ 1 ∉ J) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) (hs : P.η₁ ≤ arqpRho f p x s σ k)
    (h1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d (k + 1)) :
    P.η₁ * (arqpKappaDmOf u P L p q * finMin 1 (fun j => ε j ^ arqpPiOf u p j) q) ≤
      f (x k) - f (x (k + 1)) :=
  (IsARqpRun.decrease hf hL hXC hA hr.one_le_q hr.q_le_p hθς hr.ε_mem hr.isARqpRun_zero hk hs h1
    (hr.radii_zero hf hjet hXC hA hu hk hs)).2

/-- The radii of the run stay at least `κ_δ(σ_max) ε_j` if they start so (e.g. from `δ₀ = 1`),
under the hypotheses of `arqpKappaDelta_mul_le_radius_zero`. -/
theorem radius_ge_zero (hr : IsARqpCRun f (0 : E → G) 0 X p q P J ε δ₀ x s σ δ δs d dm)
    (hf : LipschitzDerivsAnchored f C A p p L)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q,
      arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ δ₀ j) :
    ∀ k, (∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i) → ∀ j ∈ Finset.Icc 1 q,
      arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ δ k j := by
  have hrun := hr.isARqpRun_zero
  intro k
  induction k with
  | zero => intro _ j hj; rw [hrun.delta_zero]; exact hδ₀ j hj
  | succ k ih =>
    intro hk j hj
    have hk' : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i := fun i hi => hk i (Nat.lt_succ_of_le hi)
    obtain ⟨hs, hu⟩ := hrun.radii k hk'
    by_cases hρ : P.η₁ ≤ arqpRho f p x s σ k
    · rw [hs hρ]
      exact hr.arqpKappaDelta_mul_le_radius_zero hf hjet hXC hA (fun i hi => hk' i hi.le)
        (fun h' => hk' k le_rfl (Or.inl h')) j hj
    · rw [(hu hρ).1]
      exact ih (fun i hi => hk' i hi.le) j hj

end IsARqpCRun

end Zero

/-! ### The constants of a call -/

section Constants

variable (P : ARqpParams) (L : ℕ → ℝ) (p q : ℕ)

/-- The decrease constant `κ_decr = η₁ κ_{Δm}` of a call (Lemma 14.2.2 of [cartis2022evaluation],
ARqpC-SC row with `c = 0`, `h = 0`, exponents `π_j = j + 1`), for constants `L` of the derivatives
of the objective: `κ_{Δm} = arqpcKappaDm P (L p) (finMax 1 L p) p q`. -/
noncomputable def arqpCallKappaDecr : ℝ :=
  P.η₁ * arqpcKappaDm P (L p) (finMax 1 L p) p q

/-- The constant `κ_unc = κ_uns + log(σ_max/σ₀)/log γ₂` bounding the number of iterations of a
call in excess of `κ_uns` times its successful ones (Lemma 14.2.3 of [cartis2022evaluation], with
`σ_max = arSigmaMax P (L p)`; the first `κ_uns` accounts for the last iteration of a call). -/
noncomputable def arqpCallKappaUnc : ℝ :=
  arqpKappaUns P + Real.log (arSigmaMax P.toARParams (L p) / P.σ₀) / Real.log P.γ₂

/-- The radius constant `κ_ρ = min(κ_δ(σ_max), 1/(4(3 L̄ + σ_max)))` of a call
(`L̄ = finMax 1 L p`): the radii certifying the output of a call are at least `κ_ρ ε_j`. -/
noncomputable def arqpCallKappaRad : ℝ :=
  min (arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)))
    (1 / (4 * (3 * finMax 1 L p + arSigmaMax P.toARParams (L p))))

variable {P L p q}

theorem arqpCallKappaUnc_nonneg (P : ARqpParams) (L : ℕ → ℝ) (p : ℕ) :
    0 ≤ arqpCallKappaUnc P L p := by
  unfold arqpCallKappaUnc
  have := arqpKappaUns_nonneg (P := P)
  have := P.log_γ₂_pos
  have : 0 ≤ Real.log (arSigmaMax P.toARParams (L p) / P.σ₀) :=
    Real.log_nonneg ((one_le_div P.σ₀_pos).2 (σ₀_le_arSigmaMax _ _))
  positivity

theorem arqpCallKappaDecr_pos (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς) (hL : 1 ≤ L p) :
    0 < arqpCallKappaDecr P L p q := by
  have hσ := arSigmaMax_pos P.toARParams (L p)
  have hκ : 0 < arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) :=
    arqpKappaDelta_pos P (zero_le_one.trans one_le_finMax) hσ
  have hb : 0 < (P.ς - P.θ) / ((q ! : ℝ) * (L p + arSigmaMax P.toARParams (L p))) *
      arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) ^ q / 3 := by
    have : 0 < P.ς - P.θ := by linarith
    have : 0 < L p + arSigmaMax P.toARParams (L p) := by linarith
    positivity
  rw [arqpCallKappaDecr, arqpcKappaDm_def]
  have := P.η₁_pos
  have := Real.rpow_pos_of_pos hb (((p : ℝ) + 1) / ((p : ℝ) - q + 1))
  positivity

theorem arqpCallKappaRad_pos : 0 < arqpCallKappaRad P L p := by
  have hσ := arSigmaMax_pos P.toARParams (L p)
  have hL1 : 1 ≤ finMax 1 L p := one_le_finMax
  refine lt_min (arqpKappaDelta_pos P (by linarith) hσ) ?_
  have : 0 < 4 * (3 * finMax 1 L p + arSigmaMax P.toARParams (L p)) := by positivity
  positivity

theorem arqpCallKappaRad_le_arqpKappaDelta :
    arqpCallKappaRad P L p ≤ arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) :=
  min_le_left _ _

/-- `κ_ρ ε_j ≤ min(1, ε_j/(4(3 J + σ)))` for `ε_j ∈ (0, 1]`, `1 ≤ J ≤ finMax 1 L p` and
`0 < σ ≤ σ_max`. -/
theorem arqpCallKappaRad_mul_le_min {εj J σ : ℝ} (hε : εj ∈ Ioc 0 1) (hJ1 : 1 ≤ J)
    (hJ : J ≤ finMax 1 L p) (hσ0 : 0 < σ) (hσ : σ ≤ arSigmaMax P.toARParams (L p)) :
    arqpCallKappaRad P L p * εj ≤ min 1 (εj / (4 * (3 * J + σ))) := by
  obtain ⟨hε0, hε1⟩ := hε
  have hrad1 : arqpCallKappaRad P L p ≤
      1 / (4 * (3 * finMax 1 L p + arSigmaMax P.toARParams (L p))) := min_le_right _ _
  have hK : 0 < 4 * (3 * J + σ) := by linarith
  have hK' : 4 * (3 * J + σ) ≤ 4 * (3 * finMax 1 L p + arSigmaMax P.toARParams (L p)) := by
    linarith
  have hKm : 0 < 4 * (3 * finMax 1 L p + arSigmaMax P.toARParams (L p)) := by linarith
  refine le_min ?_ ?_
  · calc arqpCallKappaRad P L p * εj
        ≤ 1 / (4 * (3 * finMax 1 L p + arSigmaMax P.toARParams (L p))) * 1 :=
          mul_le_mul hrad1 hε1 hε0.le (div_pos one_pos hKm).le
      _ ≤ 1 := by rw [mul_one, div_le_one hKm]; linarith
  · calc arqpCallKappaRad P L p * εj
        ≤ 1 / (4 * (3 * finMax 1 L p + arSigmaMax P.toARParams (L p))) * εj :=
          mul_le_mul_of_nonneg_right hrad1 hε0.le
      _ ≤ εj / (4 * (3 * J + σ)) := by
          rw [one_div_mul_eq_div]
          exact div_le_div_of_nonneg_left hε0.le hK hK'

theorem arqpCallKappaUnc_eq :
    arqpCallKappaUnc P L p =
      arqpKappaUns P + Real.log (arSigmaMax P.toARParams (L p) / P.σ₀) / Real.log P.γ₂ := rfl

end Constants

section Zero

variable {f : E → ℝ} {X : Set E} {p q : ℕ} {P : ARqpParams} {J : Set ℕ} {ε δ₀ : ℕ → ℝ}
  {x s : ℕ → E} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → E} {C A : Set E} {L : ℕ → ℝ}

/-- **Decrease with the exponents of the ARqpC-SC row of (14.2.12)** ([cartis2022evaluation],
Lemma 14.2.2 with `c = 0`, `h = 0`): under the hypotheses of `IsARqpCRun.decrease_zero`, every
successful iteration `k` not followed by termination decreases `f` by at least
`κ_decr ε_j^{j+1}` for some `j ∈ [1, q]` (`κ_decr = arqpCallKappaDecr P L p q`). -/
theorem IsARqpCRun.decrease_composite_zero
    (hr : IsARqpCRun f (0 : E → G) 0 X p q P J ε δ₀ x s σ δ δs d dm)
    (hf : LipschitzDerivsAnchored f C A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A) (hθς : P.θ < P.ς) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) (hs : P.η₁ ≤ arqpRho f p x s σ k)
    (h1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d (k + 1)) :
    ∃ j ∈ Finset.Icc 1 q, arqpCallKappaDecr P L p q * ε j ^ (j + 1) ≤ f (x k) - f (x (k + 1)) := by
  have hpol := (hr.radii_zero hf hjet hXC hA (u := False) (fun h => h.elim) hk hs).2 not_false
  obtain ⟨j, hj, -, hdec⟩ := hr.run.composite_decrease (Lw := L p) (Kw := finMax 1 L p) hf
    (LipschitzDerivsAnchored.zero_fun hf.isOpen hf.convex hf.subset) hasLipschitzConst_zero hL
    le_rfl (by simp) one_le_finMax hXC (fun z hz hz' => hA z hz (by simpa using hz'))
    hr.one_le_q hr.q_le_p hθς hr.ε_mem hr.δ₀_mem (fun i hi => arqpcStop_zero_iff.not.2 (hk i hi))
    (by rw [arqpRatio_zero]; exact hs) (arqpStop₁_arqpcData_zero_iff.not.2 h1) hpol
  refine ⟨j, hj, ?_⟩
  unfold arqpCallKappaDecr
  rw [mul_assoc]
  simpa using hdec

end Zero

/-- The jet bound `max(1, max_{i ∈ [2, p]} ‖∇^i f(y)‖)` at `y` (computable from the derivatives
that Step 1 of ARqp evaluates at `y`). -/
noncomputable def arqpJetBound (f : E → ℝ) (p : ℕ) (y : E) : ℝ :=
  finMax 1 (fun i => if i < p then ‖iteratedFDeriv ℝ (i + 1) f y‖ else 0) p

theorem one_le_arqpJetBound (f : E → ℝ) (p : ℕ) (y : E) : 1 ≤ arqpJetBound f p y :=
  le_finMax_left

/-- `arqpJetBound f p y ≤ finMax 1 L p` when `‖∇^i f(y)‖ ≤ finMax 1 L p` for `i ∈ [2, p]`. -/
theorem arqpJetBound_le {f : E → ℝ} {p : ℕ} {y : E} {M : ℝ} (hM : 1 ≤ M)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ‖iteratedFDeriv ℝ i f y‖ ≤ M) : arqpJetBound f p y ≤ M := by
  refine finMax_le hM fun i hi => ?_
  split_ifs with hip
  · exact hjet (i + 1) (Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hi).1; omega, by omega⟩)
  · exact zero_le_one.trans hM

/-- The jet bound bounds the derivatives `‖∇^i f(y)‖`, `i ∈ [2, p]`. -/
theorem norm_iteratedFDeriv_le_arqpJetBound (f : E → ℝ) {p : ℕ} (y : E) {i : ℕ}
    (hi : i ∈ Finset.Icc 2 p) : ‖iteratedFDeriv ℝ i f y‖ ≤ arqpJetBound f p y := by
  have hi' : i - 1 ∈ Finset.Icc 1 p := Finset.mem_Icc.2
    ⟨by have := (Finset.mem_Icc.1 hi).1; omega, by have := (Finset.mem_Icc.1 hi).2; omega⟩
  refine le_trans (le_of_eq ?_) (le_finMax hi')
  have hlt : i - 1 < p := by have := (Finset.mem_Icc.1 hi); omega
  simp only [hlt, ite_true]
  rw [Nat.sub_add_cancel (by have := (Finset.mem_Icc.1 hi).1; omega : 1 ≤ i)]

/-! ### Certificates at termination -/

section Certificate

variable {f : E → ℝ} {X : Set E} {p q : ℕ} {P : ARqpParams} {J : Set ℕ} {ε δ₀ : ℕ → ℝ}
  {x s : ℕ → E} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → E} {C A : Set E} {L : ℕ → ℝ}

/-- **The certificate at a Step-2 termination**: if Step 2 terminates at `k`, the radii
`min(1, ε_j/(4(3 J + σ_k)))`, `J = arqpJetBound f p x_k`, lie in `(0, 1]` and certify
`(ε, δ)`-approximate `q`-th order optimality at `x_k`, since `0` minimizes the model there. -/
theorem IsARqpCRun.isEpsDeltaApprox_of_stop₂_zero
    (hr : IsARqpCRun f (0 : E → G) 0 X p q P J ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i)
    (h1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d k) (h2 : arqpStop₂ (arqpData f p x σ) s k)
    (hcd : ContDiffAt ℝ p f (x k)) :
    (∀ j ∈ Finset.Icc 1 q, min 1 (ε j / (4 * (3 * arqpJetBound f p (x k) + σ k))) ∈ Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) {e | x k + e ∈ X} q ε
        (fun j => min 1 (ε j / (4 * (3 * arqpJetBound f p (x k) + σ k)))) := by
  have hrun := hr.isARqpRun_zero
  exact isEpsDeltaApprox_of_isMinOn_zero_of_jet (hrun.mem k hk) hcd
    (L := fun i => if i < p then ‖iteratedFDeriv ℝ (i + 1) f (x k)‖ else 0)
    (fun i hi => norm_iteratedFDeriv_le_arqpJetBound f (x k) hi) hr.q_le_p hr.ε_mem
    (hrun.toIsARRun.sigma_pos hk k le_rfl) ((hrun.step hk h1).isMinOn_of_eq h2)

/-- **The certificate of a terminating run with explicit radii**: under the hypotheses of
`IsARqpCRun.radius_ge_zero` with `δ₀ = 1`, at the first termination index `k_ε` there are radii
`δ_ε ∈ (0, 1]^q` with `δ_{ε,j} ≥ κ_ρ ε_j` (`κ_ρ = arqpCallKappaRad P L p`) certifying
`(ε, δ_ε)`-approximate `q`-th order optimality of `x_{k_ε}`. -/
theorem IsARqpCRun.exists_cert_zero
    (hr : IsARqpCRun f (0 : E → G) 0 X p q P J ε (fun _ => 1) x s σ δ δs d dm)
    (hf : LipschitzDerivsAnchored f C A p p L)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A) {kε : ℕ}
    (hhit : IsFirstHit (arqpcStop f (0 : E → G) 0 P p q ε x s σ δ d) kε) :
    ∃ δε : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δε j ∧ δε j ≤ 1) ∧
      (∀ j ∈ Finset.Icc 1 q, arqpCallKappaRad P L p * ε j ≤ δε j) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} q ε δε := by
  have hrun := hr.isARqpRun_zero
  have hk : ∀ i < kε, ¬ arqpStop f P p q ε x s σ δ d i :=
    fun i hi => arqpcStop_zero_iff.not.1 (hhit.2 i hi)
  have hstop : arqpStop f P p q ε x s σ δ d kε := arqpcStop_zero_iff.1 hhit.1
  have hε := hr.ε_mem
  have hσ := hrun.sigma_le_of_anchored hf hXC hA kε hk
  have hσ0 : 0 < σ kε := hrun.toIsARRun.sigma_pos hk kε le_rfl
  have hxA : x kε ∈ A := hA _ (hrun.mem kε hk) (hrun.mem_sublevel kε hk).2
  by_cases h1 : arqpStop₁ P q ε (arqpData f p x σ) δ d kε
  · refine ⟨δ kε, fun j hj => hrun.delta_mem hr.δ₀_mem kε hk j hj, fun j hj => ?_,
      MeasureTestPasses.isEpsDeltaApprox P.ς_pos (hrun.witness kε hk) h1⟩
    have hδ₀ : ∀ j ∈ Finset.Icc 1 q,
        arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ 1 :=
      fun j hj => by
        have h1 := arqpKappaDelta_lt_one P (one_le_finMax (L := L) (p := p))
          (arSigmaMax_pos P.toARParams (L p)).le
        have h2 := hε j hj
        have h3 := arqpKappaDelta_pos P (zero_le_one.trans (one_le_finMax (L := L) (p := p)))
          (arSigmaMax_pos P.toARParams (L p))
        nlinarith [h2.1, h2.2]
    exact (mul_le_mul_of_nonneg_right arqpCallKappaRad_le_arqpKappaDelta (hε j hj).1.le).trans
      (hr.radius_ge_zero hf hjet hXC hA hδ₀ kε hk j hj)
  · obtain ⟨hδ, hcert⟩ := hr.isEpsDeltaApprox_of_stop₂_zero hk h1 (hstop.resolve_left h1)
      (hf.contDiffAt _ (hf.subset hxA))
    exact ⟨_, hδ, fun j hj => arqpCallKappaRad_mul_le_min (hε j hj) (one_le_arqpJetBound f p _)
      (arqpJetBound_le one_le_finMax fun i hi => hjet i hi _ hxA) hσ0 hσ.2, hcert⟩

end Certificate

/-! ### Terminating calls and their cost -/

section Output

variable {f : E → ℝ} {X : Set E} {p q : ℕ} {P : ARqpParams} {ε : ℕ → ℝ} {C A : Set E}
  {L : ℕ → ℝ}

variable (G) in
/-- `(y, δ)` is the output of a call `INNER(f, X, q, x^S, ε)` realized by ARqp-SC: `y` is the
first termination iterate of an ARqpC run with `c = 0 : E → G`, `h = 0`, the halving set
`compositeHalvingSet 0 X` and initial radii `1` on `f` from `x^S`, and the radii `δ ∈ (0, 1]^q`
certify `(ε, δ)`-approximate `q`-th order optimality at `y` over `X`. -/
def IsARqpOutput (f : E → ℝ) (X : Set E) (p q : ℕ) (P : ARqpParams) (ε : ℕ → ℝ) (xS y : E)
    (δ : ℕ → ℝ) : Prop :=
  (∃ (x s : ℕ → E) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E) (kε : ℕ),
    IsARqpCRun f (0 : E → G) 0 X p q P (compositeHalvingSet (0 : G → ℝ) X) ε (fun _ => 1) x s σ
      δ δs d dm ∧
    IsFirstHit (arqpcStop f (0 : E → G) 0 P p q ε x s σ δ d) kε ∧ x 0 = xS ∧ x kε = y) ∧
  (∀ j ∈ Finset.Icc 1 q, 0 < δ j ∧ δ j ≤ 1) ∧
  IsEpsDeltaApprox (ftaylorSeries ℝ f y) {e | y + e ∈ X} q ε δ

variable (G) in
/-- `(y, δ)` is the output of a call (as in `IsARqpOutput`) whose run uses `nF` evaluations of `f`
and `nD` evaluations of its derivatives (`funEvalCount` and `derivEvalCount` at its first
termination index). -/
def IsARqpOutputCost (f : E → ℝ) (X : Set E) (p q : ℕ) (P : ARqpParams) (ε : ℕ → ℝ)
    (xS y : E) (δ : ℕ → ℝ) (nF nD : ℕ) : Prop :=
  (∃ (x s : ℕ → E) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E) (kε : ℕ),
    IsARqpCRun f (0 : E → G) 0 X p q P (compositeHalvingSet (0 : G → ℝ) X) ε (fun _ => 1) x s σ
      δ δs d dm ∧
    IsFirstHit (arqpcStop f (0 : E → G) 0 P p q ε x s σ δ d) kε ∧
    x 0 = xS ∧ x kε = y ∧ nF = funEvalCount kε ∧
    nD = derivEvalCount (fun k => P.η₁ ≤ arqpRatio (fun y => f y + (0 : G → ℝ) ((0 : E → G) y))
      (arqpcData f (0 : E → G) 0 p x σ) x s k) kε) ∧
  (∀ j ∈ Finset.Icc 1 q, 0 < δ j ∧ δ j ≤ 1) ∧
  IsEpsDeltaApprox (ftaylorSeries ℝ f y) {e | y + e ∈ X} q ε δ

namespace IsARqpOutput

variable {xS y : E} {δ : ℕ → ℝ}

/-- The output is feasible. -/
theorem mem (h : IsARqpOutput G f X p q P ε xS y δ) : y ∈ X := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, -, rfl⟩, -⟩ := h
  exact hr.mem hhit.2

/-- A call does not increase `f`. -/
theorem le (h : IsARqpOutput G f X p q P ε xS y δ) : f y ≤ f xS := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, rfl, rfl⟩, -⟩ := h
  exact hr.antitone_zero hhit 0 kε (Nat.zero_le _) le_rfl

/-- The output radii lie in `(0, 1]`. -/
theorem radius_mem (h : IsARqpOutput G f X p q P ε xS y δ) :
    ∀ j ∈ Finset.Icc 1 q, 0 < δ j ∧ δ j ≤ 1 := h.2.1

/-- The output radii certify `(ε, δ)`-approximate optimality at the output. -/
theorem isEpsDeltaApprox (h : IsARqpOutput G f X p q P ε xS y δ) :
    IsEpsDeltaApprox (ftaylorSeries ℝ f y) {e | y + e ∈ X} q ε δ := h.2.2

end IsARqpOutput

namespace IsARqpOutputCost

variable {xS y : E} {δ : ℕ → ℝ} {nF nD : ℕ}

theorem isARqpOutput (h : IsARqpOutputCost G f X p q P ε xS y δ nF nD) :
    IsARqpOutput G f X p q P ε xS y δ := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, h0, hy, -, -⟩, hδ, happ⟩ := h
  exact ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, h0, hy⟩, hδ, happ⟩

/-- The tolerances of a call lie in `(0, 1]`. -/
theorem ε_mem (h : IsARqpOutputCost G f X p q P ε xS y δ nF nD) :
    ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1 := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, -⟩, -⟩ := h
  exact hr.ε_mem

theorem one_le_q (h : IsARqpOutputCost G f X p q P ε xS y δ nF nD) : 1 ≤ q := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, -⟩, -⟩ := h
  exact hr.one_le_q

theorem q_le_p (h : IsARqpOutputCost G f X p q P ε xS y δ nF nD) : q ≤ p := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, -⟩, -⟩ := h
  exact hr.q_le_p

/-- A call evaluates `f` and its derivatives at least once. -/
theorem one_le (h : IsARqpOutputCost G f X p q P ε xS y δ nF nD) : 1 ≤ nF ∧ 1 ≤ nD := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, -, -, -, -, rfl, rfl⟩, -, -⟩ := h
  simp [derivEvalCount, funEvalCount]

/-- **The cost of a terminating call, ARqpC-SC row** ([cartis2022evaluation], Theorem 14.2.4
with `c = 0`, `h = 0`, `π_j = j + 1`): for `f ≥ f_low` on `X`,
`LipschitzDerivsAnchored f C A p p L` with `X ⊆ C`, `L_p ≥ 1`, jet bounds `finMax 1 L p` on
`A ⊇ {y ∈ X | f(y) ≤ f(x^S)}`, `σ_min > 0` and `θ < ς`, the call uses at most
`κ_uns (f(x^S) - f_low)/(κ_decr m_ε) + κ_C` evaluations of `f` and
`(f(x^S) - f_low)/(κ_decr m_ε) + 2` evaluations of its derivatives, where
`m_ε = min_j ε_j^{j+1}`, `κ_decr = arqpCallKappaDecr P L p q` and `κ_C = kappaCARqp P L p`. -/
theorem cost_le {flow : ℝ} (h : IsARqpOutputCost G f X p q P ε xS y δ nF nD)
    (hb : ∀ z ∈ X, flow ≤ f z) (hf : LipschitzDerivsAnchored f C A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ z ∈ A, ‖iteratedFDeriv ℝ i f z‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ z ∈ X, f z ≤ f xS → z ∈ A) (hσmin : 0 < P.σmin)
    (hθς : P.θ < P.ς) :
    (nF : ℝ) ≤ arqpKappaUns P * ((f xS - flow) /
        (arqpCallKappaDecr P L p q * finMin 1 (fun j => ε j ^ (j + 1)) q)) + kappaCARqp P L p ∧
      (nD : ℝ) ≤ (f xS - flow) /
        (arqpCallKappaDecr P L p q * finMin 1 (fun j => ε j ^ (j + 1)) q) + 2 := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, hx0, -, rfl, rfl⟩, -, -⟩ := h
  subst hx0
  have hε := hr.ε_mem
  set mε := finMin 1 (fun j => ε j ^ (j + 1)) q
  have hmε0 : 0 < mε := finMin_pos one_pos fun j hj => pow_pos (hε j hj).1 _
  obtain ⟨kε', hhit', -, hF', hD'⟩ := hr.complexity (Lw := L p) (Kw := finMax 1 L p)
    (Kf := finMax 1 L p) (Kc := 0) hf
    (LipschitzDerivsAnchored.zero_fun hf.isOpen hf.convex hf.subset)
    hasLipschitzConst_zero isSubadditive_zero rfl hL le_rfl (by simp)
    (zero_le_one.trans one_le_finMax) le_rfl (by simp) one_le_finMax hjet
    (fun _ _ _ _ => by simp) hXC
    (fun z hz hz' => hA z hz (by simpa using hz')) hθς hσmin (wlow := flow)
    (fun z hz => by simpa using hb z hz) hmε0 (fun j hj => finMin_le hj)
  obtain rfl := hhit'.unique hhit
  have e0 : f (x 0) + (0 : G → ℝ) ((0 : E → G) (x 0)) - flow = f (x 0) - flow := by simp
  have e1 : P.η₁ * (arqpcKappaDm P (L p) (finMax 1 L p) p q * mε) =
      arqpCallKappaDecr P L p q * mε := by
    unfold arqpCallKappaDecr; ring
  rw [e0, e1] at hF' hD'
  exact ⟨hF', hD'⟩

/-- **The cost of a terminating call, ARqp-SC row** ([cartis2022evaluation], Theorem 14.2.4 for
ARqp-SC, in radii mode `u` with `u → q = 1 ∧ X` convex): under the hypotheses of `cost_le`, the
call uses at most `κ^a (f(x^S) - f_low)/m_ε + κ^c` evaluations of `f` and
`κ^s (f(x^S) - f_low)/m_ε + 2` evaluations of its derivatives, where
`m_ε = min_j ε_j^{π_j}`, `π_j = arqpPiOf u p j`, `κ^a = kappaAARqpOf u P L p q`,
`κ^s = kappaSARqpOf u P L p q` and `κ^c = kappaCARqp P L p`. -/
theorem cost_le_arqp {flow : ℝ} (h : IsARqpOutputCost G f X p q P ε xS y δ nF nD)
    (hb : ∀ z ∈ X, flow ≤ f z) (hf : LipschitzDerivsAnchored f C A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ z ∈ A, ‖iteratedFDeriv ℝ i f z‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ z ∈ X, f z ≤ f xS → z ∈ A) (hσmin : 0 < P.σmin)
    (hθς : P.θ < P.ς) {u : Prop} [Decidable u] (hu : u → q = 1 ∧ Convex ℝ X) :
    (nF : ℝ) ≤ kappaAARqpOf u P L p q * (f xS - flow) /
        finMin 1 (fun j => ε j ^ arqpPiOf u p j) q + kappaCARqp P L p ∧
      (nD : ℝ) ≤ kappaSARqpOf u P L p q * (f xS - flow) /
        finMin 1 (fun j => ε j ^ arqpPiOf u p j) q + 2 := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, hx0, -, rfl, rfl⟩, -, -⟩ := h
  subst hx0
  have hrun := hr.isARqpRun_zero
  obtain ⟨kε', hhit', hF', hD'⟩ := hrun.exists_isFirstHit_of_anchored hb hf hL hXC hA
    hr.one_le_q hr.q_le_p hσmin hθς hr.ε_mem (u := u) fun k hk hs =>
      hr.radii_zero hf hjet hXC hA
        (fun hu' => ⟨(hu hu').1, one_notMem_compositeHalvingSet_zero (hu hu').2⟩)
        (fun i hi => hk i (by omega)) hs
  have hhit'' : IsFirstHit (arqpStop f P p q ε x s σ δ d) kε :=
    ⟨arqpcStop_zero_iff.1 hhit.1, fun i hi => arqpcStop_zero_iff.not.1 (hhit.2 i hi)⟩
  obtain rfl := hhit'.unique hhit''
  have e : (fun k => P.η₁ ≤ arqpRatio (fun y => f y + (0 : G → ℝ) ((0 : E → G) y))
      (arqpcData f (0 : E → G) 0 p x σ) x s k) = fun k => P.η₁ ≤ arqpRho f p x s σ k :=
    funext fun k => by rw [arqpRatio_zero]
  rw [e]
  exact ⟨hF', hD'⟩

end IsARqpOutputCost

variable (G) in
/-- **Terminating calls exist**: in finite dimension, for a closed `X`, `x^S ∈ X`, `f ≥ f_low` on
`X`, `LipschitzDerivsAnchored f C A p p L` with `X ⊆ C`, jet bounds `finMax 1 L p` on
`A ⊇ {y ∈ X | f(y) ≤ f(x^S)}`, `σ_min > 0`, `θ < ς`, `1 ≤ q ≤ p` and `ε ∈ (0, 1]^q`, there is a
terminating call from `x^S`, with radii at least `κ_ρ ε_j`. -/
theorem exists_isARqpOutputCost [FiniteDimensional ℝ E] {flow : ℝ} (hX : IsClosed X) {xS : E}
    (hxS : xS ∈ X) (hb : ∀ y ∈ X, flow ≤ f y) (hf : LipschitzDerivsAnchored f C A p p L)
    (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f xS → y ∈ A) (P : ARqpParams) (hσmin : 0 < P.σmin)
    (hθς : P.θ < P.ς) (hq : 1 ≤ q) (hqp : q ≤ p) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) :
    ∃ (y : E) (δ : ℕ → ℝ) (nF nD : ℕ), IsARqpOutputCost G f X p q P ε xS y δ nF nD ∧
      ∀ j ∈ Finset.Icc 1 q, arqpCallKappaRad P L p * ε j ≤ δ j := by
  obtain ⟨x, s, σ, δ, δs, d, dm, hx0, hr⟩ := exists_isARqpCRun_compositeHalvingSet
    (f := f) (c := (0 : E → G)) (p := p) hasLipschitzConst_zero isSubadditive_zero rfl P hq hqp
    hε (δ₀ := fun _ => 1) (fun _ _ => ⟨one_pos, le_rfl⟩) hX hxS
  subst hx0
  have hmε0 : 0 < finMin 1 (fun j => ε j ^ (j + 1)) q :=
    finMin_pos one_pos fun j hj => pow_pos (hε j hj).1 _
  obtain ⟨kε, hhit, -, -, -⟩ := hr.complexity (Lw := L p) (Kw := finMax 1 L p)
    (Kf := finMax 1 L p) (Kc := 0) hf
    (LipschitzDerivsAnchored.zero_fun hf.isOpen hf.convex hf.subset)
    hasLipschitzConst_zero isSubadditive_zero rfl hL le_rfl (by simp)
    (zero_le_one.trans one_le_finMax) le_rfl (by simp) one_le_finMax hjet
    (fun _ _ _ _ => by simp) hXC
    (fun z hz hz' => hA z hz (by simpa using hz')) hθς hσmin (wlow := flow)
    (fun z hz => by simpa using hb z hz) hmε0 (fun j hj => finMin_le hj)
  obtain ⟨δε, hδε, hrad, happ⟩ := hr.exists_cert_zero hf hjet hXC hA hhit
  exact ⟨x kε, δε, _, _, ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, rfl, rfl, rfl, rfl⟩, hδε, happ⟩,
    hrad⟩

end Output

/-! ### Calls cut by the outer method -/

section CallOut

variable {f : E → ℝ} {X : Set E} {p q : ℕ} {P : ARqpParams} {ε : ℕ → ℝ} {C A : Set E}
  {L : ℕ → ℝ}

variable (G) in
/-- **A call of ARqp-SC with its returned radii** ([cartis2022evaluation], Algorithm 14.1.1 with
`c = 0`, `h = 0` used as INNER, e.g. in Algorithm 14.3.2): the points `xi 0, …, xi e` are the first
`e + 1` iterates of an ARqpC run with `c = 0 : E → G`, `h = 0`, the halving set
`compositeHalvingSet 0 X` and initial radii `1` on `f`, whose first termination index `k_ε` is at
least `e` (the call may be cut before termination); `succ i` holds for `i < e` exactly when
iteration `i` of the run is successful, and the returned radii `δo` are
* the current radii `δ_e` (at a Step-1 termination these are certifying radii);
* or, whenever Step 2 is computed at `e`, the Step-2 radii `δ_{s_e}`;
* or, at a Step-2 termination (`e = k_ε`), the radii `min(1, ε_j/(4(3 J + σ_e)))`,
  `J = arqpJetBound f p x_e`, which certify `(ε, δo)`-approximate optimality at `x_e`
  (`IsARqpCRun.isEpsDeltaApprox_of_stop₂_zero`). -/
def IsARqpCallOut (f : E → ℝ) (X : Set E) (p q : ℕ) (P : ARqpParams) (ε : ℕ → ℝ)
    (xi : ℕ → E) (e : ℕ) (succ : ℕ → Prop) (δo : ℕ → ℝ) : Prop :=
  ∃ (x s : ℕ → E) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E) (kε : ℕ),
    IsARqpCRun f (0 : E → G) 0 X p q P (compositeHalvingSet (0 : G → ℝ) X) ε (fun _ => 1) x s σ
      δ δs d dm ∧
    IsFirstHit (arqpcStop f (0 : E → G) 0 P p q ε x s σ δ d) kε ∧
    e ≤ kε ∧ (∀ i ≤ e, xi i = x i) ∧
    (∀ i < e, (succ i ↔ P.η₁ ≤ arqpRatio (fun y => f y + (0 : G → ℝ) ((0 : E → G) y))
      (arqpcData f (0 : E → G) 0 p x σ) x s i)) ∧
    ((∀ j ∈ Finset.Icc 1 q, δo j = δ e j) ∨
      (¬ arqpStop₁ P q ε (arqpcData f (0 : E → G) 0 p x σ) δ d e ∧
        ∀ j ∈ Finset.Icc 1 q, δo j = δs e j) ∨
      (e = kε ∧ ¬ arqpStop₁ P q ε (arqpcData f (0 : E → G) 0 p x σ) δ d e ∧
        ∀ j ∈ Finset.Icc 1 q, δo j = min 1 (ε j / (4 * (3 * arqpJetBound f p (x e) + σ e)))))

namespace IsARqpCallOut

variable {xi : ℕ → E} {e : ℕ} {succ : ℕ → Prop} {δo : ℕ → ℝ}

/-- `f` does not increase along a call. -/
theorem antitone (h : IsARqpCallOut G f X p q P ε xi e succ δo) :
    ∀ i < e, f (xi (i + 1)) ≤ f (xi i) := by
  obtain ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he, hxi, -, -⟩ := h
  intro i hi
  rw [hxi i (by omega), hxi (i + 1) (by omega)]
  exact hr.antitone_zero hhit i (i + 1) (by omega) (by omega)

/-- Unsuccessful iterations of a call do not move. -/
theorem eq_of_not_succ (h : IsARqpCallOut G f X p q P ε xi e succ δo) :
    ∀ i < e, ¬ succ i → xi (i + 1) = xi i := by
  obtain ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he, hxi, hsucc, hδo⟩ := h
  have hrun := hr.isARqpRun_zero
  have hnot : ∀ i < e, ¬ arqpStop f P p q ε x s σ δ d i :=
    fun i hi => arqpcStop_zero_iff.not.1 (hhit.2 i (by omega))
  have hsucc' : ∀ i < e, (succ i ↔ P.η₁ ≤ arqpRho f p x s σ i) := fun i hi => by
    rw [hsucc i hi, arqpRatio_zero]
  intro i hi hs
  rw [hxi i hi.le, hxi (i + 1) hi]
  exact hrun.toIsARRun.eq_of_not_succ (fun l hl => hnot l (by omega))
    (not_le.1 ((hsucc' i hi).not.1 hs))

open Classical in
/-- **The number of iterations of a call** ([cartis2022evaluation], Lemma 14.2.3):
`e ≤ κ_uns |𝒮| + κ_unc`, `𝒮` the successful iterations of the call, for an objective with
`LipschitzDerivsAnchored f C A p p L`, `X ⊆ C`, on a set `A` containing the sublevel set of `f`
at the start of the call. -/
theorem le_count (h : IsARqpCallOut G f X p q P ε xi e succ δo)
    (hf : LipschitzDerivsAnchored f C A p p L) (hXC : X ⊆ C)
    (hA : ∀ y ∈ X, f y ≤ f (xi 0) → y ∈ A) :
    (e : ℝ) ≤ arqpKappaUns P * ((Finset.range e).filter succ).card + arqpCallKappaUnc P L p := by
  obtain ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he, hxi, hsucc, hδo⟩ := h
  have hrun := hr.isARqpRun_zero
  have hnot : ∀ i < e, ¬ arqpStop f P p q ε x s σ δ d i :=
    fun i hi => arqpcStop_zero_iff.not.1 (hhit.2 i (by omega))
  have hsucc' : ∀ i < e, (succ i ↔ P.η₁ ≤ arqpRho f p x s σ i) := fun i hi => by
    rw [hsucc i hi, arqpRatio_zero]
  rw [hxi 0 (Nat.zero_le _)] at hA
  have h3 := hrun.toIsARRun.le_succ_count (k := e) hnot
    (hrun.sigma_le_of_anchored hf hXC hA e hnot).2
  set ρ := fun i => P.η₁ ≤ arqpRho f p x s σ i
  have hS' : (Finset.range e).filter succ = (Finset.range e).filter ρ :=
    Finset.filter_congr fun i hi => hsucc' i (Finset.mem_range.1 hi)
  have hcard' := card_successSet_le_card_filter_add_one ρ e
  have hκ := arqpKappaUns_nonneg (P := P)
  rw [hS', arqpCallKappaUnc_eq]
  rw [arqpKappaUns_eq] at hκ ⊢
  nlinarith

/-- **The decrease of a call, ARqpC-SC row** ([cartis2022evaluation], Lemma 14.2.2): under the
hypotheses of `le_count`, `L_p ≥ 1`, jet bounds `finMax 1 L p` on `A` and `θ < ς`, every
successful iteration `i < e` that is not the last one, or that is the last one of a call ending
at a point failing the test of `(ε, δo)`-approximate optimality, decreases `f` by at least
`κ_decr ε_l^{l+1}` for some `l`. -/
theorem decrease (h : IsARqpCallOut G f X p q P ε xi e succ δo)
    (hf : LipschitzDerivsAnchored f C A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (xi 0) → y ∈ A) (hθς : P.θ < P.ς) :
    ∀ i < e, succ i → (i + 1 < e ∨ ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (xi e))
        {d | xi e + d ∈ X} q ε δo) →
      ∃ l ∈ Finset.Icc 1 q, arqpCallKappaDecr P L p q * ε l ^ (l + 1) ≤
        f (xi i) - f (xi (i + 1)) := by
  obtain ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he, hxi, hsucc, hδo⟩ := h
  have hrun := hr.isARqpRun_zero
  have hnot : ∀ i < e, ¬ arqpStop f P p q ε x s σ δ d i :=
    fun i hi => arqpcStop_zero_iff.not.1 (hhit.2 i (by omega))
  have hsucc' : ∀ i < e, (succ i ↔ P.η₁ ≤ arqpRho f p x s σ i) := fun i hi => by
    rw [hsucc i hi, arqpRatio_zero]
  rw [hxi 0 (Nat.zero_le _)] at hA
  have hns : ∀ i < e, (i + 1 < e ∨ ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (xi e))
      {d | xi e + d ∈ X} q ε δo) → ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d (i + 1) := by
    intro i hi hcont h1
    by_cases hlt : i + 1 < e
    · exact hnot (i + 1) hlt (Or.inl h1)
    · have htest := hcont.resolve_left hlt
      have hie : i + 1 = e := by omega
      rw [hie] at h1
      rcases hδo with hδo | ⟨hn, -⟩ | ⟨-, hn, -⟩
      · refine htest fun j hj => ?_
        have happ := MeasureTestPasses.isEpsDeltaApprox P.ς_pos (hrun.witness e hnot) h1
        rw [hxi e le_rfl, hδo j hj]
        exact happ j hj
      · exact hn (arqpStop₁_arqpcData_zero_iff.2 h1)
      · exact hn (arqpStop₁_arqpcData_zero_iff.2 h1)
  intro i hi hs hcont
  obtain ⟨l, hl, hdec⟩ := hr.decrease_composite_zero hf hL hjet hXC hA hθς
    (fun l hl => hnot l (by omega)) ((hsucc' i hi).1 hs) (hns i hi hcont)
  refine ⟨l, hl, ?_⟩
  rw [hxi i hi.le, hxi (i + 1) hi]
  exact hdec

/-- **The decrease of a call, ARqp-SC row** ([cartis2022evaluation], Lemma 14.2.2): as
`decrease`, with the decrease `η₁ κ_{Δm} ε_l^{π_l}` of the ARqp-SC row in a radii mode `u` with
`u → q = 1 ∧ X` convex (`π_l = arqpPiOf u p l`). -/
theorem decrease_arqp (h : IsARqpCallOut G f X p q P ε xi e succ δo)
    (hf : LipschitzDerivsAnchored f C A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (xi 0) → y ∈ A) (hθς : P.θ < P.ς) {u : Prop} [Decidable u]
    (hu : u → q = 1 ∧ Convex ℝ X) :
    ∀ i < e, succ i →
      (i + 1 < e ∨ ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (xi e)) {d | xi e + d ∈ X} q ε δo) →
      ∃ l ∈ Finset.Icc 1 q, P.η₁ * arqpKappaDmOf u P L p q * ε l ^ arqpPiOf u p l ≤
        f (xi i) - f (xi (i + 1)) := by
  obtain ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he, hxi, hsucc, hδo⟩ := h
  have hrun := hr.isARqpRun_zero
  have hnot : ∀ i < e, ¬ arqpStop f P p q ε x s σ δ d i :=
    fun i hi => arqpcStop_zero_iff.not.1 (hhit.2 i (by omega))
  have hsucc' : ∀ i < e, (succ i ↔ P.η₁ ≤ arqpRho f p x s σ i) := fun i hi => by
    rw [hsucc i hi, arqpRatio_zero]
  rw [hxi 0 (Nat.zero_le _)] at hA
  have hq := hr.one_le_q
  have hε := hr.ε_mem
  have hns : ∀ i < e, (i + 1 < e ∨ ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (xi e))
      {d | xi e + d ∈ X} q ε δo) → ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d (i + 1) := by
    intro i hi hcont h1
    by_cases hlt : i + 1 < e
    · exact hnot (i + 1) hlt (Or.inl h1)
    · have htest := hcont.resolve_left hlt
      have hie : i + 1 = e := by omega
      rw [hie] at h1
      rcases hδo with hδo | ⟨hn, -⟩ | ⟨-, hn, -⟩
      · refine htest fun j hj => ?_
        have happ := MeasureTestPasses.isEpsDeltaApprox P.ς_pos (hrun.witness e hnot) h1
        rw [hxi e le_rfl, hδo j hj]
        exact happ j hj
      · exact hn (arqpStop₁_arqpcData_zero_iff.2 h1)
      · exact hn (arqpStop₁_arqpcData_zero_iff.2 h1)
  intro i hi hs hcont
  have hdec := hr.decrease_zero hf hL hjet hXC hA hθς
    (fun hu' => ⟨(hu hu').1, one_notMem_compositeHalvingSet_zero (hu hu').2⟩)
    (fun l hl => hnot l (by omega)) ((hsucc' i hi).1 hs) (hns i hi hcont)
  obtain ⟨l, hl, hmin⟩ := exists_finMin_eq hq
    (u := fun j => ε j ^ arqpPiOf u p j) (b := 1) fun j hj =>
      Real.rpow_le_one (hε j hj).1.le (hε j hj).2 (arqpPiOf_nonneg u p j)
  refine ⟨l, hl, ?_⟩
  rw [hmin] at hdec
  rw [hxi i hi.le, hxi (i + 1) hi, mul_assoc]
  exact hdec

/-- **The returned radii of a call** (the radius policy of Algorithm 14.1.2): under the
hypotheses of `le_count` and jet bounds `finMax 1 L p` on `A`, the returned radii are at least
`κ_ρ ε_j`. -/
theorem radius_ge (h : IsARqpCallOut G f X p q P ε xi e succ δo)
    (hf : LipschitzDerivsAnchored f C A p p L)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (xi 0) → y ∈ A) :
    ∀ j ∈ Finset.Icc 1 q, arqpCallKappaRad P L p * ε j ≤ δo j := by
  obtain ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he, hxi, hsucc, hδo⟩ := h
  have hrun := hr.isARqpRun_zero
  have hnot : ∀ i < e, ¬ arqpStop f P p q ε x s σ δ d i :=
    fun i hi => arqpcStop_zero_iff.not.1 (hhit.2 i (by omega))
  have hsucc' : ∀ i < e, (succ i ↔ P.η₁ ≤ arqpRho f p x s σ i) := fun i hi => by
    rw [hsucc i hi, arqpRatio_zero]
  rw [hxi 0 (Nat.zero_le _)] at hA
  have hε := hr.ε_mem
  intro j hj
  have hκε := mul_le_mul_of_nonneg_right (arqpCallKappaRad_le_arqpKappaDelta (P := P) (L := L)
    (p := p)) (hε j hj).1.le
  have hδ₀ : ∀ j ∈ Finset.Icc 1 q,
      arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ 1 :=
    fun j hj => by
      have h1 := arqpKappaDelta_lt_one P (one_le_finMax (L := L) (p := p))
        (arSigmaMax_pos P.toARParams (L p)).le
      have h2 := hε j hj
      have h3 := arqpKappaDelta_pos P (zero_le_one.trans (one_le_finMax (L := L) (p := p)))
        (arSigmaMax_pos P.toARParams (L p))
      nlinarith [h2.1, h2.2]
  rcases hδo with hδo | ⟨hn, hδo⟩ | ⟨-, -, hδo⟩
  · rw [hδo j hj]
    exact hκε.trans (hr.radius_ge_zero hf hjet hXC hA hδ₀ e hnot j hj)
  · rw [hδo j hj]
    exact hκε.trans (hr.arqpKappaDelta_mul_le_radius_zero hf hjet hXC hA hnot
      (arqpStop₁_arqpcData_zero_iff.not.1 hn) j hj)
  · rw [hδo j hj]
    have hxA : x e ∈ A := hA _ (hrun.mem e hnot) (hrun.mem_sublevel e hnot).2
    exact arqpCallKappaRad_mul_le_min (hε j hj) (one_le_arqpJetBound f p _)
      (arqpJetBound_le one_le_finMax fun i hi => hjet i hi _ hxA)
      (hrun.toIsARRun.sigma_pos hnot e le_rfl) (hrun.sigma_le_of_anchored hf hXC hA e hnot).2

open Classical in
/-- **The contract of one call** ([cartis2022evaluation], Lemmas 14.2.2 and 14.2.3 for ARqp-SC,
and the radius policy of Algorithm 14.1.2), bundling `eq_of_not_succ`, `le_count`, `decrease`,
`decrease_arqp` and `radius_ge` (the form used by the two-phase analysis). -/
theorem contract (h : IsARqpCallOut G f X p q P ε xi e succ δo)
    (hf : LipschitzDerivsAnchored f C A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (xi 0) → y ∈ A) (hθς : P.θ < P.ς) :
    (∀ i < e, ¬ succ i → xi (i + 1) = xi i) ∧
    (e : ℝ) ≤ arqpKappaUns P * ((Finset.range e).filter succ).card + arqpCallKappaUnc P L p ∧
    (∀ i < e, succ i → (i + 1 < e ∨ ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (xi e))
        {d | xi e + d ∈ X} q ε δo) →
      ∃ l ∈ Finset.Icc 1 q, arqpCallKappaDecr P L p q * ε l ^ (l + 1) ≤
        f (xi i) - f (xi (i + 1))) ∧
    (∀ (u : Prop) [Decidable u], (u → q = 1 ∧ Convex ℝ X) → ∀ i < e, succ i →
      (i + 1 < e ∨ ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (xi e)) {d | xi e + d ∈ X} q ε δo) →
      ∃ l ∈ Finset.Icc 1 q, P.η₁ * arqpKappaDmOf u P L p q * ε l ^ arqpPiOf u p l ≤
        f (xi i) - f (xi (i + 1))) ∧
    (∀ j ∈ Finset.Icc 1 q, arqpCallKappaRad P L p * ε j ≤ δo j) :=
  ⟨h.eq_of_not_succ, h.le_count hf hXC hA, h.decrease hf hL hjet hXC hA hθς,
    fun _ _ hu => h.decrease_arqp hf hL hjet hXC hA hθς hu, h.radius_ge hf hjet hXC hA⟩

end IsARqpCallOut

variable (G) in
open Classical in
/-- **Calls stopped by an external test exist**: in finite dimension, under the hypotheses of
`exists_isARqpOutputCost` and for any test `stop` on points, there is a call from `x₀`
(`IsARqpCallOut`) cut at the first iterate satisfying `stop` or at the termination of the run,
whichever comes first. Its iterates stay in `X`, do not increase `f`, the returned radii lie in
`(0, 1]`, and at the last iterate either `stop` holds or the returned radii certify
`(ε, δo)`-approximate `q`-th order optimality. -/
theorem exists_isARqpCallOut_of_stop [FiniteDimensional ℝ E] {flow : ℝ} (hX : IsClosed X)
    {x₀ : E} (hx₀ : x₀ ∈ X) (hb : ∀ y ∈ X, flow ≤ f y) (hf : LipschitzDerivsAnchored f C A p p L)
    (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) (P : ARqpParams) (hσmin : 0 < P.σmin)
    (hθς : P.θ < P.ς) (hq : 1 ≤ q) (hqp : q ≤ p) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (stop : E → Prop) :
    ∃ (xi : ℕ → E) (e : ℕ) (succ : ℕ → Prop) (δo : ℕ → ℝ),
      IsARqpCallOut G f X p q P ε xi e succ δo ∧ xi 0 = x₀ ∧ xi e ∈ X ∧
      (∀ j ∈ Finset.Icc 1 q, 0 < δo j ∧ δo j ≤ 1) ∧
      (∀ i < e, f (xi (i + 1)) ≤ f (xi i)) ∧ (∀ i ≤ e, f (xi i) ≤ f x₀) ∧
      (∀ i < e, ¬ stop (xi i)) ∧
      (stop (xi e) ∨ IsEpsDeltaApprox (ftaylorSeries ℝ f (xi e)) {d | xi e + d ∈ X} q ε δo) := by
  obtain ⟨x, s, σ, δ, δs, d, dm, hx0, hr⟩ := exists_isARqpCRun_compositeHalvingSet
    (f := f) (c := (0 : E → G)) (p := p) hasLipschitzConst_zero isSubadditive_zero rfl P hq hqp
    hε (δ₀ := fun _ => 1) (fun _ _ => ⟨one_pos, le_rfl⟩) hX hx₀
  have hA' : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A := by rw [hx0]; exact hA
  have hmε0 : 0 < finMin 1 (fun j => ε j ^ (j + 1)) q :=
    finMin_pos one_pos fun j hj => pow_pos (hε j hj).1 _
  obtain ⟨kε, hhit, -, -, -⟩ := hr.complexity (Lw := L p) (Kw := finMax 1 L p)
    (Kf := finMax 1 L p) (Kc := 0) hf
    (LipschitzDerivsAnchored.zero_fun hf.isOpen hf.convex hf.subset)
    hasLipschitzConst_zero isSubadditive_zero rfl hL le_rfl (by simp)
    (zero_le_one.trans one_le_finMax) le_rfl (by simp) one_le_finMax hjet
    (fun _ _ _ _ => by simp) hXC
    (fun z hz hz' => hA' z hz (by simpa using hz')) hθς hσmin (wlow := flow)
    (fun z hz => by simpa using hb z hz) hmε0 (fun j hj => finMin_le hj)
  have hrun := hr.isARqpRun_zero
  have hmono := hr.antitone_zero hhit
  have hmem : ∀ i ≤ kε, x i ∈ X := fun i hi => hr.mem fun l hl => hhit.2 l (hl.trans_le hi)
  have hex : ∃ i, i = kε ∨ stop (x i) := ⟨kε, Or.inl rfl⟩
  set e := Nat.find hex with he
  have he_le : e ≤ kε := Nat.find_min' hex (Or.inl rfl)
  have hnot : ∀ i < e, ¬ arqpStop f P p q ε x s σ δ d i :=
    fun i hi => arqpcStop_zero_iff.not.1 (hhit.2 i (by omega))
  have hstop : ∀ i < e, ¬ stop (x i) := fun i hi => (not_or.1 (Nat.find_min hex hi)).2
  have hmono' : ∀ i < e, f (x (i + 1)) ≤ f (x i) := fun i hi =>
    hmono i (i + 1) (by omega) (by omega)
  have hle : ∀ i ≤ e, f (x i) ≤ f x₀ := fun i hi => hx0 ▸ hmono 0 i (Nat.zero_le _) (by omega)
  have hsucc : ∀ i < e, ((fun i => P.η₁ ≤ arqpRatio (fun y => f y + (0 : G → ℝ) ((0 : E → G) y))
      (arqpcData f (0 : E → G) 0 p x σ) x s i) i ↔ P.η₁ ≤ arqpRatio
        (fun y => f y + (0 : G → ℝ) ((0 : E → G) y)) (arqpcData f (0 : E → G) 0 p x σ) x s i) :=
    fun _ _ => Iff.rfl
  by_cases hcase : e < kε ∨ arqpStop₁ P q ε (arqpData f p x σ) δ d e
  · -- the current radii
    refine ⟨x, e, fun i => P.η₁ ≤ arqpRatio (fun y => f y + (0 : G → ℝ) ((0 : E → G) y))
      (arqpcData f (0 : E → G) 0 p x σ) x s i, δ e,
      ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he_le, fun _ _ => rfl, hsucc,
        Or.inl fun _ _ => rfl⟩, hx0, hmem e he_le,
      fun j hj => hrun.delta_mem hr.δ₀_mem e hnot j hj, hmono', hle, hstop, ?_⟩
    rcases hcase with hlt | h1
    · rcases Nat.find_spec hex with hek | hst
      · exact absurd hek (by omega)
      · exact Or.inl hst
    · exact Or.inr (MeasureTestPasses.isEpsDeltaApprox P.ς_pos (hrun.witness e hnot) h1)
  · -- a Step-2 termination: the radii certified by the minimality of the model at `0`
    push Not at hcase
    obtain ⟨hke, h1⟩ := hcase
    have hek : e = kε := le_antisymm he_le hke
    have hstopk : arqpStop f P p q ε x s σ δ d e := arqpcStop_zero_iff.1 (hek ▸ hhit.1)
    have hxA : x e ∈ A := hA' _ (hrun.mem e hnot) (hrun.mem_sublevel e hnot).2
    obtain ⟨hδ, hcert⟩ := hr.isEpsDeltaApprox_of_stop₂_zero hnot h1 (hstopk.resolve_left h1)
      (hf.contDiffAt _ (hf.subset hxA))
    exact ⟨x, e, fun i => P.η₁ ≤ arqpRatio (fun y => f y + (0 : G → ℝ) ((0 : E → G) y))
      (arqpcData f (0 : E → G) 0 p x σ) x s i,
      fun j => min 1 (ε j / (4 * (3 * arqpJetBound f p (x e) + σ e))),
      ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he_le, fun _ _ => rfl, hsucc,
        Or.inr (Or.inr ⟨hek, arqpStop₁_arqpcData_zero_iff.not.2 h1, fun _ _ => rfl⟩)⟩, hx0,
      hmem e he_le, hδ, hmono', hle, hstop, Or.inr hcert⟩

end CallOut

/-! ### Calls of ARqp with unit radii on the whole space

For `X = E` and `q ≤ 2`, the detailed Step 2 of Algorithm 12.2.3 keeps the radii `1` at the orders
`j ≤ 2` (`exists_isARqpRun`) and an ARqp run never terminates in Step 2
(`IsARqpRun.arqpStop₁_of_isFirstHit_of_le_two`), so the radii `1` certify the output of a call;
the analysis is that of the unit-radius mode of ARqp (exponents `π_j = (p+1)/(p-j+1)`). -/

section Unit

variable {f : E → ℝ} {p q : ℕ} {P : ARqpParams} {ε : ℕ → ℝ} {A : Set E} {L : ℕ → ℝ}

/-- **ARqp runs on the whole space with unit radii terminate**: in finite dimension, for
`1 ≤ q ≤ min(2, p)`, `ε ∈ (0, 1]^q`, `σ_min > 0`, `θ < ς`, `f ≥ f_low`, and
`LipschitzDerivsAnchored f univ A p p L` with `L_p ≥ 1` and jet bounds `finMax 1 L p` on a set
`A ⊇ {y | f(y) ≤ f(x^S)}`, there is an ARqp run with exact data from `x^S` with initial radii `1`
whose Step-2 radii are `1` before termination; it terminates at some `k_ε`, does not increase `f`,
and the radii `1` certify `(ε, 1)`-approximate `q`-th order optimality at `x_{k_ε}`. -/
theorem exists_isARqpRun_unit [FiniteDimensional ℝ E] {flow : ℝ} (hb : ∀ y, flow ≤ f y)
    (hf : LipschitzDerivsAnchored f univ A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (P : ARqpParams) (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς) (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hqp : q ≤ p) (xS : E) (hA : ∀ y, f y ≤ f xS → y ∈ A)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) :
    ∃ (x s : ℕ → E) (σ : ℕ → ℝ) (δr δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E) (kε : ℕ),
      IsARqpRun f univ P q ε (fun _ => 1) (arqpData f p x σ) x s σ δr δs d dm ∧
      (∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δr d i) →
        ∀ j ∈ Finset.Icc 1 q, δs k j = 1) ∧
      IsFirstHit (arqpStop f P p q ε x s σ δr d) kε ∧
      x 0 = xS ∧ (∀ i j, i ≤ j → j ≤ kε → f (x j) ≤ f (x i)) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ (univ : Set E)} q ε
        (fun _ => 1) := by
  have hp : 1 ≤ p := hq.trans hqp
  have hδ₀ : ∀ j ∈ Finset.Icc 1 q, (0 : ℝ) < (fun _ => (1 : ℝ)) j ∧ (fun _ => (1 : ℝ)) j ≤ 1 :=
    fun _ _ => ⟨one_pos, le_rfl⟩
  obtain ⟨x, s, σ, δr, δs, d, dm, h0, h, hrad⟩ := exists_isARqpRun f P hp hqp
    (fun j hj => (hε j hj).1) hδ₀ (fun y => ∑ i ∈ Finset.Icc 2 p, ‖iteratedFDeriv ℝ i f y‖)
    (fun _ => by positivity) (fun y i hi => Finset.single_le_sum
      (f := fun i => ‖iteratedFDeriv ℝ i f y‖) (fun _ _ => norm_nonneg _) hi) xS
  have hδs : ∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δr d i) →
      ∀ j ∈ Finset.Icc 1 q, δs k j = 1 := fun k hk j hj =>
    (hrad k (fun i hi => hk i hi.le)).1 j hj ((Finset.mem_Icc.1 hj).2.trans hq2)
  obtain ⟨kε, hhit, -, -, -, -⟩ := IsARqpRun.complexity (X := univ) (C := univ)
    (fun y _ => hb y) hf hL hjet (subset_univ _) (fun y _ hy => hA y (h0 ▸ hy)) hq hqp hσmin hθς
    hε hδ₀ h (u := True) ⟨fun _ => ⟨fun _ _ => rfl, hδs⟩, fun h' => absurd trivial h'⟩
  have h1 : arqpStop₁ P q ε (arqpData f p x σ) δr d kε :=
    h.arqpStop₁_of_isFirstHit_of_le_two (hf.contDiffAt _ (mem_univ _)) hqp hε hδ₀ hhit hq2
  have hone := h.delta_eq_one (fun _ _ => rfl) hδs kε hhit.2
  have hcert := MeasureTestPasses.isEpsDeltaApprox P.ς_pos (h.witness kε hhit.2) h1
  refine ⟨x, s, σ, δr, δs, d, dm, kε, h, hδs, hhit, h0, ?_, fun j hj => ?_⟩
  · intro i j hij hj
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih =>
      exact (h.objective_le fun l hl => hhit.2 l (by omega)).trans (ih (by omega))
  · have := hcert j hj
    rwa [hone j hj] at this

/-- `(y, δ)` is the output of a call `INNER(f, E, q, x^S, ε)` realized by ARqp on the whole space
with unit radii, using `nF` evaluations of `f` and `nD` of its derivatives: `y` is the first
termination iterate of an ARqp run with exact data from `x^S` with initial radii `1` whose Step-2
radii are `1` before termination, and the radii `δ = 1` certify `(ε, δ)`-approximate optimality at
`y`. -/
def IsARqpUnitOutputCost (f : E → ℝ) (p q : ℕ) (P : ARqpParams) (ε : ℕ → ℝ) (xS y : E)
    (δ : ℕ → ℝ) (nF nD : ℕ) : Prop :=
  (∃ (x s : ℕ → E) (σ : ℕ → ℝ) (δr δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E) (kε : ℕ),
    IsARqpRun f univ P q ε (fun _ => 1) (arqpData f p x σ) x s σ δr δs d dm ∧
    (∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δr d i) → ∀ j ∈ Finset.Icc 1 q, δs k j = 1) ∧
    IsFirstHit (arqpStop f P p q ε x s σ δr d) kε ∧
    x 0 = xS ∧ x kε = y ∧ nF = funEvalCount kε ∧
    nD = derivEvalCount (fun k => P.η₁ ≤ arqpRho f p x s σ k) kε) ∧
  (∀ j ∈ Finset.Icc 1 q, δ j = 1) ∧
  IsEpsDeltaApprox (ftaylorSeries ℝ f y) {e | y + e ∈ (univ : Set E)} q ε δ

/-- **Terminating unit-radius calls exist**, under the hypotheses of `exists_isARqpRun_unit`. -/
theorem exists_isARqpUnitOutputCost [FiniteDimensional ℝ E] {flow : ℝ} (hb : ∀ y, flow ≤ f y)
    (hf : LipschitzDerivsAnchored f univ A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (P : ARqpParams) (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς) (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hqp : q ≤ p) (xS : E) (hA : ∀ y, f y ≤ f xS → y ∈ A)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) :
    ∃ (y : E) (nF nD : ℕ), IsARqpUnitOutputCost f p q P ε xS y (fun _ => 1) nF nD := by
  obtain ⟨x, s, σ, δr, δs, d, dm, kε, h, hδs, hhit, h0, -, hcert⟩ :=
    exists_isARqpRun_unit hb hf hL hjet P hσmin hθς hq hq2 hqp xS hA hε
  exact ⟨x kε, _, _, ⟨x, s, σ, δr, δs, d, dm, kε, h, hδs, hhit, h0, rfl, rfl, rfl⟩,
    fun _ _ => rfl, hcert⟩

namespace IsARqpUnitOutputCost

variable {xS y : E} {δ : ℕ → ℝ} {nF nD : ℕ}

/-- A call does not increase `f`. -/
theorem le (h : IsARqpUnitOutputCost f p q P ε xS y δ nF nD) : f y ≤ f xS := by
  obtain ⟨⟨x, s, σ, δr, δs, d, dm, kε, hr, -, hhit, rfl, rfl, -, -⟩, -⟩ := h
  have : ∀ j ≤ kε, f (x j) ≤ f (x 0) := by
    intro j hj
    induction j with
    | zero => exact le_rfl
    | succ j ih =>
      exact (hr.objective_le fun l hl => hhit.2 l (by omega)).trans (ih (by omega))
  exact this kε le_rfl

/-- The output radii are `1`. -/
theorem radius_eq_one (h : IsARqpUnitOutputCost f p q P ε xS y δ nF nD) :
    ∀ j ∈ Finset.Icc 1 q, δ j = 1 := h.2.1

/-- The output radii certify `(ε, δ)`-approximate optimality at the output. -/
theorem isEpsDeltaApprox (h : IsARqpUnitOutputCost f p q P ε xS y δ nF nD) :
    IsEpsDeltaApprox (ftaylorSeries ℝ f y) {e | y + e ∈ (univ : Set E)} q ε δ := h.2.2

/-- **The cost of a unit-radius call** ([cartis2022evaluation], Theorem 12.2.14 in the unit-radius
mode): for `f ≥ f_low`, `LipschitzDerivsAnchored f univ A p p L` with `L_p ≥ 1` and jet bounds
`finMax 1 L p` on `A ⊇ {y | f(y) ≤ f(x^S)}`, `σ_min > 0`, `θ < ς`, `1 ≤ q ≤ p` and
`ε ∈ (0, 1]^q`, the call uses at most `κ^a (f(x^S) - f_low)/min_j ε_j^{π_j} + κ^c` evaluations
of `f` and `κ^s (f(x^S) - f_low)/min_j ε_j^{π_j} + 2` of its derivatives, with the unit-radius
exponents `π_j = arqpPiOf True p j`. -/
theorem cost_le {flow : ℝ} (h : IsARqpUnitOutputCost f p q P ε xS y δ nF nD)
    (hb : ∀ y, flow ≤ f y) (hf : LipschitzDerivsAnchored f univ A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hA : ∀ y, f y ≤ f xS → y ∈ A) (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς) (hq : 1 ≤ q)
    (hqp : q ≤ p) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) :
    (nF : ℝ) ≤ kappaAARqpOf True P L p q * (f xS - flow) /
        finMin 1 (fun j => ε j ^ arqpPiOf True p j) q + kappaCARqp P L p ∧
      (nD : ℝ) ≤ kappaSARqpOf True P L p q * (f xS - flow) /
        finMin 1 (fun j => ε j ^ arqpPiOf True p j) q + 2 := by
  obtain ⟨⟨x, s, σ, δr, δs, d, dm, kε, hr, hδs, hhit, hx0, -, rfl, rfl⟩, -, -⟩ := h
  subst hx0
  obtain ⟨kε', hhit', -, -, hF', hD'⟩ := IsARqpRun.complexity (X := univ) (C := univ)
    (fun y _ => hb y) hf hL hjet (subset_univ _) (fun y _ hy => hA y hy) hq hqp hσmin hθς hε
    (fun _ _ => ⟨one_pos, le_rfl⟩) hr (u := True)
    ⟨fun _ => ⟨fun _ _ => rfl, hδs⟩, fun h' => absurd trivial h'⟩
  obtain rfl := hhit'.unique hhit
  exact ⟨hF', hD'⟩

end IsARqpUnitOutputCost

/-- The iterates `x_0, …, x_e` and successful iterations of a call of ARqp on the whole space with
unit radii: the first `e + 1` iterates of an ARqp run with exact data, initial radii `1` and
Step-2 radii `1` before termination, whose first termination index is at least `e`. -/
def IsARqpUnitCall (f : E → ℝ) (p q : ℕ) (P : ARqpParams) (ε : ℕ → ℝ) (xi : ℕ → E) (e : ℕ)
    (succ : ℕ → Prop) : Prop :=
  ∃ (x s : ℕ → E) (σ : ℕ → ℝ) (δr δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E) (kε : ℕ),
    IsARqpRun f univ P q ε (fun _ => 1) (arqpData f p x σ) x s σ δr δs d dm ∧
    (∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δr d i) → ∀ j ∈ Finset.Icc 1 q, δs k j = 1) ∧
    IsFirstHit (arqpStop f P p q ε x s σ δr d) kε ∧
    e ≤ kε ∧ (∀ i ≤ e, xi i = x i) ∧
    ∀ i < e, (succ i ↔ P.η₁ ≤ arqpRho f p x s σ i)

/-- A unit-radius call returning the radii `1`. -/
def IsARqpUnitCallOut (f : E → ℝ) (p q : ℕ) (P : ARqpParams) (ε : ℕ → ℝ) (xi : ℕ → E) (e : ℕ)
    (succ : ℕ → Prop) (δo : ℕ → ℝ) : Prop :=
  IsARqpUnitCall f p q P ε xi e succ ∧ ∀ j ∈ Finset.Icc 1 q, δo j = 1

namespace IsARqpUnitCallOut

variable {xi : ℕ → E} {e : ℕ} {succ : ℕ → Prop} {δo : ℕ → ℝ}

/-- The returned radii are `1`. -/
theorem radius_eq_one (h : IsARqpUnitCallOut f p q P ε xi e succ δo) :
    ∀ j ∈ Finset.Icc 1 q, δo j = 1 := h.2

/-- `f` does not increase along a unit-radius call. -/
theorem antitone (h : IsARqpUnitCallOut f p q P ε xi e succ δo) :
    ∀ i < e, f (xi (i + 1)) ≤ f (xi i) := by
  obtain ⟨⟨x, s, σ, δr, δs, d, dm, kε, hr, -, hhit, he, hxi, -⟩, -⟩ := h
  intro i hi
  rw [hxi i hi.le, hxi (i + 1) hi]
  exact hr.objective_le fun l hl => hhit.2 l (by omega)

open Classical in
/-- **The contract of one unit-radius call** ([cartis2022evaluation], Lemmas 12.2.13 and 14.2.3
with unit radii), for `LipschitzDerivsAnchored f univ A p p L` with `L_p ≥ 1` on a set `A`
containing the sublevel set of `f` at the start of the call, `θ < ς` and `1 ≤ q ≤ p`:
unsuccessful iterations do not move, `e ≤ κ_uns |𝒮| + κ_unc`, and, for tolerances in `(0, 1]`,
every successful iteration that is not the last one, or the last one of a call ending at a point
failing the test with radii `1`, decreases `f` by at least `η₁ κ_{Δm} ε_l^{π_l}` with the
unit-radius exponents `π_l = (p+1)/(p-l+1)`. -/
theorem contract (h : IsARqpUnitCallOut f p q P ε xi e succ δo)
    (hf : LipschitzDerivsAnchored f univ A p p L) (hL : 1 ≤ L p)
    (hA : ∀ y, f y ≤ f (xi 0) → y ∈ A) (hθς : P.θ < P.ς) (hq : 1 ≤ q) (hqp : q ≤ p) :
    (∀ i < e, ¬ succ i → xi (i + 1) = xi i) ∧
    (e : ℝ) ≤ arqpKappaUns P * ((Finset.range e).filter succ).card + arqpCallKappaUnc P L p ∧
    ((∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) → ∀ i < e, succ i →
      (i + 1 < e ∨ ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (xi e))
        {d | xi e + d ∈ (univ : Set E)} q ε δo) →
      ∃ l ∈ Finset.Icc 1 q, P.η₁ * arqpKappaDmOf True P L p q * ε l ^ arqpPiOf True p l ≤
        f (xi i) - f (xi (i + 1))) := by
  obtain ⟨⟨x, s, σ, δr, δs, d, dm, kε, hr, hδs, hhit, he, hxi, hsucc⟩, hδo⟩ := h
  have hAμ : ∀ y ∈ (univ : Set E), f y ≤ f (x 0) → y ∈ A := fun y _ hy =>
    hA y (by rwa [hxi 0 (Nat.zero_le _)])
  have hone := hr.delta_eq_one (fun _ _ => rfl) hδs
  have hnot : ∀ i < e, ¬ arqpStop f P p q ε x s σ δr d i :=
    fun i hi => hhit.2 i (lt_of_lt_of_le hi he)
  refine ⟨fun i hi hs => ?_, ?_, fun hε i hi hs hcont => ?_⟩
  · rw [hxi i hi.le, hxi (i + 1) hi]
    exact hr.toIsARRun.eq_of_not_succ (fun l hl => hnot l (lt_of_le_of_lt hl hi))
      (not_le.1 ((hsucc i hi).not.1 hs))
  · have h3 := hr.toIsARRun.le_succ_count (k := e) hnot
      (hr.sigma_le_of_anchored hf (subset_univ _) hAμ e hnot).2
    set ρ := fun i => P.η₁ ≤ arqpRho f p x s σ i
    have hS' : (Finset.range e).filter succ = (Finset.range e).filter ρ :=
      Finset.filter_congr fun i hi => hsucc i (Finset.mem_range.1 hi)
    have hcard' := card_successSet_le_card_filter_add_one ρ e
    have hκ := arqpKappaUns_nonneg (P := P)
    rw [hS', arqpCallKappaUnc_eq]
    rw [arqpKappaUns_eq] at hκ ⊢
    nlinarith
  · have h1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δr d (i + 1) := by
      intro h1
      by_cases hlt : i + 1 < e
      · exact hnot (i + 1) hlt (Or.inl h1)
      · have hie : i + 1 = e := by omega
        rw [hie] at h1
        refine (hcont.resolve_left hlt) fun j hj => ?_
        have happ := MeasureTestPasses.isEpsDeltaApprox P.ς_pos (hr.witness e hnot) h1
        rw [hxi e le_rfl, hδo j hj, ← hone e hnot j hj]
        exact happ j hj
    have hdec := (IsARqpRun.decrease hf hL (subset_univ _) hAμ hq hqp hθς hε hr
      (k := i) (fun l hl => hnot l (by omega)) ((hsucc i hi).1 hs) h1 (u := True)
      ⟨fun _ => hone (i + 1) (fun l hl => hnot l (by omega)), fun h' => absurd trivial h'⟩).2
    obtain ⟨l, hl, hmin⟩ := exists_finMin_eq hq
      (u := fun j => ε j ^ arqpPiOf True p j) (b := 1) fun j hj =>
        Real.rpow_le_one (hε j hj).1.le (hε j hj).2 (arqpPiOf_nonneg True p j)
    refine ⟨l, hl, ?_⟩
    rw [hmin] at hdec
    rw [hxi i hi.le, hxi (i + 1) hi, mul_assoc]
    exact hdec

end IsARqpUnitCallOut

open Classical in
/-- **Unit-radius calls stopped by an external test exist**: under the hypotheses of
`exists_isARqpRun_unit` and for any test `stop` on points, there is a unit-radius call from `x₀`
cut at the first iterate satisfying `stop` or at the termination of the run. Its iterates do not
increase `f`, and at the last iterate either `stop` holds or the radii `1` certify
`(ε, 1)`-approximate `q`-th order optimality. -/
theorem exists_isARqpUnitCallOut_of_stop [FiniteDimensional ℝ E] {flow : ℝ}
    (hb : ∀ y, flow ≤ f y) (hf : LipschitzDerivsAnchored f univ A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (P : ARqpParams) (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς) (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hqp : q ≤ p) (x₀ : E) (hA : ∀ y, f y ≤ f x₀ → y ∈ A)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (stop : E → Prop) :
    ∃ (xi : ℕ → E) (e : ℕ) (succ : ℕ → Prop),
      IsARqpUnitCallOut f p q P ε xi e succ (fun _ => 1) ∧ xi 0 = x₀ ∧
      (∀ i < e, f (xi (i + 1)) ≤ f (xi i)) ∧ (∀ i ≤ e, f (xi i) ≤ f x₀) ∧
      (∀ i < e, ¬ stop (xi i)) ∧
      (stop (xi e) ∨ IsEpsDeltaApprox (ftaylorSeries ℝ f (xi e)) {d | xi e + d ∈ (univ : Set E)}
        q ε (fun _ => 1)) := by
  obtain ⟨x, s, σ, δr, δs, d, dm, kε, hr, hδs, hhit, hx0, hmono, hcert⟩ :=
    exists_isARqpRun_unit hb hf hL hjet P hσmin hθς hq hq2 hqp x₀ hA hε
  have hex : ∃ i, i = kε ∨ stop (x i) := ⟨kε, Or.inl rfl⟩
  set e := Nat.find hex with he
  have he_le : e ≤ kε := Nat.find_min' hex (Or.inl rfl)
  refine ⟨x, e, fun i => P.η₁ ≤ arqpRho f p x s σ i,
    ⟨⟨x, s, σ, δr, δs, d, dm, kε, hr, hδs, hhit, he_le, fun _ _ => rfl, fun _ _ => Iff.rfl⟩,
      fun _ _ => rfl⟩, hx0, fun i hi => hmono i (i + 1) (by omega) (by omega),
    fun i hi => hx0 ▸ hmono 0 i (Nat.zero_le _) (by omega),
    fun i hi => (not_or.1 (Nat.find_min hex hi)).2, ?_⟩
  rcases Nat.find_spec hex with hek | hst
  · right
    rw [show e = kε from hek]
    exact hcert
  · exact Or.inl hst

end Unit

end Optimization
