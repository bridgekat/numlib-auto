import NumlibSurface.CartisGouldToint.Chapter14.Section03

/-!
# Cartis–Gould–Toint §14.3: LENq-SC and TPqp-GC under the anchored assumptions

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §14.3.2: existence and evaluation
complexity of the LENq-SC (Theorem 14.3.4) and TPqp-GC (Theorem 14.3.9) runs with INNER = ARqp-SC
under the book's *anchored* smoothness assumptions, Φ₂.D1pLaB.X for LENq-SC and f.D1pLB.X,
c.D1pLB.X (with f.B.Fb) for TPqp-GC, in place of the global Lipschitz assumptions of
`exists_algorithm_14_3_1_complexity` and `exists_algorithm_14_3_2_complexity`.

The ARqpC-SC analysis of §14.1 holds under `AnchoredCompositeBounds` on the sublevel set of the
objective at the starting point (`theorem_14_1_10_ii_anchored`, `lemma_14_1_9_anchored`,
`sigma_le_arqpcSigmaMax_anchored`): the models are built at iterates, which stay in the sublevel
set, and the trial points are related to them by Taylor's theorem with the Lipschitz condition
anchored at the iterate (the book's remark after (14.2.10)). The trial points need not lie in the
sublevel set, only in `X ⊆ X₀`; no bound on the step lengths is needed. Lemma 14.3.6 provides the
anchored bounds for `ν = ½ ‖c‖²` on `𝓛_ν(x₀)` and for `μ(·, t)` on `𝓛_μ(t)`, with constants
independent of `t`; each INNER call of Phase 1 (resp. Phase 2) starts in `𝓛_ν(x₀)` (resp. at a
point with `‖r(x, t)‖ ≤ ε₀ ≤ 1`), so its sublevel set lies in that set.

## Main definitions

* `anchoredConst L B`: the constants `max(L_j, B_{j+1})` in which f.D1pLaB.X (constants `L`, `B`)
  gives `AnchoredCompositeBounds`.

## Main results

* `anchoredCompositeBounds_zeroCon_of`, `anchoredCompositeBounds_zeroCon`,
  `AssumptionD1qLaBX.anchoredCompositeBounds`: f.D1pLaB.X (or its parts used by the analysis)
  gives the anchored bounds of the ARqpC-SC analysis for INNER (`c = 0`, `h = 0`) on the sublevel
  set;
* `exists_algorithm_14_3_1_complexity_anchored`: Theorem 14.3.4 for constructed LENq-SC runs
  under Φ₂.D1pLaB.X;
* `exists_anchoredCompositeBounds_nu_mu`: c.D1pLB.X and f.D1pLB.X give, through Lemma 14.3.6, the
  anchored bounds of `ν` on `𝓛_ν(x₀)` and of `μ(·, t)` on `𝓛_μ(t)` (constants independent of `t`)
  assumed by the anchored TPqp-GC theorems of `Chapter14.Section03`;
* `exists_algorithm_14_3_2_complexity_anchored'` (explicit anchored bounds for `ν` and `μ`) and
  `exists_algorithm_14_3_2_complexity_anchored` (from c.D1pLB.X and f.D1pLB.X through
  Lemma 14.3.6, with constants depending only on the data and `‖c(x₀)‖`): Theorem 14.3.9 for
  constructed TPqp-GC runs.

The constructions and INNER contracts used here are proved in `Chapter14.Section03` under
`AnchoredCompositeBounds` (`theorem_14_2_4_arqpc_anchored`, `IsARqpSCOutputCost.cost_le_anchored`,
`lenq_core_anchored`, `exists_isTPqpGCPhase2_isInnerPhaseRun_anchored`,
`exists_algorithm_14_3_2_of_phase2_anchored`, `phase1_cost_le_anchored`); the global versions of
that module are their instances. The certified, strong-contract, ARqp-SC-exponent and
unit-radius variants are proved there under anchored bounds as well
(`exists_algorithm_14_3_2_complexity_certified_anchored`,
`exists_algorithm_14_3_2_complexity_strong_anchored`,
`exists_algorithm_14_3_1_complexity_arqp_anchored`,
`exists_algorithm_14_3_2_complexity_arqp_anchored`
and their `_add` forms, `exists_algorithm_14_3_1_complexity_unit_anchored`,
`exists_algorithm_14_3_2_complexity_unit_anchored`); their hypotheses follow from the book's
assumptions by `AssumptionD1qLaBX.anchoredCompositeBounds` (LENq-SC) and
`exists_anchoredCompositeBounds_nu_mu` (TPqp-GC).

## Deviations from the book

* As in `exists_algorithm_14_3_1_complexity` and `exists_algorithm_14_3_2_complexity`, INNER is
  ARqp-SC run as ARqpC-SC with `c = 0`, `h = 0`, whose contracts are proved with the exponents
  `π_j = j + 1` of the ARqpC-SC row of (14.2.12); `X` is closed and `q ≥ 1`; `∑_j` replaces
  `max_j` in Theorem 14.3.4; the number of bad outer iterations of Phase 2 is a parameter of the
  conclusion of Theorem 14.3.9 (see `exists_algorithm_14_3_2_complexity`).
* f.D1pLaB.X with constants `L`, `B` is used through the constants `max(L_j, B_{j+1})`
  (`anchoredConst`): the analysis of ARqpC bounds the jets `‖∇^i f(x_k)‖` (`i ≥ 2`) by the
  constants of order `i - 1`. Only the Lipschitz condition at order `p` and the derivative bounds
  at orders `2, …, p` are used.
* TPqp-GC: for Phase 2, Lemma 14.3.6 (ii) gives bounds on `𝓛_μ(t) = {‖r(x, t)‖ ≤ 1}`, which
  contains the sublevel sets of the INNER calls because `‖r(x_k, t_k)‖ ≤ ε₀ ≤ 1`; no f.B.Fb is
  needed for the contract, only for the counting argument of Theorem 14.3.9.
-/

open Set Metric
open scoped Nat

namespace CartisGouldToint.Chapter14

variable {n m : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

set_option hygiene false in
local notation "ℝᵐ" => EuclideanSpace ℝ (Fin m)

/-! ### Anchored bounds for the objective of INNER -/

/-- The constants `max(L_j, B_{j+1})`: if `∇^j F` is `L_j`-Lipschitz anchored on `S` and
`‖∇^j F‖ ≤ B_j` on `S`, then the anchored bounds of the ARqpC analysis
(`AnchoredCompositeBounds`, which bounds `‖∇^i F‖` by the constant of order `i - 1`) hold with
these constants. -/
noncomputable def anchoredConst (L B : ℕ → ℝ) : ℕ → ℝ := fun j => max (L j) (B (j + 1))

theorem anchoredConst_apply (L B : ℕ → ℝ) (j : ℕ) : anchoredConst L B j = max (L j) (B (j + 1)) :=
  rfl

/-- The zero constraint map `ℝⁿ → ℝ⁰` has vanishing iterated derivatives (all maps into `ℝ⁰`
vanish). -/
theorem iteratedFDeriv_zeroCon (i : ℕ) (x : ℝⁿ) : iteratedFDeriv ℝ i (zeroCon n) x = 0 := by
  ext v j
  exact j.elim0

/-- The anchored bounds of the ARqpC analysis for INNER on `F` (ARqpC-SC with `c = 0`, `h = 0`)
need only the Lipschitz condition of `∇^p F` anchored on `S` (constant `L_p ≥ 1`) and the bounds
`‖∇^i F‖ ≤ L_{i-1}` on `S` for `i ∈ [2 : p]`. -/
theorem anchoredCompositeBounds_zeroCon_of {F : ℝⁿ → ℝ} {X₀ S : Set ℝⁿ} {p : ℕ} {L : ℕ → ℝ}
    (hX₀ : IsOpen X₀) (hconv : Convex ℝ X₀) (hS : S ⊆ X₀) (hF : ContDiffOn ℝ p F X₀)
    (hL1 : 1 ≤ L p) (hlip : IteratedFDerivLipschitzAnchored F p (L p) S X₀)
    (hbd : ∀ i ∈ Finset.Icc 2 p, ∀ x ∈ S, ‖iteratedFDeriv ℝ i F x‖ ≤ L (i - 1)) :
    AnchoredCompositeBounds F (zeroCon n) X₀ S p L (fun _ => 0) where
  isOpen := hX₀
  convex := hconv
  subset := hS
  contDiffOn_f := hF
  contDiffOn_c := contDiffOn_const
  one_le := hL1
  nonneg := le_rfl
  lipschitz_f := hlip
  lipschitz_c x _ y _ := by simp [iteratedFDeriv_zeroCon]
  norm_f := hbd
  norm_c i _ x _ := by simp [iteratedFDeriv_zeroCon]

/-- Anchored Lipschitz and bounded derivatives of `F` of orders `1, …, p` on an anchor set `S`
(the shape of f.D1pLaB.X) give the anchored bounds of the ARqpC analysis for INNER on `F`
(ARqpC-SC with `c = 0`, `h = 0`) with the constants `anchoredConst L B`
(`anchoredCompositeBounds_zeroCon_of`). -/
theorem anchoredCompositeBounds_zeroCon {F : ℝⁿ → ℝ} {X₀ S : Set ℝⁿ} {p : ℕ} {L B : ℕ → ℝ}
    (hX₀ : IsOpen X₀) (hconv : Convex ℝ X₀) (hS : S ⊆ X₀) (hF : ContDiffOn ℝ p F X₀)
    (hp : 1 ≤ p) (hL1 : 1 ≤ L p)
    (hb : ∀ j ∈ Finset.Icc 1 p, IteratedFDerivLipschitzAnchored F j (L j) S X₀ ∧
      ∀ x ∈ S, ‖iteratedFDeriv ℝ j F x‖ ≤ B j) :
    AnchoredCompositeBounds F (zeroCon n) X₀ S p (anchoredConst L B) (fun _ => 0) :=
  anchoredCompositeBounds_zeroCon_of hX₀ hconv hS hF (hL1.trans (le_max_left _ _))
    ((hb p (Finset.mem_Icc.2 ⟨hp, le_rfl⟩)).1.mono_const (le_max_left _ _)) fun i hi x hx => by
      obtain ⟨hi2, hip⟩ := Finset.mem_Icc.1 hi
      refine ((hb i (Finset.mem_Icc.2 ⟨by omega, hip⟩)).2 x hx).trans ?_
      rw [anchoredConst_apply, show i - 1 + 1 = i by omega]
      exact le_max_right _ _

/-- **f.D1pLaB.X gives the anchored bounds for INNER**: under f.D1pLaB.X (constants `L`, `B`,
sublevel set `𝓛_F(x₀)`), the anchored bounds of the ARqpC analysis hold for ARqpC-SC with `c = 0`,
`h = 0` on `F`, anchored on `𝓛_F(x₀)`, with the constants `anchoredConst L B`. -/
theorem AssumptionD1qLaBX.anchoredCompositeBounds {F : ℝⁿ → ℝ} {X X₀ : Set ℝⁿ} {x₀ : ℝⁿ}
    {p : ℕ} {L B : ℕ → ℝ} (h : AssumptionD1qLaBX F X X₀ x₀ 1 p L B) (hp : 1 ≤ p) :
    AnchoredCompositeBounds F (zeroCon n) X₀ (sublevel F X x₀) p (anchoredConst L B)
      (fun _ => 0) :=
  anchoredCompositeBounds_zeroCon h.isOpen h.convex (sublevel_subset.trans h.subset) h.contDiffOn
    hp (h.one_le_lip p (Finset.mem_Icc.2 ⟨hp, le_rfl⟩))
    fun j hj => ⟨h.lipschitzAnchored j hj, h.norm_le j hj⟩

/-! ### LENq-SC under Φ₂.D1pLaB.X -/

section LENq

/-- **Complexity of the constructed LENq-SC runs under Φ₂.D1pLaB.X** ([cartis2022evaluation],
Theorem 14.3.4 with INNER = ARqp-SC, under its assumption Φ₂.D1pLaB.X). Let `X` be closed,
`1 ≤ q ≤ p`, `Φ₂ = ½ ‖r‖²` satisfy Φ₂.D1pLaB.X on an open convex `X₀ ⊇ X` with constants `L`, `B`
and the sublevel set `𝓛_{Φ₂}(x₀)` (`AssumptionD1qLaBX (phi2 r) X X₀ x₀ 1 p L B`), and `P` be
ARqpC constants with `θ < ς`. Then for the starting point `x₀ ∈ X` of Φ₂.D1pLaB.X and every
admissible `ε`, `β`, there is a LENq-SC
run from `x₀`, terminating at its first hit `k_max`, whose `k`-th INNER call is an ARqp-SC call
using `nF k` evaluations of `Φ₂` and `nD k` of its derivatives (`IsARqpSCOutputCost`); their
totals obey (14.3.27)–(14.3.28) (with `∑_j` for `max_j`) with
`κ_F = arqpSCKappaF P (anchoredConst L B) p q`, `κ_D = arqpSCKappaD P (anchoredConst L B) p q` and
`π_j = j + 1` (the ARqpC-SC row of (14.2.12); see `exists_algorithm_14_3_1_complexity`). -/
theorem exists_algorithm_14_3_1_complexity_anchored {r : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} (hX : IsClosed X)
    {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) {X₀ : Set ℝⁿ} {x₀ : ℝⁿ} {L B : ℕ → ℝ}
    (hΦ : AssumptionD1qLaBX (phi2 r) X X₀ x₀ 1 p L B) (P : ARqpCParams) (hθς : P.θ < P.ς)
    {ε : ℕ → ℝ} (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hx₀ : x₀ ∈ X) (hβr : β * ‖r x₀‖ < 1) :
    ∃ (x : ℕ → ℝⁿ) (δ : ℕ → ℕ → ℝ) (nF nD : ℕ → ℕ) (kmax : ℕ), x 0 = x₀ ∧
      algorithm_14_3_1 r X q ε β x δ ∧ Optimization.IsFirstHit (lenStop r X q ε x δ) kmax ∧
      (∀ k, 1 ≤ k → k ≤ kmax →
        IsARqpSCOutputCost (phi2 r) X p q P (fun j => β * ‖r (x (k - 1))‖ * ε j) (x (k - 1))
          (x k) (δ k) (nF k) (nD k)) ∧
      (∑ k ∈ Finset.Icc 1 kmax, (nF k : ℝ) ≤
        1 / 2 * arqpSCKappaF P (anchoredConst L B) p q * ‖r x₀‖ *
        ∑ j ∈ Finset.Icc 1 q, β ^ (1 - 2 * ((j : ℝ) + 1)) / (β ^ (1 - ((j : ℝ) + 1)) - 1) *
          ε 0 ^ (1 - ((j : ℝ) + 1)) * ε j ^ (-((j : ℝ) + 1))) ∧
      (∑ k ∈ Finset.Icc 1 kmax, (nD k : ℝ) ≤
        1 / 2 * arqpSCKappaD P (anchoredConst L B) p q * ‖r x₀‖ *
        ∑ j ∈ Finset.Icc 1 q, β ^ (1 - 2 * ((j : ℝ) + 1)) / (β ^ (1 - ((j : ℝ) + 1)) - 1) *
          ε 0 ^ (1 - ((j : ℝ) + 1)) * ε j ^ (-((j : ℝ) + 1))) := by
  have hp : 1 ≤ p := hq.trans hqp
  have hA := hΦ.anchoredCompositeBounds hp
  have hS : ∀ y ∈ X, ‖r y‖ ≤ ‖r x₀‖ → y ∈ sublevel (phi2 r) X x₀ := fun y hy hry =>
    ⟨hy, by rw [phi2_apply, phi2_apply]; gcongr⟩
  obtain ⟨x, δ, nF, nD, hx0, hrun, hcalls⟩ :=
    lenq_core_anchored hX hq hqp hA hΦ.subset P hθς hε hβ0 hβ1 hx₀ hS hβr
  obtain ⟨⟨kmax, hhit, -, -⟩, -⟩ := theorem_14_3_3 hrun
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
  have hε1 := hε 1 (Finset.mem_range.2 (by omega))
  have hπ1 : ∀ l ∈ Finset.Icc 1 q, 1 < (fun l : ℕ => (l : ℝ) + 1) l := fun l hl => by
    have : (1 : ℝ) ≤ l := by exact_mod_cast (Finset.mem_Icc.1 hl).1
    change 1 < (l : ℝ) + 1
    linarith
  have hκF : 0 ≤ arqpSCKappaF P (anchoredConst L B) p q := by
    unfold arqpSCKappaF
    have := arqpSCKappaDecr_pos_of (q := q) hA.one_le hθς
    have := arqpSCKappaUns_nonneg P
    have := arqpSCKappaC_nonneg P (anchoredConst L B) p
    positivity
  have hκD : 0 ≤ arqpSCKappaD P (anchoredConst L B) p q := by
    unfold arqpSCKappaD
    have := arqpSCKappaDecr_pos_of (q := q) hA.one_le hθς
    positivity
  have hcalls' : ∀ k, 1 ≤ k → k ≤ kmax →
      IsARqpSCOutputCost (phi2 r) X p q P (fun j => β * ‖r (x (k - 1))‖ * ε j) (x (k - 1))
        (x k) (δ k) (nF k) (nD k) :=
    fun k hk1 hk => hcalls k hk1 fun i hi => hhit.2 i (hi.trans_le hk)
  have hcost : ∀ k ∈ Finset.Icc 1 kmax,
      (nF k : ℝ) ≤ innerEvalBound (arqpSCKappaF P (anchoredConst L B) p q) (fun l => (l : ℝ) + 1) q
        (phi2 r (x (k - 1))) (fun j => β * ‖r (x (k - 1))‖ * ε j) ∧
      (nD k : ℝ) ≤ innerEvalBound (arqpSCKappaD P (anchoredConst L B) p q) (fun l => (l : ℝ) + 1) q
        (phi2 r (x (k - 1))) (fun j => β * ‖r (x (k - 1))‖ * ε j) := by
    intro k hk
    obtain ⟨hk1, hkk⟩ := Finset.mem_Icc.1 hk
    have hmem : x (k - 1) ∈ X := by
      rcases Nat.eq_zero_or_pos (k - 1) with h0 | hpos
      · rw [h0]; exact hrun.mem_zero
      · exact hrun.mem (k - 1) hpos fun i hi => hhit.2 i (by omega)
    have hrk : ‖r (x (k - 1))‖ ≤ ‖r x₀‖ := by
      have := hrun.norm_le_pow_mul (Nat.zero_le (k - 1)) fun l hl => hhit.2 l (by omega)
      rw [hx0] at this
      exact this.trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hβ0.le hβ1.le))
    refine (hcalls' k hk1 hkk).cost_le_anchored hA hΦ.subset
      (fun y _ => by rw [phi2_apply]; positivity) hθς hmem
      (fun y hy hyk => hS y hy ((norm_le_of_phi2_le hyk).trans hrk)) ?_
    rw [phi2_apply]
    have hb1 : β * ε 1 ≤ 1 := by nlinarith
    have hb0 : 0 ≤ β * ε 1 := by have := hε1.1; positivity
    have : (β * ‖r (x (k - 1))‖ * ε 1) ^ 2 = (β * ε 1) ^ 2 * ‖r (x (k - 1))‖ ^ 2 := by ring
    rw [this]
    have : (β * ε 1) ^ 2 ≤ 1 := pow_le_one₀ hb0 hb1
    nlinarith [sq_nonneg ‖r (x (k - 1))‖]
  have hF := theorem_14_3_4 hrun hhit hπ1 hκF fun k hk => (hcost k hk).1
  have hD := theorem_14_3_4 hrun hhit hπ1 hκD fun k hk => (hcost k hk).2
  rw [hx0] at hF hD
  exact ⟨x, δ, nF, nD, kmax, hx0, hrun, hhit, hcalls', hF, hD⟩

end LENq

/-! ### Phase 2 of TPqp-GC under the anchored assumptions -/

section TPqp

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams} {ε : ℕ → ℝ}
  {θ β : ℝ}

/-- **Complexity of the constructed TPqp-GC runs under anchored bounds**
([cartis2022evaluation], Theorem 14.3.9 for TPqp-GC with INNER = ARqp-SC in both phases). Let `X`
be closed, `1 ≤ q ≤ p`, `X₀ ⊇ X` open and convex, `ν = ½ ‖c‖²` satisfy the anchored bounds of the
ARqpC analysis on `𝓛_ν(x₀)` with constants `L_ν`, and `μ(·, t)` satisfy them on `𝓛_μ(t)` with
constants `L` independent of `t` (Lemma 14.3.6 gives both under c.D1pLB.X and f.D1pLB.X:
`exists_algorithm_14_3_2_complexity_anchored`), and let f.B.Fb hold on `ℱ_{β_F}` with
`ε₀ ≤ β_F`. Then the conclusions of `exists_algorithm_14_3_2_complexity` hold: there is a
TPqp-GC run from `x₀` whose Phase-1 INNER calls satisfy the cost contract with
`κ_F = arqpSCKappaF P L_ν p q`, `κ_D = arqpSCKappaD P L_ν p q`, `π_j = j + 1` (totals as in
Lemma 14.3.7), and whose Phase 2, if entered, satisfies `IsInnerPhaseRun` with
`κ_decr = arqpSCKappaDecr P L p q`, `κ_unc = arqpSCKappaUnc P L p`, and (i)–(iii) of
Theorem 14.3.9 with the number of bad outer iterations as a parameter. -/
theorem exists_algorithm_14_3_2_complexity_anchored' (hX : IsClosed X) (hq : 1 ≤ q) (hqp : q ≤ p)
    {X₀ : Set ℝⁿ} {x₀ : ℝⁿ} {Lν : ℕ → ℝ}
    (hν : AnchoredCompositeBounds (phi2 c) (zeroCon n) X₀ (nuSublevel c X x₀) p Lν (fun _ => 0))
    {βF flow fup : ℝ} (hB : Chapter07.AssumptionBFb f c X βF flow fup) (hεβ : ε 0 ≤ βF)
    {L : ℕ → ℝ}
    (hμ : ∀ t, AnchoredCompositeBounds (Constrained.targetMerit f c t) (zeroCon n) X₀
      (muSublevel f c X t) p L (fun _ => 0)) (hXX₀ : X ⊆ X₀)
    (P : ARqpCParams) (hθς : P.θ < P.ς) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) (hβ0 : 0 < β) (hβθ : β ≤ θ)
    {β₁ : ℝ} (hβ₁0 : 0 < β₁) (hβ₁1 : β₁ < 1) (hx₀ : x₀ ∈ X)
    (hβ₁c : β₁ * ‖c x₀‖ < 1) :
    ∃ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
      algorithm_14_3_2 f c X q θ β₁ β ε x₀ xP δP k₁ D ∧
      (∀ k, 1 ≤ k → k ≤ k₁ → IsARqpSCOutputCost (phi2 c) X p q P
        (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) (xP (k - 1)) (xP k) (δP k) (nF₁ k)
          (nD₁ k)) ∧
      (∀ k ∈ Finset.Icc 1 k₁,
        (nF₁ k : ℝ) ≤ innerEvalBound (arqpSCKappaF P Lν p q) (fun l => (l : ℝ) + 1) q
          (phi2 c (xP (k - 1))) (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) ∧
        (nD₁ k : ℝ) ≤ innerEvalBound (arqpSCKappaD P Lν p q) (fun l => (l : ℝ) + 1) q
          (phi2 c (xP (k - 1))) (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j)) ∧
      (∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤ 1 / 2 * arqpSCKappaF P Lν p q * ‖c x₀‖ *
        ∑ j ∈ Finset.Icc 1 q, β₁ ^ (1 - 2 * ((j : ℝ) + 1)) / (β₁ ^ (1 - ((j : ℝ) + 1)) - 1) *
          θ ^ (1 - ((j : ℝ) + 1)) * ε 0 ^ (1 - ((j : ℝ) + 1)) * ε j ^ (-((j : ℝ) + 1))) ∧
      (∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ 1 / 2 * arqpSCKappaD P Lν p q * ‖c x₀‖ *
        ∑ j ∈ Finset.Icc 1 q, β₁ ^ (1 - 2 * ((j : ℝ) + 1)) / (β₁ ^ (1 - ((j : ℝ) + 1)) - 1) *
          θ ^ (1 - ((j : ℝ) + 1)) * ε 0 ^ (1 - ((j : ℝ) + 1)) * ε j ^ (-((j : ℝ) + 1))) ∧
      (‖c (xP k₁)‖ ≤ θ * ε 0 →
        (∀ k, 1 ≤ k → D.Before f c X q θ ε k →
          IsARqpSCCall (Constrained.targetMerit f c (D.t k)) X p q P
            (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j)
            (D.xi k) (D.e k) (D.succ k)) ∧
        IsInnerPhaseRun f c X q θ β ε D (arqpSCKappaDecr P L p q) (arqpSCKappaUns P)
          (arqpSCKappaUnc P L p) (fun l => (l : ℝ) + 1) ∧
        (∀ K, 1 ≤ K → D.Before f c X q θ ε K →
          (K : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) *
            (goodBound (arqpSCKappaDecr P L p q) β θ ((q : ℝ) + 1) (arqpSCPhase2M q ε) + 1) +
              D.badCount f c X q θ ε K) ∧
        (∀ Bb : ℝ, (∀ K, D.Before f c X q θ ε K → (D.badCount f c X q θ ε K : ℝ) ≤ Bb) →
          ∃ kε, D.IsEnd f c X q θ ε kε ∧
            (kε : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) *
              (goodBound (arqpSCKappaDecr P L p q) β θ ((q : ℝ) + 1) (arqpSCPhase2M q ε) + 1) +
                Bb) ∧
        (∀ kε, D.IsEnd f c X q θ ε kε →
          (D.derivEvals kε : ℝ) ≤
            1 + goodBound (arqpSCKappaDecr P L p q) β θ ((q : ℝ) + 1) (arqpSCPhase2M q ε) *
              ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) + kε ∧
          (D.funEvals kε : ℝ) ≤
            1 + arqpSCKappaUns P *
              (goodBound (arqpSCKappaDecr P L p q) β θ ((q : ℝ) + 1) (arqpSCPhase2M q ε) *
                ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) + kε) +
              arqpSCKappaUnc P L p * kε)) := by
  obtain ⟨xP, δP, k₁, D, nF₁, nD₁, h, hcalls, hQ⟩ := exists_algorithm_14_3_2_of_phase2_anchored hX
    hq hqp hν hXX₀ P hθς hθ0 hθ1 hε hβ₁0 hβ₁1 hx₀ hβ₁c (β := β) (Q := fun D =>
      (∀ k, 1 ≤ k → D.Before f c X q θ ε k →
        IsARqpSCCall (Constrained.targetMerit f c (D.t k)) X p q P
          (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j)
          (D.xi k) (D.e k) (D.succ k)) ∧
      0 < arqpSCKappaDecr P L p q ∧
      IsInnerPhaseRun f c X q θ β ε D (arqpSCKappaDecr P L p q) (arqpSCKappaUns P)
        (arqpSCKappaUnc P L p) (fun l => (l : ℝ) + 1))
    fun _ hx₁ hc₁ => exists_isTPqpGCPhase2_isInnerPhaseRun_anchored hX hq hqp hμ hXX₀ P hθς hθ0
      hθ1 hβ0 hβθ hε hx₁ hc₁
  have hp : 1 ≤ p := hq.trans hqp
  have hεI : ∀ l ∈ Finset.Icc 1 q, 0 < ε l ∧ ε l ≤ 1 := fun l hl =>
    hε l (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hl).2))
  have hε₀ : 0 < ε 0 := (hε 0 (by simp)).1
  have hπ1 : ∀ l ∈ Finset.Icc 1 q, 1 < (fun l : ℕ => (l : ℝ) + 1) l := fun l hl => by
    have : (1 : ℝ) ≤ l := by exact_mod_cast (Finset.mem_Icc.1 hl).1
    change 1 < (l : ℝ) + 1
    linarith
  -- Phase 1: the cost contract of the INNER calls
  have hκ₁ : 0 < arqpSCKappaDecr P Lν p q := arqpSCKappaDecr_pos_of hν.one_le hθς
  have hκF : 0 ≤ arqpSCKappaF P Lν p q := by
    unfold arqpSCKappaF
    have := arqpSCKappaUns_nonneg P
    have := arqpSCKappaC_nonneg P Lν p
    positivity
  have hκD : 0 ≤ arqpSCKappaD P Lν p q := by unfold arqpSCKappaD; positivity
  have hcost := phase1_cost_le_anchored h hq hν hXX₀ hθς hε hcalls
  refine ⟨xP, δP, k₁, D, nF₁, nD₁, h, hcalls, hcost,
    (lemma_14_3_7 h hθ0 hπ1 hκF fun k hk => (hcost k hk).1).2,
    (lemma_14_3_7 h hθ0 hπ1 hκD fun k hk => (hcost k hk).2).2,
    fun hc1 => ⟨(hQ hc1).1, (hQ hc1).2.2, ?_⟩⟩
  -- Phase 2: Theorem 14.3.9 (its Phase-2 part does not involve the Phase-1 costs)
  have hterm : ∀ l ∈ Finset.Icc 1 q, 0 < ε 0 ^ (2 - ((l : ℝ) + 1)) * ε l ^ (-((l : ℝ) + 1)) :=
    fun l hl => mul_pos (Real.rpow_pos_of_pos hε₀ _) (Real.rpow_pos_of_pos (hεI l hl).1 _)
  have hπ : ∀ l ∈ Finset.Icc 1 q, 0 ≤ (fun l : ℕ => (l : ℝ) + 1) l ∧
      (fun l : ℕ => (l : ℝ) + 1) l ≤ (q : ℝ) + 1 := fun l hl => by
    have : (l : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.1 hl).2
    exact ⟨by positivity, by linarith⟩
  have hM0 : 0 < arqpSCPhase2M q ε :=
    Finset.sum_pos hterm ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hq⟩⟩
  have hM : ∀ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - (fun l : ℕ => (l : ℝ) + 1) l) *
      ε l ^ (-(fun l : ℕ => (l : ℝ) + 1) l) ≤ arqpSCPhase2M q ε := fun l hl =>
    Finset.single_le_sum (f := fun l : ℕ => ε 0 ^ (2 - ((l : ℝ) + 1)) * ε l ^ (-((l : ℝ) + 1)))
      (fun i hi => (hterm i hi).le) hl
  exact (theorem_14_3_9 h hθ0 hπ1 hκF hκD (fun k hk => (hcost k hk).1)
    (fun k hk => (hcost k hk).2) (hQ hc1).2.2 (hQ hc1).2.1 (arqpSCKappaUns_nonneg P) hπ hM0 hM hB
    hεβ).2.2 hc1

/-- The constants `max(L^A_j + L^B_j ‖c(x₀)‖, B^A_{j+1} + B^B_{j+1} ‖c(x₀)‖)` (`anchoredConst`) of
the anchored bounds of `ν = ½ ‖c‖²` on `𝓛_ν(x₀)` given by Lemma 14.3.6 (i) (constants `L^A`, `L^B`,
`B^A`, `B^B`, `r = ‖c(x₀)‖`). -/
noncomputable def nuAnchoredConst (LA LB BA BB : ℕ → ℝ) (r : ℝ) : ℕ → ℝ :=
  anchoredConst (fun j => LA j + LB j * r) (fun j => BA j + BB j * r)

/-- **Anchored bounds for `ν` and `μ(·, t)` from the book's assumptions** ([cartis2022evaluation],
Lemma 14.3.6): under c.D1pLB.X and f.D1pLB.X (on an open convex `X₀ ⊇ X`) there are constants
`L^A_j, L^B_j, B^A_j, B^B_j, L_{μ,j}, B_{μ,j} ≥ 1`, depending only on `m` and the constants of these
assumptions, such that for every `x₀` the function `ν = ½ ‖c‖²` satisfies the anchored bounds of the
ARqpC analysis on `𝓛_ν(x₀)` with the constants `nuAnchoredConst L^A L^B B^A B^B ‖c(x₀)‖`, and every
`μ(·, t)` satisfies them on `𝓛_μ(t)` with the constants `anchoredConst L_μ B_μ`. These are the
hypotheses `hν`, `hμ` (with `hXX₀ = hc.subset`) of the TPqp-GC theorems of `Chapter14.Section03`
stated under anchored bounds (`exists_algorithm_14_3_2_complexity_anchored'`,
`exists_algorithm_14_3_2_complexity_certified_anchored`,
`exists_algorithm_14_3_2_complexity_strong_anchored`,
`exists_algorithm_14_3_2_complexity_arqp_anchored`,
`exists_algorithm_14_3_2_complexity_arqp_add_anchored`, and, on `X = X₀ = ℝⁿ`,
`exists_algorithm_14_3_2_complexity_unit_anchored`). -/
theorem exists_anchoredCompositeBounds_nu_mu (hp : 1 ≤ p) {X₀ : Set ℝⁿ} {Lc Bc Lf Bf : ℕ → ℝ}
    (hc : AssumptionCD1pLBX c X X₀ p Lc Bc) (hf : AssumptionD1pLBX f X X₀ p Lf Bf) :
    ∃ LA LB BA BB Lμ Bμ : ℕ → ℝ,
      (∀ j, 1 ≤ LA j ∧ 1 ≤ LB j ∧ 1 ≤ BA j ∧ 1 ≤ BB j ∧ 1 ≤ Lμ j ∧ 1 ≤ Bμ j) ∧
      (∀ x₀ : ℝⁿ, AnchoredCompositeBounds (phi2 c) (zeroCon n) X₀ (nuSublevel c X x₀) p
        (nuAnchoredConst LA LB BA BB ‖c x₀‖) (fun _ => 0)) ∧
      ∀ t, AnchoredCompositeBounds (Constrained.targetMerit f c t) (zeroCon n) X₀
        (muSublevel f c X t) p (anchoredConst Lμ Bμ) (fun _ => 0) := by
  obtain ⟨LA, LB, BA, BB, h1, hν⟩ := lemma_14_3_6_i hc
  obtain ⟨Lμ, Bμ, h2, hμ⟩ := lemma_14_3_6_ii hc hf
  refine ⟨LA, LB, BA, BB, Lμ, Bμ, fun j => ⟨(h1 j).1, (h1 j).2.1, (h1 j).2.2.1, (h1 j).2.2.2,
    (h2 j).1, (h2 j).2⟩, fun x₀ => ?_, fun t => ?_⟩
  · refine anchoredCompositeBounds_zeroCon hc.isOpen hc.convex (fun x hx => hc.subset hx.1)
      (hν x₀).1 hp ?_ (hν x₀).2
    have := (h1 p).1
    have := (h1 p).2.1
    have := norm_nonneg (c x₀)
    nlinarith
  · exact anchoredCompositeBounds_zeroCon hc.isOpen hc.convex (fun x hx => hc.subset hx.1)
      (hμ t).1 hp (h2 p).1 (hμ t).2

/-- **Theorem 14.3.9 of [cartis2022evaluation] for the constructed TPqp-GC runs, under the book's
assumptions** X.CNe (`X` closed), c.D1pLB.X, f.D1pLB.X (on an open convex `X₀ ⊇ X`) and f.B.Fb,
with INNER = ARqp-SC in both phases. There are constants `L^A_j, L^B_j, B^A_j, B^B_j ≥ 1` (for
`ν`, Lemma 14.3.6 (i)) and `L_{μ,j}, B_{μ,j} ≥ 1` (for `μ`, Lemma 14.3.6 (ii)), depending only on
`m` and the constants of c.D1pLB.X and f.D1pLB.X, such that for all ARqpC constants with `θ < ς`
and every admissible `θ`, `β`, `β₁`, `ε` and `x₀ ∈ X`, the conclusions of
`exists_algorithm_14_3_2_complexity` hold with the Phase-1 constants
`κ_F = arqpSCKappaF P Lν p q`, `κ_D = arqpSCKappaD P Lν p q`,
`Lν = nuAnchoredConst LA LB BA BB ‖c(x₀)‖` (depending on `‖c(x₀)‖`, as in the book) and the
Phase-2 constants `κ_decr = arqpSCKappaDecr P L p q`, `κ_unc = arqpSCKappaUnc P L p`,
`L = anchoredConst Lμ Bμ` (independent of the targets). The exponents are those of the
ARqpC-SC row of (14.2.12), `π_j = j + 1`, and the number of bad outer iterations is a parameter of
(i)–(ii), as in `exists_algorithm_14_3_2_complexity`. -/
theorem exists_algorithm_14_3_2_complexity_anchored (hX : IsClosed X) (hq : 1 ≤ q) (hqp : q ≤ p)
    {X₀ : Set ℝⁿ} {Lc Bc Lf Bf : ℕ → ℝ} (hc : AssumptionCD1pLBX c X X₀ p Lc Bc)
    (hf : AssumptionD1pLBX f X X₀ p Lf Bf) :
    ∃ LA LB BA BB Lμ Bμ : ℕ → ℝ,
      (∀ j, 1 ≤ LA j ∧ 1 ≤ LB j ∧ 1 ≤ BA j ∧ 1 ≤ BB j ∧ 1 ≤ Lμ j ∧ 1 ≤ Bμ j) ∧
      ∀ (P : ARqpCParams) {θ β β₁ : ℝ} {ε : ℕ → ℝ} {x₀ : ℝⁿ} {βF flow fup : ℝ},
        Chapter07.AssumptionBFb f c X βF flow fup → ε 0 ≤ βF → P.θ < P.ς → 0 < θ → θ < 1 →
        (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → 0 < β → β ≤ θ → 0 < β₁ → β₁ < 1 →
        x₀ ∈ X → β₁ * ‖c x₀‖ < 1 →
        let Lν := nuAnchoredConst LA LB BA BB ‖c x₀‖
        let L := anchoredConst Lμ Bμ
        ∃ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
          algorithm_14_3_2 f c X q θ β₁ β ε x₀ xP δP k₁ D ∧
          (∀ k, 1 ≤ k → k ≤ k₁ → IsARqpSCOutputCost (phi2 c) X p q P
            (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) (xP (k - 1)) (xP k) (δP k) (nF₁ k)
              (nD₁ k)) ∧
          (∀ k ∈ Finset.Icc 1 k₁,
            (nF₁ k : ℝ) ≤ innerEvalBound (arqpSCKappaF P Lν p q) (fun l => (l : ℝ) + 1) q
              (phi2 c (xP (k - 1))) (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) ∧
            (nD₁ k : ℝ) ≤ innerEvalBound (arqpSCKappaD P Lν p q) (fun l => (l : ℝ) + 1) q
              (phi2 c (xP (k - 1))) (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j)) ∧
          (∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤ 1 / 2 * arqpSCKappaF P Lν p q * ‖c x₀‖ *
            ∑ j ∈ Finset.Icc 1 q, β₁ ^ (1 - 2 * ((j : ℝ) + 1)) / (β₁ ^ (1 - ((j : ℝ) + 1)) - 1) *
              θ ^ (1 - ((j : ℝ) + 1)) * ε 0 ^ (1 - ((j : ℝ) + 1)) * ε j ^ (-((j : ℝ) + 1))) ∧
          (∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ 1 / 2 * arqpSCKappaD P Lν p q * ‖c x₀‖ *
            ∑ j ∈ Finset.Icc 1 q, β₁ ^ (1 - 2 * ((j : ℝ) + 1)) / (β₁ ^ (1 - ((j : ℝ) + 1)) - 1) *
              θ ^ (1 - ((j : ℝ) + 1)) * ε 0 ^ (1 - ((j : ℝ) + 1)) * ε j ^ (-((j : ℝ) + 1))) ∧
          (‖c (xP k₁)‖ ≤ θ * ε 0 →
            (∀ k, 1 ≤ k → D.Before f c X q θ ε k →
              IsARqpSCCall (Constrained.targetMerit f c (D.t k)) X p q P
                (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j)
                (D.xi k) (D.e k) (D.succ k)) ∧
            IsInnerPhaseRun f c X q θ β ε D (arqpSCKappaDecr P L p q) (arqpSCKappaUns P)
              (arqpSCKappaUnc P L p) (fun l => (l : ℝ) + 1) ∧
            (∀ K, 1 ≤ K → D.Before f c X q θ ε K →
              (K : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) *
                (goodBound (arqpSCKappaDecr P L p q) β θ ((q : ℝ) + 1) (arqpSCPhase2M q ε) + 1) +
                  D.badCount f c X q θ ε K) ∧
            (∀ Bb : ℝ, (∀ K, D.Before f c X q θ ε K → (D.badCount f c X q θ ε K : ℝ) ≤ Bb) →
              ∃ kε, D.IsEnd f c X q θ ε kε ∧
                (kε : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) *
                  (goodBound (arqpSCKappaDecr P L p q) β θ ((q : ℝ) + 1) (arqpSCPhase2M q ε) + 1) +
                    Bb) ∧
            (∀ kε, D.IsEnd f c X q θ ε kε →
              (D.derivEvals kε : ℝ) ≤
                1 + goodBound (arqpSCKappaDecr P L p q) β θ ((q : ℝ) + 1) (arqpSCPhase2M q ε) *
                  ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) + kε ∧
              (D.funEvals kε : ℝ) ≤
                1 + arqpSCKappaUns P *
                  (goodBound (arqpSCKappaDecr P L p q) β θ ((q : ℝ) + 1) (arqpSCPhase2M q ε) *
                    ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) + kε) +
                  arqpSCKappaUnc P L p * kε)) := by
  obtain ⟨LA, LB, BA, BB, Lμ, Bμ, h1, hνA, hμA⟩ :=
    exists_anchoredCompositeBounds_nu_mu (hq.trans hqp) hc hf
  refine ⟨LA, LB, BA, BB, Lμ, Bμ, h1, ?_⟩
  intro P θ β β₁ ε x₀ βF flow fup hB hεβ hθς hθ0 hθ1 hε hβ0 hβθ hβ₁0 hβ₁1 hx₀ hβ₁c
  exact exists_algorithm_14_3_2_complexity_anchored' hX hq hqp (hνA x₀) hB hεβ hμA hc.subset P hθς
    hθ0 hθ1 hε hβ0 hβθ hβ₁0 hβ₁1 hx₀ hβ₁c

end TPqp

end CartisGouldToint.Chapter14
