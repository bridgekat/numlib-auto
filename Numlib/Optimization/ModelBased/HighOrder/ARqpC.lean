import Numlib.Optimization.ModelBased.HighOrder.ARqp
import Numlib.Optimization.ModelBased.HighOrderStep

/-!
# The adaptive-regularization method ARqpC for composite problems

ARqpC ([cartis2022evaluation], §14.1, Algorithm 14.1.1) minimizes `w = f + h ∘ c` with
`f : E → ℝ`, `c : E → F` smooth and `h : F → ℝ` Lipschitz (possibly nonsmooth) on a feasible set
`X` (`X = univ` is ARqpC, a closed `X` is ARqpC-SC of §14.2). It is the generic ARqp run
`Optimization.IsARqpRun` for the objective `w` with the composite model data
`arqpcData f c h p x σ k = ARqpData.ofComposite (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k))
h p (σ k)`, whose Step 2 is computed by the detailed Step 2 (Algorithm 14.1.2): the abstract
transition system `Optimization.DetailedStepTrans` for the composite model
`compositeRegularizedModel` and its decrements (14.1.14), with a set `J` of orders at which the
radius may be halved (`j ≥ 2`, and `j = 1` as well if `h` or `X` is not convex).

## Main definitions

* `Optimization.arqpcData`, `Optimization.arqpcStop`: the model data and termination test;
* `Optimization.IsARqpCDetailedStep`: the outputs of the detailed Step 2.

## Main results

* `Optimization.exists_isARqpCDetailedStep`: in finite dimension the detailed Step 2 has an output
  whose radii satisfy the lower bound of Lemma 14.1.3 at the halved orders (and are `1` at the
  others);
* `Optimization.IsARqpCDetailedStep.exists_arqpStep`: its outputs satisfy the Step-2 conditions of
  the run;
* `Optimization.exists_isARqpRun_composite`: ARqpC runs exist for any `f`, `c` and any Lipschitz,
  subadditive `h` with `h 0 = 0`, on a closed feasible set (no smoothness is needed);
* `Optimization.isARqpCDetailedStep_of_isMinOn`: for `q = 1`, convex `h` and `X`, global model
  minimizers are outputs of the detailed Step 2.
-/

open Set Metric
open scoped Nat

namespace Optimization

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {p q : ℕ}

/-- The model data of ARqpC at iteration `k` ([cartis2022evaluation], (14.1.10)–(14.1.15)):
generalized Taylor decrements of `w = f + h ∘ c` at `x_k`, the model `m̂_k` (14.1.11), its
decrements (14.1.14) and the predicted decrease `ΔT_{w,p}(x_k, ·)`. -/
noncomputable abbrev arqpcData (f : E → ℝ) (c : E → F) (h : F → ℝ) (p : ℕ) (x : ℕ → E)
    (σ : ℕ → ℝ) (k : ℕ) : ARqpData E :=
  ARqpData.ofComposite (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k)) h p (σ k)

/-- The termination test of ARqpC at iteration `k`: the Step-1 test, or the Step-2 test
`m̂_k(s_k) = m̂_k(0)`. -/
abbrev arqpcStop (f : E → ℝ) (c : E → F) (h : F → ℝ) (P : ARqpParams) (p q : ℕ) (ε : ℕ → ℝ)
    (x s : ℕ → E) (σ : ℕ → ℝ) (δ : ℕ → ℕ → ℝ) (d : ℕ → ℕ → E) (k : ℕ) : Prop :=
  IsARRun.Stop (arqpStop₁ P q ε (arqpcData f c h p x σ) δ d)
    (arqpStop₂ (arqpcData f c h p x σ) s) k

/-- The outputs `(s, δ_s)` of the detailed Step 2 of ARqpC ([cartis2022evaluation],
Algorithm 14.1.2) at the iterate `x` with weight `σ`: the abstract detailed Step 2
(`IsDetailedStepOutput`) for the composite model `m̂` over the feasible steps `{s | x + s ∈ X}`,
with displacements `{d | x + s + d ∈ X}`, the model decrements (14.1.14), and the halving set
`J`. -/
abbrev IsARqpCDetailedStep (f : E → ℝ) (c : E → F) (h : F → ℝ) (X : Set E) (p q : ℕ)
    (P : ARqpParams) (ε : ℕ → ℝ) (J : Set ℕ) (σ : ℝ) (x s : E) (δs : ℕ → ℝ) : Prop :=
  IsDetailedStepOutput
    (compositeRegularizedModel (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h p σ)
    {s | x + s ∈ X} (fun s => {d | x + s + d ∈ X})
    (fun j s d => compositeModelDecrement (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h p σ j s d)
    q P.ς P.θ ε J s δs

variable {f : E → ℝ} {c : E → F} {h : F → ℝ} {X : Set E} {ε : ℕ → ℝ} {Lh : ℝ}

/-- **Existence of a step for ARqpC** ([cartis2022evaluation], Lemma 14.1.3). In finite
dimension, let `h` be subadditive with `h 0 = 0` and Lipschitz constant `L_h`, `X` closed,
`x ∈ X`, `‖∇^i f(x)‖ ≤ K_f` and `‖∇^i c(x)‖ ≤ K_c` for `i ∈ [2, p]` (`K_f ≥ 1`, `K_c ≥ 0`),
`σ > 0`, `1 ≤ q ≤ p`, `ε ∈ (0, 1]^q`, and let the orders `j ∈ [1, q]` outside the halving set
`J` be `j = 1` with `h` and `X` convex. Then the detailed Step 2 has an
output `(s, δ_s)` with `δ_{s,j} = 1` for `j ∉ J` and, if `‖s‖ < 1`,
`δ_{s,j} ≥ ςθ/(8(3(K_f + L_h K_c) + σ)) ε_j` for `j ∈ J ∩ [1, q]` ((14.1.24)). -/
theorem exists_isARqpCDetailedStep [FiniteDimensional ℝ E] (hLh : HasLipschitzConst h Lh)
    (hS : IsSubadditive h) (h0 : h 0 = 0) (P : ARqpParams) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hX : IsClosed X) {x : E} (hx : x ∈ X)
    {Kf Kc : ℝ} (hKf : 1 ≤ Kf) (hKc : 0 ≤ Kc)
    (hDf : ∀ i ∈ Finset.Icc 2 p, ‖iteratedFDeriv ℝ i f x‖ ≤ Kf)
    (hDc : ∀ i ∈ Finset.Icc 2 p, ‖iteratedFDeriv ℝ i c x‖ ≤ Kc) {σ : ℝ} (hσ : 0 < σ)
    {J : Set ℕ} (hJ : ∀ j ∈ Finset.Icc 1 q, j ∉ J → j = 1 ∧ ConvexOn ℝ univ h ∧ Convex ℝ X) :
    ∃ s δs, IsARqpCDetailedStep f c h X p q P ε J σ x s δs ∧ (∀ j ∉ J, δs j = 1) ∧
      (‖s‖ < 1 → ∀ j ∈ Finset.Icc 1 q, j ∈ J →
        P.ς * P.θ / (8 * (3 * (Kf + Lh * Kc) + σ)) * ε j ≤ δs j) := by
  set Df := ftaylorSeries ℝ f x
  set Dc := ftaylorSeries ℝ c x
  set mod := compositeRegularizedModel Df Dc h p σ
  set T : Set E := {s | x + s ∈ X}
  have hLh0 := hLh.nonneg
  set K := 3 * (Kf + Lh * Kc) + σ
  have hK : 3 ≤ K := by
    have : 0 ≤ Lh * Kc := mul_nonneg hLh0 hKc
    simp only [K]; linarith
  have hp : 1 ≤ p := hq.trans hqp
  have hTc : IsClosed T := hX.preimage (continuous_const.add continuous_id)
  have hT0 : (0 : E) ∈ T := by simpa [T] using hx
  obtain ⟨sstar, hsT, hmin⟩ := exists_isMinOn_compositeRegularizedModel
    (Df := Df) (Dc := Dc) (p := p) hLh hσ hTc hT0
  have hinf : sInf (mod '' T) = mod sstar :=
    IsLeast.csInf_eq ⟨⟨sstar, hsT, rfl⟩, by rintro _ ⟨t, ht, rfl⟩; exact isMinOn_iff.1 hmin t ht⟩
  rcases le_or_gt 1 ‖sstar‖ with hlong | hshort
  · -- a long step: returned at once (Step 2.3)
    refine ⟨sstar, fun _ => 1, ⟨1, ⟨one_pos, le_rfl⟩, Relation.ReflTransGen.single
      (DetailedStepTrans.ret hsT (by rw [hinf, one_mul]) hlong)⟩,
      fun _ _ => rfl, fun h' => absurd h' (not_lt.2 hlong)⟩
  · -- a short step: the argument of Lemma 12.2.9 (`exists_isDetailedStepOutput`)
    have hς := P.ς_pos
    have hθ := P.θ_pos
    set δbar : ℕ → ℝ := fun j => min 1 (P.ς * P.θ * ε j / (4 * K))
    have hfeas : ∀ d ∈ {d | x + sstar + d ∈ X}, sstar + d ∈ T := fun d hd => by
      simpa [T, add_assoc] using hd
    have hSd : IsClosed {d : E | x + sstar + d ∈ X} :=
      hX.preimage (continuous_const.add continuous_id)
    have hSd0 : (0 : E) ∈ {d : E | x + sstar + d ∈ X} := by simpa [T] using hsT
    obtain ⟨δs, hout, h1, h2⟩ := exists_isDetailedStepOutput (m := mod) (T := T)
      (Sd := fun s => {d | x + s + d ∈ X})
      (ΔT := fun j s d => compositeModelDecrement Df Dc h p σ j s d)
      (J := J) (δbar := δbar) (ε := ε) (ς := P.ς) (θ := P.θ) hq hsT
      (fun t ht => isMinOn_iff.1 hmin t ht) hfeas hSd0 hς P.ς_le_one hθ
      (fun j hj => (hε j hj).1)
      (fun j _ => by simp [compositeModelDecrement_def])
      (fun j _ δ hδ => by
        obtain ⟨d, hd, heq⟩ := exists_compositeTaylorMeasure_eq
          (Df := ftaylorSeries ℝ (regularizedModel Df p σ) sstar)
          (Dc := ftaylorSeries ℝ (Dc.taylorSum p) sstar) (h := h) (j := j)
          hLh.continuous hSd hSd0 hδ.1.le
        refine ⟨d, hd, fun d' hd' => ?_⟩
        simp only [compositeModelDecrement_def]
        rw [heq]
        exact compositeTaylorDecrement_le_compositeTaylorMeasure hLh hd')
      (fun j hj hjJ d hd => by
        obtain ⟨hj1, hconvh, hconvX⟩ := hJ j hj hjJ
        subst hj1
        have hTconv : Convex ℝ T := hconvX.translate_preimage_right x
        have hmloc : IsLocalMinOn (fun z => regularizedModel Df p σ z +
            h (Dc.taylorSum p z)) T sstar := hmin.isLocalMinOn
        exact compositeTaylorDecrement_one_nonpos_of_isLocalMinOn hTconv hsT
          ((contDiff_regularizedModel (D := Df) (p := p) (σ := σ)).differentiable
            (by exact_mod_cast Nat.one_le_iff_ne_zero.1 hp) sstar)
          ((Dc.contDiff_taylorSum p (n := 1)).differentiable one_ne_zero sstar)
          hconvh hLh hmloc (hfeas d hd.2))
      (fun j hj _ => ⟨lt_min one_pos (by have := (hε j hj).1; positivity), min_le_left _ _⟩)
      (fun j hj _ δ hδ d hd hdec => by
        have hj' : j ∈ Finset.Icc 1 p := Finset.mem_Icc.2
          ⟨(Finset.mem_Icc.1 hj).1, (Finset.mem_Icc.1 hj).2.trans hqp⟩
        have hδα : 4 * (3 * (Kf + Lh * Kc) + σ) * δ ≤ P.ς * P.θ * ε j := by
          have := hδ.2.trans (min_le_right _ _)
          rw [le_div_iff₀ (by positivity)] at this
          linarith
        have := compositeRegularizedModel_sub_ge_of_decrement_ge hLh hS h0
          (zero_le_one.trans hKf) hKc hDf hDc hσ.le hj' hshort.le hδ.1.le
          (hδ.2.trans (min_le_left _ _)) hδα (mem_closedBall_zero_iff.1 hd.1) hdec
        calc P.ς * P.θ * ε j * δ ^ j / (2 * j !) = P.ς * P.θ * ε j / 2 * δ ^ j / j ! := by
              field_simp
          _ ≤ _ := this)
    refine ⟨sstar, δs, hout, h1, fun _ j hj hjJ => (le_of_eq ?_).trans (h2 j hj hjJ)⟩
    have hε1 := hε j hj
    have hsm : P.ς * P.θ * ε j / (4 * K) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : P.ς * P.θ * ε j ≤ 1 := by
        have := P.ς_le_one; have := P.θ_lt_one.le
        have := hε1.1.le
        calc P.ς * P.θ * ε j ≤ 1 * 1 * 1 := by gcongr; exact hε1.2
          _ = 1 := by ring
      linarith
    simp only [δbar, min_eq_right hsm]
    field_simp
    ring

/-- An output of the detailed Step 2 satisfies the Step-2 conditions of the ARqp run
(`ARqpStep`) for suitable model displacements `dm` (finite dimension, `σ > 0`, `x ∈ X`, `X`
closed, `h` Lipschitz). -/
theorem IsARqpCDetailedStep.exists_arqpStep [FiniteDimensional ℝ E]
    (hLh : HasLipschitzConst h Lh) (hX : IsClosed X) {P : ARqpParams} {J : Set ℕ} {σ : ℝ}
    (hσ : 0 < σ) {x s : E} (hx : x ∈ X) {δs : ℕ → ℝ}
    (hout : IsARqpCDetailedStep f c h X p q P ε J σ x s δs) :
    ∃ dm : ℕ → E, ARqpStep X P q ε
      (ARqpData.ofComposite (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h p σ) x s δs dm := by
  classical
  obtain ⟨hsT, -, hrad, -, hbr⟩ := hout.spec
  have hTc : IsClosed {s : E | x + s ∈ X} := hX.preimage (continuous_const.add continuous_id)
  have hT0 : (0 : E) ∈ {s : E | x + s ∈ X} := by simpa using hx
  obtain ⟨smin, -, hmin⟩ := exists_isMinOn_compositeRegularizedModel
    (Df := ftaylorSeries ℝ f x) (Dc := ftaylorSeries ℝ c x) (p := p) hLh hσ hTc hT0
  have hbdd : BddBelow (compositeRegularizedModel (ftaylorSeries ℝ f x)
      (ftaylorSeries ℝ c x) h p σ '' {s | x + s ∈ X}) :=
    ⟨_, by rintro _ ⟨t, ht, rfl⟩; exact isMinOn_iff.1 hmin t ht⟩
  have hdm : ∀ j, ∃ d : E, j ∈ Finset.Icc 1 q → ‖s‖ < 1 →
      IsApproxMeasureStep (compositeModelDecrement (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h
          p σ j s) (δs j) {e | x + s + e ∈ X} P.ς d ∧
        compositeModelDecrement (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h p σ j s d ≤
          P.ς * P.θ * ε j * δs j ^ j / j ! := by
    intro j
    by_cases hj : j ∈ Finset.Icc 1 q
    · rcases hbr with hlong | hshort
      · exact ⟨0, fun _ h' => absurd hlong (not_le.2 h')⟩
      · obtain ⟨d, hd, h1, h2⟩ := hshort j hj
        exact ⟨d, fun _ _ => ⟨⟨hd, h1⟩, h2⟩⟩
    · exact ⟨0, fun h' => absurd h' hj⟩
  choose dm hdm using hdm
  refine ⟨dm, ⟨hsT, hout.le_of_bddBelow hT0 hbdd, fun heq => hout.isMinOn_of_eq hbdd heq,
    fun j _ => (hrad j).1, fun j _ => (hrad j).2, ?_⟩⟩
  rcases le_or_gt 1 ‖s‖ with hlong | hshort
  · exact Or.inl hlong
  · exact Or.inr fun j hj => hdm j hj hshort

/-- **Existence of ARqpC runs** ([cartis2022evaluation], Algorithms 14.1.1–14.1.2 are well
defined; no smoothness is needed): in finite dimension, for any `f`, `c`, a Lipschitz subadditive
`h` with `h 0 = 0`, a closed feasible set `X`, `x₀ ∈ X`, `1 ≤ q ≤ p`, `ε ∈ (0, 1]^q`,
`δ₀ ∈ (0, 1]^q` and a halving set `J` as in `exists_isARqpCDetailedStep`, there is an ARqpC run
from `x₀` whose Step-2 pairs are outputs of the detailed Step 2 at every iteration reached. -/
theorem exists_isARqpRun_composite [FiniteDimensional ℝ E] (hLh : HasLipschitzConst h Lh)
    (hS : IsSubadditive h) (h0 : h 0 = 0) (P : ARqpParams) (hq : 1 ≤ q) (hqp : q ≤ p)
    {δ₀ : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) (hX : IsClosed X) {x₀ : E} (hx₀ : x₀ ∈ X)
    {J : Set ℕ} (hJ : ∀ j ∈ Finset.Icc 1 q, j ∉ J → j = 1 ∧ ConvexOn ℝ univ h ∧ Convex ℝ X) :
    ∃ (x s : ℕ → E) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E), x 0 = x₀ ∧
      IsARqpRun (fun y => f y + h (c y)) X P q ε δ₀ (arqpcData f c h p x σ) x s σ δ δs d dm ∧
      ∀ k, (∀ i < k, ¬ arqpcStop f c h P p q ε x s σ δ d i) →
        IsARqpCDetailedStep f c h X p q P ε J (σ k) (x k) (s k) (δs k) := by
  refine exists_isARqpRun_of_forall (fun y => f y + h (c y)) X P hδ₀
    (fun y σ => ARqpData.ofComposite (ftaylorSeries ℝ f y) (ftaylorSeries ℝ c y) h p σ)
    (fun y σ s δs _ => IsARqpCDetailedStep f c h X p q P ε J σ y s δs)
    (fun y hy δ hδ => ?_) (fun y hy σ hσ => ?_) hx₀
  · have h' : ∀ j, ∃ dj : E, j ∈ Finset.Icc 1 q → IsApproxMeasureStep
        (compositeTaylorDecrement (ftaylorSeries ℝ f y) (ftaylorSeries ℝ c y) h j) (δ j)
        {e | y + e ∈ X} P.ς dj := by
      intro j
      by_cases hj : j ∈ Finset.Icc 1 q
      · obtain ⟨dj, hdj⟩ := exists_isApproxMeasureStep
          (hX.preimage (continuous_const.add continuous_id)) (by simpa using hy) (hδ j hj).1.le
          (continuous_compositeTaylorDecrement _ _ h j hLh.continuous).continuousOn
          (compositeTaylorDecrement_zero_right _ _ h j) P.ς_le_one
        exact ⟨dj, fun _ => hdj⟩
      · exact ⟨0, fun h'' => absurd h'' hj⟩
    choose d hd using h'
    exact ⟨d, fun _ j hj => hd j hj⟩
  · have hDf : ∀ i ∈ Finset.Icc 2 p, ‖iteratedFDeriv ℝ i f y‖ ≤
        1 + ∑ l ∈ Finset.Icc 2 p, ‖iteratedFDeriv ℝ l f y‖ := fun i hi =>
      (Finset.single_le_sum (f := fun l => ‖iteratedFDeriv ℝ l f y‖)
        (fun _ _ => norm_nonneg _) hi).trans (le_add_of_nonneg_left zero_le_one)
    have hDc : ∀ i ∈ Finset.Icc 2 p, ‖iteratedFDeriv ℝ i c y‖ ≤
        ∑ l ∈ Finset.Icc 2 p, ‖iteratedFDeriv ℝ l c y‖ := fun i hi =>
      Finset.single_le_sum (f := fun l => ‖iteratedFDeriv ℝ l c y‖)
        (fun _ _ => norm_nonneg _) hi
    obtain ⟨s, δs, hout, -⟩ := exists_isARqpCDetailedStep hLh hS h0 P hq hqp hε hX hy
      (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _))
      (Finset.sum_nonneg fun _ _ => norm_nonneg _) hDf hDc hσ hJ
    obtain ⟨dm, hdm⟩ := hout.exists_arqpStep hLh hX hσ hy
    exact ⟨s, δs, dm, hdm, hout⟩

/-- **Global model minimizers are outputs of the detailed Step 2 for `q = 1`** (convex `h` and
`X`, any halving set): if `x + s ∈ X` and `s` globally minimizes the composite model over the
feasible steps, then `(s, 1)` is an output: a long step is returned at once, and for a short step
the order-`1` model decrements at `s` are nonpositive (first-order necessity for the model), so
the displacement `0` passes the order-`1` test with radius `1`. -/
theorem isARqpCDetailedStep_of_isMinOn (hp : 1 ≤ p) (hLh : HasLipschitzConst h Lh)
    (hconv : ConvexOn ℝ univ h) (hX : Convex ℝ X) (P : ARqpParams) (J : Set ℕ) (hε : 0 ≤ ε 1)
    {σ : ℝ} {x s : E} (hs : x + s ∈ X)
    (hmin : IsMinOn (compositeRegularizedModel (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h p σ)
      {t | x + t ∈ X} s) :
    IsARqpCDetailedStep f c h X p 1 P ε J σ x s (fun _ => 1) := by
  set mod := compositeRegularizedModel (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h p σ
  set T : Set E := {t | x + t ∈ X}
  have hsT : s ∈ T := hs
  have hinf : sInf (mod '' T) = mod s :=
    IsLeast.csInf_eq ⟨⟨s, hsT, rfl⟩, by rintro _ ⟨t, ht, rfl⟩; exact isMinOn_iff.1 hmin t ht⟩
  rcases le_or_gt 1 ‖s‖ with hlong | hshort
  · exact ⟨1, ⟨one_pos, le_rfl⟩, Relation.ReflTransGen.single
      (DetailedStepTrans.ret hsT (by rw [hinf, one_mul]) hlong)⟩
  set D : Set E := closedBall (0 : E) 1 ∩ {d | x + s + d ∈ X}
  have hnp : ∀ d ∈ D, compositeModelDecrement (ftaylorSeries ℝ f x)
      (ftaylorSeries ℝ c x) h p σ 1 s d ≤ 0 := fun d hd =>
    compositeTaylorDecrement_one_nonpos_of_isLocalMinOn
      (hX.translate_preimage_right x) hsT
      ((contDiff_regularizedModel (D := ftaylorSeries ℝ f x) (p := p)
        (σ := σ)).differentiable (by exact_mod_cast Nat.one_le_iff_ne_zero.1 hp) s)
      (((ftaylorSeries ℝ c x).contDiff_taylorSum p (n := 1)).differentiable one_ne_zero s)
      hconv hLh hmin.isLocalMinOn (by simpa [T, add_assoc] using hd.2)
  have h0 : (0 : E) ∈ D := ⟨by simp, by simpa using hs⟩
  have hsup : sSup ((fun d => compositeModelDecrement (ftaylorSeries ℝ f x)
      (ftaylorSeries ℝ c x) h p σ 1 s d) '' D) ≤ 0 :=
    csSup_le ⟨_, ⟨0, h0, rfl⟩⟩ (by rintro _ ⟨d, hd, rfl⟩; exact hnp d hd)
  have hdec0 : compositeModelDecrement (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x)
      h p σ 1 s 0 = 0 := by
    simp [compositeModelDecrement_def]
  refine ⟨1, ⟨one_pos, le_rfl⟩, Relation.ReflTransGen.head
    (DetailedStepTrans.start hsT (by rw [hinf, one_mul]) hshort)
    (Relation.ReflTransGen.single (DetailedStepTrans.finish (d := 0) h0 ?_ ?_ le_rfl))⟩
  · rw [hdec0]
    exact mul_nonpos_of_nonneg_of_nonpos P.ς_pos.le hsup
  · rw [hdec0]
    have := P.ς_pos
    have := P.θ_pos
    positivity

end Optimization
