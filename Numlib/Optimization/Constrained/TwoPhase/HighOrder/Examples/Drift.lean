import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.Plane

/-!
# A Phase-2 run that never terminates

On `ℝ²`, with `X = {x | |x₁| ≤ 3}`, `f(x) = x₂ - x₁`, `c(x) = 3/5 + x₂ ∈ ℝ¹`, `θ = 3/5`,
`ε₀ = ε₁ = 1` and `q = 1`, Phase-2 data of a high-order target-following method with one-step
inner calls (`Constrained.HighOrderTargetSeq.oneStep`) form a run
(`Constrained.IsHighOrderTargetRun`) that never terminates: the outer iterates are
`x_k = (-(24/5) 2^{-k}, 0)`, the targets `t_k = (16/5) 2^{-k}`, and the radii `1`. Then
`f(x_{k+1}) = t_k - a_k` with `a_k = (4/5) 2^{-k}`, so every outer iteration is in `𝒦_b` and
`t_{k+1} = t_k - 2 a_k` (14.3.35). Each call ends at a point passing the criticality test
(14.3.34) for the old target (`‖∇μ(x_{k+1}, t_k)‖² = θ² + 2a_k² - 2θa_k ≤ θ² + a_k²`), so the
end-criticality contract `Constrained.HighOrderTargetSeq.IsEndCritContract` holds with every
constant and no iteration is good; and (14.3.34) fails at `x_{k+1}` for `t_{k+1}` (along
`d = -e₂` the decrease is `θ + a_k > √(θ² + a_k²)`), so Phase 2 does not stop. The inner-test
contract `Constrained.HighOrderTargetSeq.IsInnerTestContract` fails for every admissible constant,
since otherwise Phase 2 would terminate
(`Constrained.IsHighOrderTargetRun.complexity_of_innerTest`).

## Main definitions

* `Constrained.TwoPhaseExample.Drift.strip`, `obj`, `con`: the problem data;
* `Constrained.TwoPhaseExample.Drift.iter`, `seq`: the outer iterates and the Phase-2 data.

## Main results

* `Constrained.TwoPhaseExample.Drift.isHighOrderTargetRun`: the data form a run;
* `Constrained.TwoPhaseExample.Drift.not_stop`, `before`: it never terminates;
* `Constrained.TwoPhaseExample.Drift.isEndCritContract`: its calls satisfy the end-criticality
  contract with every constant;
* `Constrained.TwoPhaseExample.Drift.not_isInnerTestContract`: they satisfy no inner-test
  contract;
* `Constrained.TwoPhaseExample.Drift.badCount_eq`: `K - 1` bad outer iterations before `K`.
-/

open Set Metric
open scoped RealInnerProductSpace

namespace Constrained.TwoPhaseExample.Drift

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

/-- The simple constraint set `X = {x ∈ ℝ² | |x₁| ≤ 3}`. -/
def strip : Set ℝ² := {x | |x 0| ≤ 3}

/-- The objective `f(x) = x₂ - x₁`. -/
def obj : ℝ² → ℝ := linObj (-1) 1

/-- The constraint `c(x) = 3/5 + x₂`. -/
noncomputable def con : ℝ² → ℝ¹ := fun x => (3 / 5 + x 1) • unitVec

/-- The outer iterates `x_k = (-(24/5) 2^{-k}, 0)`. -/
noncomputable def iter (k : ℕ) : ℝ² := pt (-(24 / 5) * (1 / 2) ^ k) 0

/-- The Phase-2 data: iterates `x_k = iter k`, targets
`t_k = (16/5) 2^{-k}`, radii `1`, and the `k`-th inner call makes one successful iteration from
`x_k` to `x_{k+1}`. -/
noncomputable def seq : HighOrderTargetSeq ℝ² :=
  HighOrderTargetSeq.oneStep iter fun k => 16 / 5 * (1 / 2) ^ k

theorem obj_apply (y : ℝ²) : obj y = y 1 - y 0 := by simp [obj, linObj]; ring

theorem iter_apply_one (k : ℕ) : iter k 1 = 0 := pt_one _ _

theorem iter_apply_zero (k : ℕ) : iter k 0 = -(24 / 5) * (1 / 2) ^ k := pt_zero _ _

/-- `f(x_k) = (24/5) 2^{-k}`. -/
theorem obj_iter (k : ℕ) : obj (iter k) = 24 / 5 * (1 / 2) ^ k := by
  rw [obj_apply, iter_apply_one, iter_apply_zero]; ring

theorem norm_con (y : ℝ²) : ‖con y‖ = |3 / 5 + y 1| := norm_smul_unitVec _

theorem hasFDerivAt_con (y : ℝ²) :
    HasFDerivAt con ((EuclideanSpace.proj (1 : Fin 2) : ℝ² →L[ℝ] ℝ).smulRight unitVec) y := by
  have := ((hasFDerivAt_const (3 / 5 : ℝ) y).add
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y 1)).smul_const unitVec
  exact this.congr_fderiv (ContinuousLinearMap.ext fun d => by simp)

/-- The first-order Taylor decrement of `μ(·, t)` at a point `y` with `y₂ = 0`:
`-∇μ(y, t)[d] = (f(y) - t) d₁ - (f(y) - t + 3/5) d₂`. -/
theorem taylorDecrement_one {y : ℝ²} (hy : y 1 = 0) (t : ℝ) (d : ℝ²) :
    (ftaylorSeries ℝ (Constrained.targetMerit obj con t) y).taylorDecrement 1 d =
      (obj y - t) * d 0 - (obj y - t + 3 / 5) * d 1 := by
  rw [Constrained.taylorDecrement_one_targetMerit (f := obj) (hasFDerivAt_linObj _ _ y)
    (hasFDerivAt_con y)]
  simp [con, unitVec, hy, inner_smul_left, inner_smul_right]
  ring

/-- An upper bound on the first-order measure (Cauchy–Schwarz). -/
theorem taylorMeasure_le {y : ℝ²} (hy : y 1 = 0) (t : ℝ) {S : Set ℝ²} (h0 : (0 : ℝ²) ∈ S) :
    Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit obj con t) y) 1 1 S ≤
      √((obj y - t) ^ 2 + (obj y - t + 3 / 5) ^ 2) := by
  have := decrementMeasure_lin_le_sqrt (a := obj y - t) (b := -(obj y - t + 3 / 5))
    (Δ := (ftaylorSeries ℝ (Constrained.targetMerit obj con t) y).taylorDecrement 1)
    (fun d => by rw [taylorDecrement_one hy]; ring) h0
  rwa [neg_sq] at this

/-- A lower bound on the first-order measure, along `d = -e₂`. -/
theorem le_taylorMeasure {y : ℝ²} (hy : y 1 = 0) (t : ℝ) {S : Set ℝ²}
    (hS : EuclideanSpace.single 1 (-1) ∈ S) :
    obj y - t + 3 / 5 ≤
      Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit obj con t) y) 1 1
        S := by
  have := Optimization.taylorDecrement_le_taylorMeasure
    (ftaylorSeries ℝ (Constrained.targetMerit obj con t) y) 1 (δ := 1)
    (d := EuclideanSpace.single 1 (-1)) ⟨by simp, hS⟩
  rw [taylorDecrement_one hy] at this
  simpa using this

/-- `‖r(y, t)‖ = √((3/5)² + (f(y) - t)²)` when `y₂ = 0`. -/
theorem targetResidual_eq {y : ℝ²} (hy : y 1 = 0) (t : ℝ) :
    Constrained.targetResidual obj con t y = √((3 / 5) ^ 2 + (obj y - t) ^ 2) := by
  rw [Constrained.targetResidual_def, norm_con, hy, add_zero, abs_of_pos (by norm_num)]

/-- The test (14.3.34) for `q = 1`, `ε₁ = 1` and radius `1`: `φ^1_{μ,X(y),1}(y, t) ≤ ‖r(y, t)‖`. -/
theorem targetCrit_iff {y : ℝ²} {t : ℝ} :
    targetCrit obj con strip 1 (fun _ => 1) t y (fun _ => 1) ↔
      Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit obj con t) y) 1 1
        {d | y + d ∈ strip} ≤ Constrained.targetResidual obj con t y := by
  simp [targetCrit, Constrained.targetCrit]

/-- `|-(24/5) 2^{-(k+1)} + a| ≤ 3` for `|a| ≤ 3/5`. -/
private theorem abs_iter_add_le (k : ℕ) {a : ℝ} (ha : |a| ≤ 3 / 5) :
    |-(24 / 5) * (1 / 2) ^ (k + 1) + a| ≤ 3 := by
  have := abs_le.1 ha
  rw [abs_le]; constructor <;> nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k,
    pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := k),
    pow_succ (1 / 2 : ℝ) k]

/-- The new iterate `x_{k+1}` passes the criticality test (14.3.34) for the old target `t_k`. -/
theorem targetCrit_old (k : ℕ) :
    targetCrit obj con strip 1 (fun _ => 1) (16 / 5 * (1 / 2) ^ k) (iter (k + 1))
      (fun _ => 1) := by
  rw [targetCrit_iff]
  have h0 : (0 : ℝ²) ∈ {d | iter (k + 1) + d ∈ strip} := by
    simpa [strip, iter_apply_zero] using abs_iter_add_le k (a := 0) (by norm_num)
  refine (taylorMeasure_le (iter_apply_one _) _ h0).trans ?_
  rw [targetResidual_eq (iter_apply_one _), obj_iter]
  refine Real.sqrt_le_sqrt ?_
  have hw := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k
  have hw1 := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := k)
  have e : (1 / 2 : ℝ) ^ (k + 1) = (1 / 2) ^ k / 2 := by rw [pow_succ]; ring
  rw [e]
  nlinarith

/-- The new iterate `x_{k+1}` fails (14.3.34) for the new target `t_{k+1}`. -/
theorem not_targetCrit_new (k : ℕ) :
    ¬ targetCrit obj con strip 1 (fun _ => 1) (16 / 5 * (1 / 2) ^ (k + 1)) (iter (k + 1))
      (fun _ => 1) := by
  rw [targetCrit_iff, not_le]
  have hS : EuclideanSpace.single 1 (-1) ∈ {d | iter (k + 1) + d ∈ strip} := by
    have e : (EuclideanSpace.single (1 : Fin 2) (-1 : ℝ)) 0 = 0 := by simp
    simpa [strip, iter_apply_zero, e] using abs_iter_add_le k (a := 0) (by norm_num)
  refine lt_of_lt_of_le ?_ (le_taylorMeasure (iter_apply_one _) _ hS)
  rw [targetResidual_eq (iter_apply_one _), obj_iter]
  have hw := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (k + 1)
  rw [Real.sqrt_lt' (by nlinarith)]
  nlinarith

/-- `‖r(y, t)‖ ≥ 3/5 = θε₀` when `y₂ = 0`. -/
theorem le_targetResidual {y : ℝ²} (hy : y 1 = 0) (t : ℝ) :
    3 / 5 ≤ Constrained.targetResidual obj con t y := by
  rw [targetResidual_eq hy]
  calc (3 / 5 : ℝ) = √((3 / 5) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (obj y - t)])

/-- No outer iteration is in `𝒦_a`. -/
theorem not_isKa (k : ℕ) : ¬ seq.IsKa obj con (3 / 5) (fun _ => 1) k := by
  rw [Constrained.HighOrderTargetSeq.isKa_iff]
  rw [mul_one, not_lt]
  exact le_targetResidual (iter_apply_one _) _

/-- Every outer iteration is in `𝒦_b`. -/
theorem isKb (k : ℕ) : seq.IsKb obj con (3 / 5) (fun _ => 1) k := by
  refine ⟨by rw [mul_one]; exact le_targetResidual (iter_apply_one _) _, ?_⟩
  change obj (iter (k + 1)) < 16 / 5 * (1 / 2) ^ k
  rw [obj_iter, pow_succ]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k]

/-- Phase 2 never terminates. -/
theorem not_stop (k : ℕ) : ¬ seq.Stop obj con strip 1 (3 / 5) (fun _ => 1) k := by
  rintro (⟨-, hb⟩ | ⟨-, hm⟩)
  · exact hb (isKb k)
  · exact not_targetCrit_new k hm

/-- Every outer iteration is reached. -/
theorem before (K : ℕ) : seq.Before obj con strip 1 (3 / 5) (fun _ => 1) K :=
  fun k _ _ => not_stop k

/-- No inner call contains a good iteration. -/
theorem goodCount_eq_zero (k : ℕ) : seq.goodCount obj con strip 1 (3 / 5) (fun _ => 1) k = 0 := by
  classical
  rw [Constrained.HighOrderTargetSeq.goodCount,
      Constrained.TargetFollowingSeq.goodCount_eq_zero_iff]
  rintro i - ⟨hi, -, h | h, -⟩
  · exact absurd h (by change ¬ i + 1 < 1; omega)
  · exact h (targetCrit_old k)

/-- The iterates `x_k`, `k ≥ 1`, lie in `X`. -/
theorem iter_mem {k : ℕ} (hk : 1 ≤ k) : iter k ∈ strip := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  simpa [strip, iter_apply_zero] using abs_iter_add_le k (a := 0) (by norm_num)

/-- `f` is smooth. -/
theorem contDiff_obj : ContDiff ℝ ⊤ obj := contDiff_linObj _ _

/-- `c` is smooth. -/
theorem contDiff_con : ContDiff ℝ ⊤ con := by
  have h1 : ContDiff ℝ ⊤ (fun x : ℝ² => 3 / 5 + x 1) :=
    contDiff_const.add (contDiff_piLp_apply (p := 2))
  exact h1.smul contDiff_const

/-- `‖∇f‖ ≤ 2`. -/
theorem norm_iteratedFDeriv_obj_le (y : ℝ²) :
    ∀ i ∈ Finset.Icc 1 1, ‖iteratedFDeriv ℝ i obj y‖ ≤ 2 :=
  fun i hi => (norm_iteratedFDeriv_linObj_le (-1) 1 y i hi).trans (by norm_num)

/-- `-5 ≤ f ≤ 4` on `{x ∈ X | ‖c(x)‖ ≤ 1}`. -/
theorem obj_mem_Icc {x : ℝ²} (hxX : x ∈ strip) (hcx : ‖con x‖ ≤ 1) : -5 ≤ obj x ∧ obj x ≤ 4 := by
  rw [norm_con] at hcx
  have h0 := abs_le.1 (show |x 0| ≤ 3 from hxX)
  have h1 := abs_le.1 hcx
  rw [obj_apply]
  constructor <;> linarith

/-- The data form a run of Phase 2 from `x₁ = (-12/5, 0)` for `θ = 3/5`, `ε_j = 1` and every
`β ∈ (0, 3/5]`. -/
theorem isHighOrderTargetRun {β : ℝ} (hβ : 0 < β) (hβθ : β ≤ 3 / 5) :
    IsHighOrderTargetRun obj con strip 1 (3 / 5) β (fun _ => 1) (iter 1) seq := by
  have hc1 : ‖con (iter 1)‖ = 3 / 5 := by
    rw [norm_con, iter_apply_one, add_zero, abs_of_pos (by norm_num)]
  refine isHighOrderTargetRun_oneStep (by norm_num) (by norm_num) hβ hβθ (fun _ _ => one_pos)
    (fun _ _ => le_rfl) (iter_mem le_rfl) (by rw [hc1]; norm_num) ?_
    (fun k _ _ => iter_mem (by omega)) (fun k _ _ => Or.inr (Or.inl (isKb k).2))
    (fun k _ _ => ?_) (fun k _ _ => by simpa using le_targetResidual (iter_apply_one k) _)
    (fun k _ _ ha => absurd ha (not_isKa k)) (fun k _ _ _ => ?_)
  · change (16 / 5 : ℝ) * (1 / 2) ^ 1 = obj (iter 1) - √(1 ^ 2 - ‖con (iter 1)‖ ^ 2)
    rw [hc1, obj_iter, show (1 : ℝ) ^ 2 - (3 / 5) ^ 2 = (4 / 5) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
    norm_num
  · change Constrained.targetMerit obj con (16 / 5 * (1 / 2) ^ k) (iter (k + 1)) ≤
      Constrained.targetMerit obj con (16 / 5 * (1 / 2) ^ k) (iter k)
    rw [Constrained.targetMerit_def, Constrained.targetMerit_def, norm_con, norm_con,
      iter_apply_one, iter_apply_one, obj_iter, obj_iter]
    have e : (1 / 2 : ℝ) ^ (k + 1) = (1 / 2) ^ k / 2 := by rw [pow_succ]; ring
    rw [e]
    have hw := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k
    nlinarith
  · change (16 / 5 : ℝ) * (1 / 2) ^ (k + 1) = 2 * obj (iter (k + 1)) - 16 / 5 * (1 / 2) ^ k
    rw [obj_iter, pow_succ]
    ring

/-- `X` is closed. -/
theorem isClosed_strip : IsClosed strip :=
  isClosed_le (continuous_abs.comp (EuclideanSpace.proj (0 : Fin 2)).continuous) continuous_const

/-- **The end-criticality contract** holds for every `β ∈ (0, 3/5]`, `κ_decr`, `π` and
`κ_uns + κ_unc ≥ 1`: each call ends at a point passing (14.3.34) for the old target. -/
theorem isEndCritContract {β κdecr κuns κunc : ℝ} {π : ℕ → ℝ} (hκ : 1 ≤ κuns + κunc) :
    seq.IsEndCritContract obj con strip 1 (3 / 5) β (fun _ => 1) κdecr κuns κunc π :=
  HighOrderTargetSeq.isEndCritContract_oneStep hκ fun k _ _ => targetCrit_old k

/-- **No inner-test contract holds**: for `β ∈ (0, 3/5]`, `κ_decr > 0`, `κ_uns ≥ 0`, `π₁ ≥ 0`
and `ρ₁ ≥ 0`, the calls do not satisfy `HighOrderTargetSeq.IsInnerTestContract`, since Phase 2
would then terminate (`IsHighOrderTargetRun.complexity_of_innerTest`, with `B_f = 2` and
`τ = η/4`, `η = kbMargin θ ε₀`). -/
theorem not_isInnerTestContract {β κdecr κuns κunc : ℝ} {π ρ : ℕ → ℝ} (hβ : 0 < β)
    (hβθ : β ≤ 3 / 5) (hκ : 0 < κdecr) (hκuns : 0 ≤ κuns) (hπ : 0 ≤ π 1) (hρ : 0 ≤ ρ 1) :
    ¬ seq.IsInnerTestContract obj con strip 1 (3 / 5) β (fun _ => 1) κdecr κuns κunc π ρ := by
  intro hs
  have hI : ∀ {j : ℕ}, j ∈ Finset.Icc 1 1 → j = 1 := fun hj => by simpa using hj
  have hη : 0 < kbMargin (3 / 5) 1 := by rw [kbMargin_def]; norm_num
  obtain ⟨-, kε, hend, -⟩ := (isHighOrderTargetRun hβ hβθ).complexity_of_innerTest hs hκ hκuns
    (πmax := π 1) (M := 1) (fun l hl => by obtain rfl := hI hl; exact ⟨hπ, le_rfl⟩) one_pos
    (fun l hl => by obtain rfl := hI hl; simp) (fun z hz hcz => obj_mem_Icc hz hcz)
    (fun j hj => by obtain rfl := hI hj; exact hρ)
    (fun _ _ => (contDiff_obj.of_le le_top).contDiffAt)
    (fun _ _ => (contDiff_con.of_le le_top).contDiffAt) (fun y _ _ => norm_iteratedFDeriv_obj_le y)
    (div_pos hη (by norm_num : (0 : ℝ) < 4))
    (fun j hj => by obtain rfl := hI hj; simp; linarith)
  exact not_stop kε hend.2.1

/-- **Every outer iteration is bad**: `n_bad(K) = K - 1`. -/
theorem badCount_eq (K : ℕ) : seq.badCount obj con strip 1 (3 / 5) (fun _ => 1) K = K - 1 := by
  classical
  rw [HighOrderTargetSeq.badCount, TargetFollowingSeq.badCount_eq_card_filter,
    Finset.filter_true_of_mem fun k _ => ⟨isKb k, goodCount_eq_zero k⟩, Nat.card_Ico]

end Constrained.TwoPhaseExample.Drift
