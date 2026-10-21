import Numlib.Analysis.SpecialFunctions.TaylorBetaKernel
import Numlib.Optimization.TaylorModelDerivatives
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Sharp Hölder remainders for Taylor models

Subtracting the highest homogeneous term gives a centered integral remainder.
Its beta-kernel estimate applies to maps into arbitrary Banach spaces. Applying
this bound recursively to derivative-valued maps controls every model derivative.
-/

open Optimization.RegularizedTaylorModel
open Set
open scoped Nat ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Taylor's integral remainder after subtracting the highest homogeneous term. -/
theorem sub_taylorModel_eq_integral_iteratedFDeriv_sub {f : E → F} {n : ℕ} {x s : E}
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (n + 1) f (x + t • s)) :
    f (x + s) - taylorModel f (n + 1) x s =
      ∫ t : ℝ in 0..1, ((1 - t) ^ n / (n ! : ℝ)) •
        ((iteratedFDeriv ℝ (n + 1) f (x + t • s) - iteratedFDeriv ℝ (n + 1) f x)
          (fun _ ↦ s)) := by
  have hc : ContinuousOn (fun t : ℝ ↦ iteratedFDeriv ℝ (n + 1) f (x + t • s)
      (fun _ ↦ s)) (Icc 0 1) := by
    intro t ht
    exact (((hf t ht).iteratedFDeriv_right (i := n + 1) (m := 0) (by simp)).continuousAt.comp
      (x := t) (by fun_prop)).continuousWithinAt.eval_const _
  have hI : IntervalIntegrable (fun t : ℝ ↦ ((1 - t) ^ n / (n ! : ℝ)) •
      iteratedFDeriv ℝ (n + 1) f (x + t • s) (fun _ ↦ s)) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact ContinuousOn.smul (by fun_prop) hc
  have hC : IntervalIntegrable (fun t : ℝ ↦ ((1 - t) ^ n / (n ! : ℝ)) •
      iteratedFDeriv ℝ (n + 1) f x (fun _ ↦ s)) MeasureTheory.volume 0 1 := by
    exact (by fun_prop : Continuous _).intervalIntegrable _ _
  have hT := map_add_eq_sum_add_integral_iteratedFDeriv hf
  change f (x + s) = taylorModel f n x s + _ at hT
  have hK : (∫ t : ℝ in 0..1, (1 - t) ^ n / (n ! : ℝ)) =
      ((n + 1)! : ℝ)⁻¹ := by
    simpa using integral_taylor_kernel (x := (0 : ℝ)) (y := 1) n
  simp_rw [sub_apply, smul_sub]
  rw [intervalIntegral.integral_sub hI hC, intervalIntegral.integral_smul_const, hK,
    taylorModel_succ, hT]
  have hnorm : (n ! : ℝ)⁻¹ • (∫ t : ℝ in 0..1, (1 - t) ^ n •
      iteratedFDeriv ℝ (n + 1) f (x + t • s) (fun _ ↦ s)) =
      ∫ t : ℝ in 0..1, ((1 - t) ^ n / (n ! : ℝ)) •
        iteratedFDeriv ℝ (n + 1) f (x + t • s) (fun _ ↦ s) := by
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [smul_smul]
    congr 1
    ring
  rw [hnorm]
  abel

/-- A sharp Hölder remainder from bounds only on the repeated step direction. No control
of mixed multilinear directions is needed for this value estimate. -/
theorem norm_sub_taylorModel_le_holder_of_diagonal {f : E → F} {n : ℕ} {x s : E} {H β : ℝ}
    (hβ : 0 ≤ β)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (n + 1) f (x + t • s))
    (hH : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(iteratedFDeriv ℝ (n + 1) f (x + t • s) -
        iteratedFDeriv ℝ (n + 1) f x) (fun _ ↦ s)‖ ≤
        H * ‖t • s‖ ^ β * ‖s‖ ^ (n + 1)) :
    ‖f (x + s) - taylorModel f (n + 1) x s‖ ≤
      H / (∏ i ∈ Finset.range (n + 1), (((i + 1 : ℕ) : ℝ) + β)) *
        ‖s‖ ^ ((n + 1 : ℕ) + β) := by
  rw [sub_taylorModel_eq_integral_iteratedFDeriv_sub hf]
  have hcont : ContinuousOn (fun t : ℝ ↦
      ((1 - t) ^ n / (n ! : ℝ)) * t ^ β * (H * ‖s‖ ^ ((n + 1 : ℕ) + β)))
      (uIcc 0 1) := by
    apply ContinuousOn.mul
    · exact ContinuousOn.mul (by fun_prop)
        (continuousOn_id.rpow_const fun _ _ ↦ Or.inr hβ)
    · exact continuousOn_const
  have hb : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖((1 - t) ^ n / (n ! : ℝ)) •
        ((iteratedFDeriv ℝ (n + 1) f (x + t • s) - iteratedFDeriv ℝ (n + 1) f x)
          (fun _ ↦ s))‖ ≤
        ((1 - t) ^ n / (n ! : ℝ)) * t ^ β *
          (H * ‖s‖ ^ ((n + 1 : ℕ) + β)) := by
    intro t ht
    have hpow : 0 ≤ (1 - t) ^ n / (n ! : ℝ) :=
      div_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) _) (by positivity)
    rw [norm_smul, Real.norm_of_nonneg hpow]
    calc
      _ ≤ ((1 - t) ^ n / (n ! : ℝ)) * (H * ‖t • s‖ ^ β * ‖s‖ ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left (hH t ht) hpow
      _ = _ := by
        rw [norm_smul, Real.norm_of_nonneg ht.1, Real.mul_rpow ht.1 (norm_nonneg _),
          Real.rpow_add_of_nonneg (norm_nonneg _) (by positivity) hβ, Real.rpow_natCast]
        ring
  calc
    _ ≤ ∫ t : ℝ in 0..1, ((1 - t) ^ n / (n ! : ℝ)) * t ^ β *
        (H * ‖s‖ ^ ((n + 1 : ℕ) + β)) :=
      intervalIntegral.norm_integral_le_of_norm_le zero_le_one
        (MeasureTheory.ae_of_all _ (fun t ht ↦ hb t (Ioc_subset_Icc_self ht)))
        hcont.intervalIntegrable
    _ = _ := by
      rw [intervalIntegral.integral_mul_const]
      have hnorm : (∫ t : ℝ in 0..1, ((1 - t) ^ n / (n ! : ℝ)) * t ^ β) =
          (n ! : ℝ)⁻¹ * (∫ t : ℝ in 0..1, t ^ β * (1 - t) ^ n) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only
        ring
      rw [hnorm, integral_rpow_mul_one_sub_pow hβ n]
      have hn : (n ! : ℝ) ≠ 0 := by positivity
      field_simp
/-- The sharp Hölder remainder of a Taylor model on a segment. The highest derivative
is measured in the multilinear operator norm. -/
theorem norm_sub_taylorModel_le_holder {f : E → F} {n : ℕ} {x s : E} {H β : ℝ}
    (hβ : 0 ≤ β)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (n + 1) f (x + t • s))
    (hH : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (n + 1) f (x + t • s) - iteratedFDeriv ℝ (n + 1) f x‖ ≤
        H * ‖t • s‖ ^ β) :
    ‖f (x + s) - taylorModel f (n + 1) x s‖ ≤
      H / (∏ i ∈ Finset.range (n + 1), (((i + 1 : ℕ) : ℝ) + β)) *
        ‖s‖ ^ ((n + 1 : ℕ) + β) := by
  apply norm_sub_taylorModel_le_holder_of_diagonal hβ hf
  intro t ht
  calc
    _ ≤ ‖iteratedFDeriv ℝ (n + 1) f (x + t • s) -
        iteratedFDeriv ℝ (n + 1) f x‖ * ‖s‖ ^ (n + 1) := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ (n + 1) f (x + t • s) -
          iteratedFDeriv ℝ (n + 1) f x).le_opNorm (fun _ ↦ s)
    _ ≤ _ := mul_le_mul_of_nonneg_right (hH t ht) (pow_nonneg (norm_nonneg s) _)

universe u v

/-- Sharp Hölder bounds for every derivative of the canonical Taylor model, with
finite smoothness at every point on the segment. -/
theorem norm_iteratedFDeriv_sub_taylorModel_le_holder {E : Type u} {F : Type (max u v)}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {f : E → F} {p j : ℕ} {x s : E} {H β : ℝ}
    (hj : j ≤ p) (hβ : 0 ≤ β)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ p f (x + t • s))
    (hH : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ p f (x + t • s) - iteratedFDeriv ℝ p f x‖ ≤ H * ‖t • s‖ ^ β) :
    ‖iteratedFDeriv ℝ j f (x + s) - iteratedFDeriv ℝ j (taylorModel f p x) s‖ ≤
      H / (∏ i ∈ Finset.range (p - j), (((i + 1 : ℕ) : ℝ) + β)) *
        ‖s‖ ^ (((p - j : ℕ) : ℝ) + β) := by
  induction p generalizing F j with
  | zero =>
    have hj0 : j = 0 := by omega
    subst j
    rw [norm_iteratedFDeriv_zero_sub]
    have h := hH 1 (by simp)
    rw [norm_iteratedFDeriv_zero_sub] at h
    simpa using h
  | succ p ih =>
    cases j with
    | zero =>
      rw [norm_iteratedFDeriv_zero_sub]
      simpa using norm_sub_taylorModel_le_holder hβ hf hH
    | succ j =>
      rw [norm_iteratedFDeriv_sub_eq_fderiv_sub]
      have hmodel : fderiv ℝ (taylorModel f (p + 1) x) =
          taylorModel (fderiv ℝ f) p x := by
        funext z
        exact fderiv_taylorModel_eq_taylorModel_fderiv (by simpa using hf 0 (by simp)) z
      rw [hmodel]
      simp only [Nat.add_sub_add_right]
      apply ih (f := fderiv ℝ f) (Nat.le_of_succ_le_succ hj)
      · intro t ht
        exact (hf t ht).fderiv_right (by simp)
      · intro t ht
        rw [← norm_iteratedFDeriv_sub_eq_fderiv_sub]
        exact hH t ht

/-- Diagonal Lipschitz control along one actual segment gives the sharp factorial Taylor
value remainder; no regularity away from that segment is required. -/
theorem norm_sub_taylorModel_le_of_lipschitz_diagonal {f : E → F} {p : ℕ} {x s : E} {L : ℝ}
    (hp : 1 ≤ p) (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ p f (x + t • s))
    (hL : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(iteratedFDeriv ℝ p f (x + t • s) - iteratedFDeriv ℝ p f x) (fun _ => s)‖ ≤
        L * ‖t • s‖ * ‖s‖ ^ p) :
    ‖f (x + s) - taylorModel f p x s‖ ≤ L / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  have hh := norm_sub_taylorModel_le_holder_of_diagonal (β := 1) (H := L)
    (x := x) (s := s) (n := n) (by norm_num) hf
    (fun t ht => by simpa only [Nat.succ_eq_add_one, Real.rpow_one] using hL t ht)
  have hprod : ∀ k : ℕ, (∏ i ∈ Finset.range k, (((i + 1 : ℕ) : ℝ) + 1)) =
      ((k + 1)! : ℝ) := by
    intro k
    have hh := congrArg (fun n : ℕ => (n : ℝ)) (Nat.factorial_mul_ascFactorial 1 k)
    norm_num [Nat.ascFactorial_eq_prod_range, Nat.cast_prod, Nat.cast_add, Nat.cast_one,
      add_comm, add_left_comm, add_assoc] at hh ⊢
    exact hh
  have he : (((n + 1 : ℕ) : ℝ) + 1) = ((n + 1 + 1 : ℕ) : ℝ) := by push_cast; rfl
  rw [he, Real.rpow_natCast] at hh
  simpa only [hprod, Nat.succ_eq_add_one] using hh
