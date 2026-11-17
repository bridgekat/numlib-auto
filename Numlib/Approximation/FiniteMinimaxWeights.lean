/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Weights for finite minimax approximation

For the supremum-norm distance from a vector to a subspace of a finite
coordinate space, a norming functional on the quotient gives coordinate
weights for which the weighted squared error is at least that distance
squared. The weights are the normalized absolute values of the coefficients
of the functional.
-/

open Finset
open scoped ComplexConjugate

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι]

private theorem exists_minimax_dual_coefficients (V : Submodule 𝕜 (ι → 𝕜)) (a : ι → 𝕜) :
    ∃ c : ι → 𝕜, (∑ i, ‖c i‖) ≤ 1 ∧
      ∀ v : V, (∑ i, c i * (a i - v.val i)) = (Metric.infDist a (V : Set (ι → 𝕜)) : 𝕜) := by
  classical
  let δ := Metric.infDist a (V : Set (ι → 𝕜))
  let Q := V.mkQL
  have hQ : ‖Q a‖ = δ := QuotientAddGroup.norm_mk a
  obtain ⟨g, hg, hga⟩ := exists_dual_vector'' 𝕜 (Q a)
  let F := g.comp Q
  have hF (x : ι → 𝕜) : ‖F x‖ ≤ ‖x‖ := by
    change ‖g (Q x)‖ ≤ ‖x‖
    calc
      ‖g (Q x)‖ ≤ ‖g‖ * ‖Q x‖ := g.le_opNorm _
      _ ≤ 1 * ‖Q x‖ := mul_le_mul_of_nonneg_right hg (norm_nonneg _)
      _ = ‖Q x‖ := one_mul _
      _ ≤ ‖x‖ := Submodule.Quotient.norm_mk_le V x
  have hFa : F a = (δ : 𝕜) := by simpa [F, hQ] using hga
  have hFV (v : V) : F v.val = 0 := by
    have hq : Q v.val = 0 := (Submodule.Quotient.mk_eq_zero V).2 v.property
    change g (Q v.val) = 0
    simp [hq]
  let B := Pi.basisFun 𝕜 ι
  let c (i : ι) := F (B i)
  have hc (x : ι → 𝕜) : (∑ i, c i * x i) = F x := by
    calc
      (∑ i, c i * x i) = F (∑ i, (B.repr x i) • B i) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul, smul_eq_mul]
        exact mul_comm _ _
      _ = F x := congrArg F (B.sum_repr x)
  let z (i : ι) := if c i = 0 then 0 else conj (c i) / (‖c i‖ : 𝕜)
  have hz (i : ι) : c i * z i = (‖c i‖ : 𝕜) := by
    by_cases hi : c i = 0
    · simp [z, hi]
    · have hni : (‖c i‖ : 𝕜) ≠ 0 := by
        exact_mod_cast (norm_ne_zero_iff.mpr hi)
      rw [show z i = conj (c i) / (‖c i‖ : 𝕜) from ite_eq_right hi,
        mul_div_assoc', RCLike.mul_conj, pow_two, mul_div_cancel_right₀ _ hni]
  have hzn : ‖z‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
    by_cases hi : c i = 0
    · simp [z, hi]
    · simp [z, hi, (norm_pos_iff.2 hi).ne']
  refine ⟨c, ?_, fun v => ?_⟩
  · let M := ∑ i, ‖c i‖
    have he : F z = (M : 𝕜) := by
      rw [← hc, show (M : 𝕜) = ∑ i, (‖c i‖ : 𝕜) from map_sum (algebraMap ℝ 𝕜) _ _]
      exact Finset.sum_congr rfl fun i _ => hz i
    have hf := (hF z).trans hzn
    have hMn : 0 ≤ M := Finset.sum_nonneg fun i _ => norm_nonneg _
    rwa [he, RCLike.norm_ofReal, abs_of_nonneg hMn] at hf
  · change (∑ i, c i * (a - v.val) i) = (δ : 𝕜)
    rw [hc, map_sub, hFa, hFV, sub_zero]

/-- There are probability weights such that every vector $v$ of a subspace
$V$ has weighted squared distance from $a$ at least the square of the
supremum-norm distance from $a$ to $V$. -/
theorem Submodule.exists_probability_weights_infDist_sq_le [Nonempty ι]
    (V : Submodule 𝕜 (ι → 𝕜)) (a : ι → 𝕜) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      ∀ v : V, (Metric.infDist a (V : Set (ι → 𝕜))) ^ 2 ≤
        ∑ i, w i * ‖a i - v.val i‖ ^ 2 := by
  classical
  let δ := Metric.infDist a (V : Set (ι → 𝕜))
  have hδ : 0 ≤ δ := Metric.infDist_nonneg
  by_cases hd0 : δ = 0
  · let j := Classical.choice (inferInstance : Nonempty ι)
    have hw (i : ι) : 0 ≤ (Pi.single j (1 : ℝ) : ι → ℝ) i := by
      by_cases hi : i = j <;> simp [hi]
    refine ⟨Pi.single j 1, hw, by simp, fun v => ?_⟩
    change δ ^ 2 ≤ _
    rw [hd0, zero_pow (by decide)]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
  obtain ⟨c, hMle, hc⟩ := exists_minimax_dual_coefficients V a
  let M := ∑ i, ‖c i‖
  have hM : 0 < M := by
    by_contra! h
    have hc0 (i : ι) : c i = 0 := norm_eq_zero.mp (le_antisymm
      ((Finset.single_le_sum (fun j _ => norm_nonneg (c j)) (Finset.mem_univ i)).trans h)
      (norm_nonneg _))
    have hcast : (δ : 𝕜) = 0 := by simpa [hc0, δ] using (hc 0).symm
    exact hd0 (by exact_mod_cast hcast)
  let w (i : ι) := ‖c i‖ / M
  have hw (i : ι) : 0 ≤ w i := div_nonneg (norm_nonneg _) hM.le
  have hws : ∑ i, w i = 1 := by
    simp_rw [w, div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ hM.ne'
  refine ⟨w, hw, hws, fun v => ?_⟩
  let x := a - v.val
  have hδle : δ ≤ ∑ i, w i * ‖x i‖ := by
    have h : (∑ i, c i * x i) = (δ : 𝕜) := hc v
    calc
      δ ≤ ∑ i, ‖c i‖ * ‖x i‖ := by
        have he := norm_sum_le Finset.univ (fun i => c i * x i)
        rwa [h, RCLike.norm_ofReal, abs_of_nonneg hδ, ← Finset.sum_congr rfl
          (fun i _ => (norm_mul (c i) (x i)).symm)] at he
      _ = M * ∑ i, w i * ‖x i‖ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← mul_assoc]
        congr 1
        change ‖c i‖ = M * (‖c i‖ / M)
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hM.ne']
      _ ≤ 1 * ∑ i, w i * ‖x i‖ :=
        mul_le_mul_of_nonneg_right hMle (Finset.sum_nonneg fun i _ =>
          mul_nonneg (hw i) (norm_nonneg _))
      _ = ∑ i, w i * ‖x i‖ := one_mul _
  have hsq := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * ‖x i‖)
  have hsqrt (i : ι) : Real.sqrt (w i) ^ 2 = w i := Real.sq_sqrt (hw i)
  simp_rw [← mul_assoc, ← pow_two, mul_pow, hsqrt] at hsq
  rw [hws, one_mul] at hsq
  exact (pow_le_pow_left₀ hδ hδle 2).trans hsq

open Polynomial

/-- For finitely many spectral points, the square of the polynomial minimax
value (over $p(0)=1$ and $\deg p\le n$) is a lower bound for the weighted
sum of squared values for some probability weights. The weights are independent
of the polynomial and admit repeated spectral points. -/
theorem Polynomial.exists_probability_weights_eval_minimax_sq_le [Nonempty ι]
    (μ : ι → 𝕜) (n : ℕ) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      ∀ (p : 𝕜[X]), p.degree ≤ n → p.eval 0 = 1 →
        (⨅ q : {q : 𝕜[X] // q.degree ≤ n ∧ q.eval 0 = 1}, ⨆ i, ‖q.1.eval (μ i)‖) ^ 2 ≤
          ∑ i, w i * ‖p.eval (μ i)‖ ^ 2 := by
  classical
  let E : 𝕜[X] →ₗ[𝕜] (ι → 𝕜) := LinearMap.pi fun i => Polynomial.leval (μ i)
  let U := Polynomial.degreeLE 𝕜 (n : WithBot ℕ) ⊓ LinearMap.ker (Polynomial.leval (0 : 𝕜))
  let V := U.map E
  let P := {p : 𝕜[X] // p.degree ≤ n ∧ p.eval 0 = 1}
  let δ := ⨅ p : P, ⨆ i, ‖p.1.eval (μ i)‖
  have hnorm (p : 𝕜[X]) : ‖E p‖ = ⨆ i, ‖p.eval (μ i)‖ := by
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonempty (E p)).2 fun i =>
        le_ciSup (f := fun j => ‖p.eval (μ j)‖) (Finite.bddAbove_range _) i
    · exact Real.iSup_le (fun i => norm_le_pi_norm (E p) i) (norm_nonneg _)
  have h1 : E 1 = 1 := by
    funext i
    exact Polynomial.eval_one
  have hdeg1 : (1 : 𝕜[X]) ∈ Polynomial.degreeLE 𝕜 (n : WithBot ℕ) :=
    Polynomial.mem_degreeLE.2 (by simp)
  have hS (p : P) : 1 - p.1 ∈ U := by
    refine ⟨Submodule.sub_mem _ hdeg1 (Polynomial.mem_degreeLE.2 p.2.1), ?_⟩
    change (1 - p.1).eval 0 = 0
    simp [p.2.2]
  have hv (p : P) : (1 : ι → 𝕜) - E p.1 ∈ V := by
    rw [← h1, ← map_sub]
    exact Submodule.mem_map_of_mem (hS p)
  have hδle : δ ≤ Metric.infDist (1 : ι → 𝕜) (V : Set (ι → 𝕜)) := by
    rw [Metric.infDist_eq_iInf]
    refine le_ciInf fun v => ?_
    obtain ⟨q, hq, hqv⟩ := Submodule.mem_map.1 v.property
    let p : P := ⟨1 - q, Polynomial.mem_degreeLE.1 (Submodule.sub_mem _ hdeg1 hq.1), by
      have hq0 : q.eval 0 = 0 := hq.2
      simp [hq0]⟩
    have hs : E p.1 = (1 : ι → 𝕜) - v.val := by
      change E (1 - q) = _
      rw [map_sub, h1, hqv]
    change (⨅ r : P, ⨆ i, ‖r.1.eval (μ i)‖) ≤ dist (1 : ι → 𝕜) v.val
    rw [dist_eq_norm, ← hs, hnorm]
    refine ciInf_le ⟨0, ?_⟩ p
    rintro _ ⟨r, rfl⟩
    change 0 ≤ ⨆ i, ‖r.1.eval (μ i)‖
    rw [← hnorm]
    exact norm_nonneg _
  have hδ : 0 ≤ δ := by
    have : Nonempty P := ⟨⟨1, by simp, by simp⟩⟩
    exact le_ciInf fun p => (hnorm p.1) ▸ norm_nonneg (E p.1)
  obtain ⟨w, hw, hsum, hb⟩ :=
    Submodule.exists_probability_weights_infDist_sq_le V (1 : ι → 𝕜)
  refine ⟨w, hw, hsum, fun p hp h0 => ?_⟩
  let q : P := ⟨p, hp, h0⟩
  let v : V := ⟨1 - E p, hv q⟩
  have hEq (i : ι) : (1 : ι → 𝕜) i - v.val i = p.eval (μ i) := by
    change (1 : 𝕜) - (1 - p.eval (μ i)) = _
    ring
  have hs := hb v
  simp_rw [hEq] at hs
  exact (pow_le_pow_left₀ hδ hδle 2).trans hs
