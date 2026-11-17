/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Radon
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Active nodes for finite polynomial minimax approximation

On $n+1$ distinct real nodes, interpolation determines the exact minimax value
for polynomials of degree at most $n$ that take the value $1$ at $0$. Helly's
theorem shows that the largest of these values over all subsets of $n+1$ nodes
is also the minimax value on the entire finite set.
-/

open Finset Polynomial

namespace Polynomial

private noncomputable def basisNormSum (T : Finset ℝ) : ℝ :=
  ∑ x ∈ T, ‖(Lagrange.basis T id x).eval (0 : ℝ)‖

private theorem basisNormSum_pos {T : Finset ℝ} (hT : T.Nonempty) : 0 < basisNormSum T := by
  have hs := congrArg (Polynomial.eval (0 : ℝ)) (Lagrange.sum_basis (Set.injOn_id _) hT)
  simp only [eval_finsetSum, eval_one] at hs
  have hn := norm_sum_le T (fun x => (Lagrange.basis T id x).eval (0 : ℝ))
  rw [hs, norm_one] at hn
  exact zero_lt_one.trans_le hn

private theorem basisNormSum_eq_product (T : Finset ℝ) :
    basisNormSum T = ∑ x ∈ T, ∏ y ∈ T.erase x, |y| / |y - x| := by
  unfold basisNormSum
  apply Finset.sum_congr rfl
  intro x _
  simp only [Lagrange.basis, Lagrange.basisDivisor, eval_prod, id_eq, eval_mul, eval_C, eval_sub,
    eval_X, zero_sub, norm_prod, norm_mul, norm_inv, norm_neg, Real.norm_eq_abs]
  apply Finset.prod_congr rfl
  intro y _
  rw [div_eq_mul_inv, abs_sub_comm y x, mul_comm]

private theorem exists_real_interpolant_le_basisNormSum_inv {T : Finset ℝ}
    (hT : T.Nonempty) :
    ∃ p : ℝ[X], p.degree ≤ (T.card - 1 : ℕ) ∧ p.eval 0 = 1 ∧
      ∀ x ∈ T, ‖p.eval x‖ ≤ (basisNormSum T)⁻¹ := by
  let c (x : ℝ) := (Lagrange.basis T id x).eval (0 : ℝ)
  let M := basisNormSum T
  let r (x : ℝ) := (if 0 ≤ c x then 1 else -1) * M⁻¹
  let p := Lagrange.interpolate T id r
  refine ⟨p, Lagrange.degree_interpolate_le _ (Set.injOn_id _), ?_, ?_⟩
  · have h (x : ℝ) : r x * c x = ‖c x‖ * M⁻¹ := by
      by_cases hx : 0 ≤ c x
      · rw [show r x = 1 * M⁻¹ from congrArg (fun z => z * M⁻¹) (ite_eq_left hx),
          Real.norm_eq_abs, abs_of_nonneg hx, one_mul, mul_comm]
      · rw [show r x = -1 * M⁻¹ from congrArg (fun z => z * M⁻¹) (ite_eq_right hx),
          Real.norm_eq_abs, abs_of_neg (lt_of_not_ge hx)]
        ring
    dsimp only [p]
    rw [Lagrange.interpolate_apply, eval_finsetSum]
    simp only [eval_mul, eval_C]
    change (∑ x ∈ T, r x * c x) = 1
    simp_rw [h]
    rw [← Finset.sum_mul]
    exact mul_inv_cancel₀ (basisNormSum_pos hT).ne'
  · intro x hx
    rw [show p.eval x = r x from Lagrange.eval_interpolate_at_node r (Set.injOn_id _) hx]
    have hM : 0 ≤ M⁻¹ := inv_nonneg.2 (basisNormSum_pos hT).le
    by_cases h : 0 ≤ c x
    · simp only [r, ite_eq_left h, one_mul, Real.norm_eq_abs, abs_of_nonneg hM]
      exact le_rfl
    · simp only [r, ite_eq_right h, neg_one_mul, norm_neg, Real.norm_eq_abs, abs_of_nonneg hM]
      exact le_rfl

private theorem map_lagrange_basis {𝕜 : Type*} [RCLike 𝕜] (T : Finset ℝ) (x : ℝ) :
    (Lagrange.basis T id x).map (algebraMap ℝ 𝕜) =
      Lagrange.basis T (fun y : ℝ => algebraMap ℝ 𝕜 y) x := by
  simp only [Lagrange.basis, Lagrange.basisDivisor, Polynomial.map_prod, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_sub, Polynomial.map_X, id_eq, map_inv₀, map_sub]

private theorem basisNormSum_inv_le_iSup {𝕜 : Type*} [RCLike 𝕜] {S T : Finset ℝ}
    {n : ℕ} (hTS : T ⊆ S) (hT : T.card = n + 1)
    (p : 𝕜[X]) (hp : p.degree ≤ n) (h0 : p.eval 0 = 1) :
    (basisNormSum T)⁻¹ ≤ ⨆ x : S, ‖p.eval (algebraMap ℝ 𝕜 x.val)‖ := by
  let k := algebraMap ℝ 𝕜
  have hk : Set.InjOn k T := k.injective.injOn
  have hd : p.degree < (T.card : WithBot ℕ) := by
    rw [hT]
    exact hp.trans_lt (WithBot.coe_lt_coe.2 (Nat.lt_succ_self _))
  have hs := congrArg (Polynomial.eval (0 : 𝕜)) (Lagrange.eq_interpolate hk hd)
  simp only [h0, Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C] at hs
  let M := ⨆ x : S, ‖p.eval (k x.val)‖
  have hTne : T.Nonempty := Finset.card_pos.1 (by omega)
  have hnorm (x : ℝ) :
      ‖(Lagrange.basis T k x).eval (0 : 𝕜)‖ = ‖(Lagrange.basis T id x).eval (0 : ℝ)‖ := by
    rw [← map_lagrange_basis, ← map_zero k, Polynomial.eval_map_apply,
      RCLike.algebraMap_eq_ofReal, RCLike.norm_ofReal, Real.norm_eq_abs]
  have hb : 1 ≤ M * basisNormSum T := by
    rw [basisNormSum, Finset.mul_sum]
    calc
      1 = ‖∑ x ∈ T, p.eval (k x) * (Lagrange.basis T k x).eval 0‖ := by rw [← hs, norm_one]
      _ ≤ ∑ x ∈ T, ‖p.eval (k x) * (Lagrange.basis T k x).eval 0‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ T, M * ‖(Lagrange.basis T id x).eval (0 : ℝ)‖ := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [norm_mul, hnorm]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact le_ciSup (f := fun y : S => ‖p.eval (k y.val)‖) (Finite.bddAbove_range _) ⟨x, hTS hx⟩
  simpa only [one_div] using (div_le_iff₀ (basisNormSum_pos hTne)).2 hb

private theorem exists_real_poly_le_of_helly {S : Finset ℝ} {n : ℕ}
    (hn : 0 < n) (hS : n + 1 ≤ S.card) {M : ℝ}
    (hM : ∀ T ⊆ S, T.card = n + 1 → (basisNormSum T)⁻¹ ≤ M) :
    ∃ p : ℝ[X], p.degree ≤ n ∧ p.eval 0 = 1 ∧ ∀ x ∈ S, ‖p.eval x‖ ≤ M := by
  let V := Polynomial.degreeLT ℝ n
  have : FiniteDimensional ℝ V := Module.Finite.of_injective
    (Polynomial.degreeLTEquiv ℝ n).toLinearMap (Polynomial.degreeLTEquiv ℝ n).injective
  have hdim : Module.finrank ℝ V = n := by
    rw [LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv ℝ n), Module.finrank_fin_fun]
  let f (x : ℝ) : V →ᵃ[ℝ] ℝ :=
    AffineMap.const ℝ V 1 + (x • (Polynomial.leval x).comp V.subtype).toAffineMap
  have hf (x : ℝ) (q : V) : f x q = 1 + x * q.val.eval x := rfl
  let K (x : ℝ) : Set V := f x ⁻¹' Set.Icc (-M) M
  have hconv (x : ℝ) (_ : x ∈ S) : Convex ℝ (K x) :=
    (convex_Icc (-M) M).affine_preimage (f x)
  have hc : Module.finrank ℝ V + 1 ≤ S.card := by rw [hdim]; exact hS
  have hlocal (T : Finset ℝ) (hTS : T ⊆ S) (hT : T.card = Module.finrank ℝ V + 1) :
      (⋂ x ∈ T, K x).Nonempty := by
    rw [hdim] at hT
    have hTne : T.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨p, hp, h0, hb⟩ := exists_real_interpolant_le_basisNormSum_inv hTne
    have hp' : p.degree ≤ n := by simpa [hT] using hp
    have hq : p.divX ∈ V := by
      apply Polynomial.mem_degreeLT.2
      by_cases hz : p.divX = 0
      · simp [hz]
      rw [← Polynomial.natDegree_lt_iff_degree_lt hz,
        Polynomial.natDegree_divX_eq_natDegree_tsub_one]
      have hnd := Polynomial.natDegree_le_iff_degree_le.2 hp'
      omega
    let q : V := ⟨p.divX, hq⟩
    have he (x : ℝ) : p.eval x = f x q := by
      have h := congrArg (Polynomial.eval x) (Polynomial.X_mul_divX_add p)
      rw [Polynomial.coeff_zero_eq_eval_zero, h0] at h
      simpa [hf, q, add_comm] using h.symm
    refine ⟨q, Set.mem_iInter₂.2 fun x hx => ?_⟩
    have hv := (hb x hx).trans (hM T hTS hT)
    rw [Real.norm_eq_abs, he, abs_le] at hv
    exact hv
  obtain ⟨q, hq⟩ := Convex.helly_theorem (𝕜 := ℝ) hc hconv hlocal
  let p : ℝ[X] := 1 + X * q.val
  have hp : p.degree ≤ n := by
    by_cases hz : q.val = 0
    · simp [p, hz]
    have hnd := (Polynomial.natDegree_lt_iff_degree_lt hz).2 (Polynomial.mem_degreeLT.1 q.2)
    have hb : (X * q.val).degree ≤ (n : WithBot ℕ) := by
      rw [← Polynomial.natDegree_le_iff_degree_le, Polynomial.natDegree_X_mul hz]
      omega
    exact Polynomial.degree_add_le_of_degree_le (by simp) hb
  refine ⟨p, hp, by simp [p], fun x hx => ?_⟩
  have h := Set.mem_iInter₂.1 hq x hx
  change f x q ∈ Set.Icc (-M) M at h
  rw [Real.norm_eq_abs, abs_le]
  simpa [hf, p] using h

/-- The normalized degree-$n$ minimax value on a finite set of real nodes
with at least $n+1$ distinct members is determined by a subset of $n+1$
nodes. Its formula uses the sum of the absolute Lagrange basis values at
zero. The value is common to real and complex polynomials. -/
theorem exists_active_nodes_eval_minimax_eq {𝕜 : Type*} [RCLike 𝕜]
    {n : ℕ} (hn : 0 < n) (S : Finset ℝ) (hS : n + 1 ≤ S.card) :
    ∃ T ⊆ S, T.card = n + 1 ∧
      (⨅ p : {p : 𝕜[X] // p.degree ≤ n ∧ p.eval 0 = 1},
        ⨆ x : S, ‖p.1.eval (algebraMap ℝ 𝕜 x.val)‖) =
        (∑ x ∈ T, ∏ y ∈ T.erase x, |y| / |y - x|)⁻¹ := by
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image (S.powersetCard (n + 1))
    (fun T => (basisNormSum T)⁻¹) (Finset.powersetCard_nonempty.2 hS)
  obtain ⟨hTS, hTc⟩ := Finset.mem_powersetCard.1 hT
  refine ⟨T, hTS, hTc, ?_⟩
  rw [← basisNormSum_eq_product]
  let M := (basisNormSum T)⁻¹
  have hM : 0 ≤ M := inv_nonneg.2 (basisNormSum_pos (Finset.card_pos.1 (by omega))).le
  obtain ⟨q, hq, hq0, hqS⟩ := exists_real_poly_le_of_helly hn hS
    (fun U hUS hUc => hmax U (Finset.mem_powersetCard.2 ⟨hUS, hUc⟩))
  let k := algebraMap ℝ 𝕜
  let P := {p : 𝕜[X] // p.degree ≤ n ∧ p.eval 0 = 1}
  let p : P := ⟨q.map k, (Polynomial.degree_map_le).trans hq, by
    rw [← map_zero k, Polynomial.eval_map_apply, hq0, map_one]⟩
  have : Nonempty P := ⟨p⟩
  have hlower (r : P) : M ≤ ⨆ x : S, ‖r.1.eval (k x.val)‖ :=
    basisNormSum_inv_le_iSup hTS hTc r.1 r.2.1 r.2.2
  apply le_antisymm _ (le_ciInf hlower)
  refine (ciInf_le ⟨M, ?_⟩ p).trans ?_
  · rintro _ ⟨r, rfl⟩
    exact hlower r
  · refine Real.iSup_le (fun x : S => ?_) hM
    change ‖(q.map k).eval (k x.val)‖ ≤ M
    rw [Polynomial.eval_map_apply, RCLike.algebraMap_eq_ofReal, RCLike.norm_ofReal,
      ← Real.norm_eq_abs]
    exact hqS x.val x.property

end Polynomial
