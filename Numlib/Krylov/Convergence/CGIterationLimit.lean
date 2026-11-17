/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.CG
import Numlib.Krylov.Convergence.CG

/-!
# Exact CG iteration limit with spectral deflation

An annihilating factor at each discarded eigenvalue makes a polynomial vanish there.
On the remaining interval, these factors have absolute value at most one. Multiplying
by a shifted Chebyshev polynomial gives an exact-arithmetic bound governed by the
condition number of the retained interval.
-/

open Finset Polynomial Polynomial.Chebyshev Krylov

namespace CG

private noncomputable def annihilator (t : ℝ) : ℝ[X] := 1 - C t⁻¹ * X

private theorem natDegree_annihilator_le (t : ℝ) : (annihilator t).natDegree ≤ 1 := by
  unfold annihilator
  refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
  exact (natDegree_C_mul_le t⁻¹ X).trans (by simp)

private theorem eval_annihilator (t u : ℝ) :
    (annihilator t).eval u = 1 - u / t := by
  rw [annihilator, eval_sub, eval_one, eval_mul, eval_C, eval_X, div_eq_mul_inv, mul_comm t⁻¹ u]

/-- For positive spectral values $\mu_i$ and a finite set $D$ of their largest indices by
value, there is a polynomial of degree at most $|D|$ equal to $1$ at zero, vanishing at the
discarded eigenvalues and bounded by $1$ at every retained eigenvalue. -/
theorem exists_deflationPolynomial {ι : Type*} (μ : ι → ℝ) (D : Finset ι)
    (hpos : ∀ i, 0 < μ i) (hhigh : ∀ i ∉ D, ∀ j ∈ D, μ i ≤ μ j) :
    ∃ q : ℝ[X], q.natDegree ≤ D.card ∧ q.eval 0 = 1 ∧
      (∀ i ∈ D, q.eval (μ i) = 0) ∧ (∀ i ∉ D, |q.eval (μ i)| ≤ 1) := by
  let q := ∏ i ∈ D, annihilator (μ i)
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · refine (natDegree_prod_le _ _).trans ?_
    simpa using sum_le_sum (fun i (_ : i ∈ D) => natDegree_annihilator_le (μ i))
  · simp [q, eval_prod, eval_annihilator]
  · intro i hi
    simp only [q, eval_prod, eval_annihilator]
    exact prod_eq_zero hi (by simp [(hpos i).ne'])
  · intro i hi
    simp only [q, eval_prod, eval_annihilator]
    have hnn (j : ι) (hj : j ∈ D) : 0 ≤ 1 - μ i / μ j :=
      sub_nonneg.2 ((div_le_one₀ (hpos j)).2 (hhigh i hi j hj))
    rw [abs_of_nonneg (prod_nonneg hnn)]
    exact prod_le_one₀ hnn (fun j _ => sub_le_self _ (div_nonneg (hpos i).le (hpos j).le))

private theorem exists_retainedPolynomial {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (n : ℕ) :
    ∃ p : ℝ[X], p.natDegree ≤ n ∧ p.eval 0 = 1 ∧ ∀ t ∈ Set.Icc a b,
      |p.eval t| ≤ 2 * ((Real.sqrt (b / a) - 1) / (Real.sqrt (b / a) + 1)) ^ n := by
  rcases hab.lt_or_eq with hlt | rfl
  · have h0 : (0 : ℝ) ∉ Set.Icc a b := fun h => (not_le.mpr ha) h.1
    have hp0 := shifted_eval_self n hlt h0
    have hpdeg := natDegree_le_of_degree_le (shifted_degree_le n a b 0)
    refine ⟨shifted n a b 0, hpdeg, hp0, fun t ht => ?_⟩
    refine (le_csSup ?_ (Set.mem_image_of_mem _ ht)).trans (sSup_abs_eval_shifted_le ha hlt n)
    exact ⟨_, by rintro _ ⟨x, hx, rfl⟩; exact abs_eval_shifted_le n hlt hx⟩
  · have hq : (Real.sqrt (a / a) - 1) / (Real.sqrt (a / a) + 1) = 0 := by
      rw [div_self ha.ne', Real.sqrt_one]
      norm_num
    rw [hq]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨1, by simp, by simp, by simp⟩
    refine ⟨annihilator a, (natDegree_annihilator_le a).trans hn, by simp [eval_annihilator],
      fun t ht => ?_⟩
    have he : t = a := le_antisymm ht.2 ht.1
    simp [he, eval_annihilator, div_self ha.ne', zero_pow hn.ne']

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E}

/-- Suppose $A$ is symmetric coercive, $Ax=b$, $0<a\le c$, and all its eigenvalues other
than the discarded set $D$ lie in $[a,c]$, while the discarded eigenvalues are at least $c$.
After $|D|+n$ conjugate-gradient steps from $x_0$, the relative energy error is bounded by
$$2 \left(\frac{\sqrt{c/a}-1}{\sqrt{c/a}+1}\right)^n.$$
The set of discarded eigenvalues can include repeated entries through the indexing
of the eigenvalues by their multiplicities. A zero initial error has relative error zero. -/
theorem energyNorm_error_le_effectiveCondition {N : ℕ} (hN : Module.finrank 𝕜 E = N)
    (hA : A.IsSymmetricCoercive) {b x x₀ : E} (hx : A x = b) {a c : ℝ}
    (ha : 0 < a) (hac : a ≤ c) (D : Finset (Fin N))
    (hhigh : ∀ i ∈ D, c ≤ hA.isSymmetric.eigenvalues hN i)
    (hlow : ∀ i ∉ D, hA.isSymmetric.eigenvalues hN i ∈ Set.Icc a c) (n : ℕ) :
    energyNorm A (x - (iterate A b x₀ (D.card + n)).x) / energyNorm A (x - x₀) ≤
      2 * ((Real.sqrt (c / a) - 1) / (Real.sqrt (c / a) + 1)) ^ n := by
  let μ := hA.isSymmetric.eigenvalues hN
  let Cn := 2 * ((Real.sqrt (c / a) - 1) / (Real.sqrt (c / a) + 1)) ^ n
  have hCn : 0 ≤ Cn := by
    have hκ : 1 ≤ c / a := (one_le_div ha).2 hac
    have hs : 1 ≤ Real.sqrt (c / a) := by simpa using Real.sqrt_le_sqrt hκ
    exact mul_nonneg (by norm_num) (pow_nonneg (div_nonneg (sub_nonneg.2 hs) (by positivity)) _)
  change _ ≤ Cn
  rcases eq_or_ne (energyNorm A (x - x₀)) 0 with hz | hz
  · rw [hz, div_zero]
    exact hCn
  rw [div_le_iff₀ (lt_of_le_of_ne (energyNorm_nonneg _ _) hz.symm)]
  obtain ⟨p, hp, hp0, hpbound⟩ := exists_retainedPolynomial ha hac n
  have hpos (i : Fin N) : 0 < μ i := by
    simpa only [RCLike.ofReal_re] using
      hA.re_pos_of_hasEigenvalue (hA.isSymmetric.hasEigenvalue_eigenvalues hN i)
  obtain ⟨q₀, hq₀, hq₀eq, hqhigh, hqlow⟩ := exists_deflationPolynomial μ D hpos
    (fun i hi j hj => (hlow i hi).2.trans (hhigh j hj))
  let q := q₀ * p
  have hq : q.natDegree ≤ D.card + n := natDegree_mul_le.trans (add_le_add hq₀ hp)
  have hq0 : q.eval 0 = 1 := by simp [q, hq₀eq, hp0]
  have hbound : ∀ i, |q.eval (μ i)| ≤ Cn := by
    intro i
    by_cases hi : i ∈ D
    · simpa [q, hqhigh i hi] using hCn
    · rw [show q.eval (μ i) = q₀.eval (μ i) * p.eval (μ i) from eval_mul]
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hqlow i hi) (abs_nonneg _)).trans
        (by simpa only [one_mul] using hpbound (μ i) (hlow i hi))
  let qK := q.map (algebraMap ℝ 𝕜)
  have hqKdeg : qK.degree ≤ (D.card + n : ℕ) := by
    refine degree_map_le.trans (degree_le_natDegree.trans ?_)
    exact_mod_cast hq
  have hqK0 : qK.eval 0 = 1 := by
    dsimp only [qK]
    rw [eval_zero_map, hq0, map_one]
  have hpoly : energyNorm A (x - (iterate A b x₀ (D.card + n)).x) ≤
      energyNorm A (aeval A qK (x - x₀)) :=
    IsGalerkinIterate.energyNorm_error_le_energyNorm_aeval hA
      (isGalerkinIterate b x₀ hA _) hx qK hqKdeg hqK0
  refine hpoly.trans (hA.isSymmetric.energyNorm_aeval_apply_le hA qK ?_ _)
  intro u hu
  obtain ⟨i, hi⟩ := hA.isSymmetric.exists_eigenvalues_eq hN hu
  rw [← hi, show qK.eval (μ i : 𝕜) = ((q.eval (μ i) : ℝ) : 𝕜) by
    dsimp only [qK]
    rw [← RCLike.algebraMap_eq_ofReal, eval_map, eval₂_at_apply]]
  simpa only [RCLike.norm_ofReal] using hbound i

private theorem chebyshevRatio_le_exp {s : ℝ} (hs : 1 ≤ s) :
    (s - 1) / (s + 1) ≤ Real.exp (-2 / s) := by
  rcases hs.eq_or_lt with rfl | hs'
  · norm_num
    positivity
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have hu0 : 0 < s - 1 := sub_pos.2 hs'
  have hv0 : 0 < s + 1 := by positivity
  have hq : 0 < (s - 1) / (s + 1) := div_pos hu0 hv0
  let u := 2 / (s - 1)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have h1 : 2 * u / (u + 2) = 2 / s := by
    dsimp [u]
    field_simp [hu0.ne', hs0.ne']
    ring
  have h2 : 1 + u = ((s - 1) / (s + 1))⁻¹ := by
    dsimp [u]
    rw [inv_div]
    field_simp [hu0.ne']
    ring
  have hh := Real.le_log_one_add_of_nonneg hu
  rw [h1, h2, Real.log_inv] at hh
  rw [← Real.exp_log hq, Real.exp_le_exp]
  simpa only [neg_neg, neg_div] using neg_le_neg hh

/-- If $\delta>0$, then after $|D|+\lceil\frac12\log(2/\delta)\sqrt{c/a}\rceil$ CG steps
under the assumptions of `CG.energyNorm_error_le_effectiveCondition`, the relative energy error
is at most $\delta$. A negative expression under the ceiling is rounded up to zero. -/
theorem energyNorm_error_le_of_iteration_limit {N : ℕ} (hN : Module.finrank 𝕜 E = N)
    (hA : A.IsSymmetricCoercive) {b x x₀ : E} (hx : A x = b) {a c : ℝ}
    (ha : 0 < a) (hac : a ≤ c) (D : Finset (Fin N))
    (hhigh : ∀ i ∈ D, c ≤ hA.isSymmetric.eigenvalues hN i)
    (hlow : ∀ i ∉ D, hA.isSymmetric.eigenvalues hN i ∈ Set.Icc a c)
    {δ : ℝ} (hδ : 0 < δ) :
    energyNorm A (x - (iterate A b x₀ (D.card +
      ⌈(1 / 2 : ℝ) * Real.log (2 / δ) * Real.sqrt (c / a)⌉₊)).x) /
      energyNorm A (x - x₀) ≤ δ := by
  let s := Real.sqrt (c / a)
  let z := (1 / 2 : ℝ) * Real.log (2 / δ) * s
  let n := ⌈z⌉₊
  have hs : 1 ≤ s := by simpa [s] using Real.sqrt_le_sqrt ((one_le_div ha).2 hac)
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have hq0 : 0 ≤ (s - 1) / (s + 1) := div_nonneg (sub_nonneg.2 hs) (by positivity)
  have hz : z ≤ (n : ℝ) := Nat.le_ceil _
  have hn : (n : ℝ) * (-2 / s) ≤ -Real.log (2 / δ) := by
    have ht := mul_le_mul_of_nonpos_right hz
      (div_nonpos_of_nonpos_of_nonneg (show (-2 : ℝ) ≤ 0 by norm_num) hs0.le)
    have hcancel : z * (-2 / s) = -Real.log (2 / δ) := by
      dsimp [z]
      field_simp [hs0.ne']
    rwa [hcancel] at ht
  have hrate : 2 * ((s - 1) / (s + 1)) ^ n ≤ δ := calc
    _ ≤ 2 * (Real.exp (-2 / s)) ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 (chebyshevRatio_le_exp hs) _) (by norm_num)
    _ = 2 * Real.exp ((n : ℝ) * (-2 / s)) := by rw [Real.exp_nat_mul]
    _ ≤ 2 * Real.exp (-Real.log (2 / δ)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hn) (by norm_num)
    _ = δ := by rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]; ring
  exact (energyNorm_error_le_effectiveCondition hN hA hx ha hac D hhigh hlow n).trans hrate

end CG
