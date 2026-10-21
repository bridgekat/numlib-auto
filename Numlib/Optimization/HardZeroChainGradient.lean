import Numlib.Optimization.HardZeroChain

/-!
# Directional derivatives of the explicit Gaussian chain

The signs of both contributions of an adjacent-coordinate interaction are explicit.
-/

noncomputable section
open scoped ContDiff
open Analysis.FlatGaussian Real

namespace Optimization.HardZeroChain

/-- Derivative contribution from changing the preceding coordinate. -/
def outgoing (a b : ℝ) : ℝ :=
  -(deriv psi (-a) * phi (-b) + deriv psi a * phi b)

/-- Derivative contribution from changing the succeeding coordinate. -/
def incoming (a b : ℝ) : ℝ :=
  -(psi (-a) * deriv phi (-b) + psi a * deriv phi b)

/-- The preceding-coordinate derivative contribution is nonpositive. -/
theorem outgoing_nonpos (a b : ℝ) : outgoing a b ≤ 0 := by
  unfold outgoing
  exact neg_nonpos.mpr (add_nonneg
    (mul_nonneg (deriv_psi_nonneg _) (primitive_pos _).le)
    (mul_nonneg (deriv_psi_nonneg _) (primitive_pos _).le))

/-- The succeeding-coordinate derivative contribution is nonpositive. -/
theorem incoming_nonpos (a b : ℝ) : incoming a b ≤ 0 := by
  unfold incoming
  rw [deriv_primitive, deriv_primitive]
  exact neg_nonpos.mpr (add_nonneg
    (mul_nonneg (psi_nonneg _) (exp_pos _).le)
    (mul_nonneg (psi_nonneg _) (exp_pos _).le))

/-- An active preceding coordinate gives a derivative contribution strictly below negative one. -/
theorem incoming_lt_neg_one {a b : ℝ} (ha : 1 ≤ |a|) (hb : |b| < 1) :
    incoming a b < -1 := by
  have hp := one_lt_deriv_primitive hb
  have hn := one_lt_deriv_primitive (show |-b| < 1 by simpa using hb)
  have hdp : 0 ≤ deriv phi b := by rw [deriv_primitive]; positivity
  have hdn : 0 ≤ deriv phi (-b) := by rw [deriv_primitive]; positivity
  rcases (le_abs).mp ha with ha | ha
  · have h := one_le_psi ha
    have hm := mul_le_mul_of_nonneg_right h hdp
    have hz := mul_nonneg (psi_nonneg (-a)) hdn
    unfold incoming
    nlinarith
  · have h := one_le_psi (show 1 ≤ -a by linarith)
    have hm := mul_le_mul_of_nonneg_right h hdn
    have hz := mul_nonneg (psi_nonneg a) hdp
    unfold incoming
    nlinarith

/-- The derivative of an interaction along any two differentiable scalar curves. -/
theorem hasDerivAt_interaction {a b : ℝ → ℝ} {a' b' t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s ↦ interaction (a s) (b s))
      (outgoing (a t) (b t) * a' + incoming (a t) (b t) * b') t := by
  have hpsi (x : ℝ) := (contDiff_psi.differentiable (by simp) x).hasDerivAt
  have hphi (x : ℝ) := (hasDerivAt_primitive x)
  have h := (((hpsi (-a t)).comp t ha.neg).mul ((hphi (-b t)).comp t hb.neg)).sub
    (((hpsi (a t)).comp t ha).mul ((hphi (b t)).comp t hb))
  convert h using 1
  · rfl
  · simp only [outgoing, incoming, deriv_primitive, Function.comp_apply, Pi.neg_apply, phi]
    ring

/-- The directional derivative is the sum of the incoming and outgoing contributions. -/
theorem hasDerivAt_chain_line (n : ℕ) (x v : ZeroChains.Space (n + 1)) :
    HasDerivAt (fun t : ℝ ↦ chain n (x + t • v))
      (-deriv phi (x 0) * v 0 + ∑ i : Fin n,
        (outgoing (x i.castSucc) (x i.succ) * v i.castSucc +
          incoming (x i.castSucc) (x i.succ) * v i.succ)) 0 := by
  have hc (i : Fin (n + 1)) :
      HasDerivAt (fun t : ℝ ↦ (x + t • v) i) (v i) 0 := by
    change HasDerivAt (fun t : ℝ ↦ x i + t * v i) (v i) 0
    simpa only [one_mul, id_eq] using
      ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (x i)
  have hs := ((hasDerivAt_primitive ((x + (0 : ℝ) • v) 0)).comp (0 : ℝ)
    (h := fun t : ℝ ↦ (x + t • v) 0) (hc 0)).neg
  have ht (i : Fin n) := hasDerivAt_interaction (hc i.castSucc) (hc i.succ)
  have h := hs.add (HasDerivAt.sum (u := (Finset.univ : Finset (Fin n))) fun i _ ↦ ht i)
  convert h using 1
  · funext t
    simp [chain_apply, interaction]
  · simp [deriv_primitive]

/-- The gradient in a coordinate direction is the actual interaction-derivative sum. -/
theorem gradient_chain_apply (n : ℕ) (x : ZeroChains.Space (n + 1)) (j : Fin (n + 1)) :
    gradient (chain n) x j =
      -deriv phi (x 0) * (EuclideanSpace.single j 1) 0 + ∑ i : Fin n,
        (outgoing (x i.castSucc) (x i.succ) * (EuclideanSpace.single j 1) i.castSucc +
          incoming (x i.castSucc) (x i.succ) * (EuclideanSpace.single j 1) i.succ) := by
  let v : ZeroChains.Space (n + 1) := EuclideanSpace.single j 1
  have hl : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hf := ((contDiff_chain n).differentiable (by simp) (x + (0 : ℝ) • v)).hasFDerivAt
  have hd := hf.comp_hasDerivAt (0 : ℝ) hl
  have heq := hd.unique (hasDerivAt_chain_line n x v)
  simpa [EuclideanSpace.gradient_apply, v] using heq

/-- Each summand in a coordinate derivative is nonpositive. -/
theorem coordinate_contribution_nonpos (n : ℕ) (x : ZeroChains.Space (n + 1))
    (j : Fin (n + 1)) (i : Fin n) :
    outgoing (x i.castSucc) (x i.succ) * (EuclideanSpace.single j 1) i.castSucc +
      incoming (x i.castSucc) (x i.succ) * (EuclideanSpace.single j 1) i.succ ≤ 0 := by
  apply add_nonpos
  · apply mul_nonpos_of_nonpos_of_nonneg (outgoing_nonpos _ _)
    simp only [PiLp.single_apply]
    split_ifs <;> norm_num
  · apply mul_nonpos_of_nonpos_of_nonneg (incoming_nonpos _ _)
    simp only [PiLp.single_apply]
    split_ifs <;> norm_num

/-- Other interactions cannot cancel the derivative from the corrected seed. -/
theorem gradient_chain_zero_le (n : ℕ) (x : ZeroChains.Space (n + 1)) :
    gradient (chain n) x 0 ≤ -deriv phi (x 0) := by
  rw [gradient_chain_apply]
  have hs := Finset.sum_nonpos (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) ↦
    coordinate_contribution_nonpos n x 0 i)
  simpa using hs

/-- Other interactions cannot cancel the incoming derivative at a succeeding coordinate. -/
theorem gradient_chain_succ_le (n : ℕ) (x : ZeroChains.Space (n + 1)) (i : Fin n) :
    gradient (chain n) x i.succ ≤ incoming (x i.castSucc) (x i.succ) := by
  rw [gradient_chain_apply]
  let f : Fin n → ℝ := fun j ↦
    outgoing (x j.castSucc) (x j.succ) * (EuclideanSpace.single i.succ 1) j.castSucc +
      incoming (x j.castSucc) (x j.succ) * (EuclideanSpace.single i.succ 1) j.succ
  have hsum : ∑ j : Fin n, f j ≤ f i := by
    have he := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) f (Finset.mem_univ i)
    have hn := Finset.sum_nonpos (s := Finset.univ.erase i)
      (fun j _ ↦ coordinate_contribution_nonpos n x i.succ j)
    linarith
  have hne : i.castSucc ≠ i.succ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hi : f i = incoming (x i.castSucc) (x i.succ) := by simp [f, hne]
  have hs : -deriv phi (x 0) * (EuclideanSpace.single i.succ 1) 0 = 0 := by simp
  rw [hs, zero_add]
  exact hsum.trans_eq hi

/-- If all earlier coordinates have magnitude at least one, a small coordinate has
an actual gradient component strictly below negative one. -/
theorem gradient_chain_lt_neg_one (n : ℕ) (x : ZeroChains.Space (n + 1))
    (j : Fin (n + 1)) (hj : |x j| < 1)
    (hprev : ∀ i : Fin (n + 1), i.val < j.val → 1 ≤ |x i|) :
    gradient (chain n) x j < -1 := by
  refine Fin.cases ?_ (fun i ↦ ?_) j hj hprev
  · intro hj _
    have h := gradient_chain_zero_le n x
    have hp := one_lt_deriv_primitive hj
    linarith
  · intro hj hprev
    have ha := hprev i.castSucc (by simp)
    exact (gradient_chain_succ_le n x i).trans_lt (incoming_lt_neg_one ha hj)

/-- Any coordinate of magnitude less than one has an earlier or equal small coordinate
whose actual gradient component is strictly below negative one. -/
theorem exists_gradient_chain_lt_neg_one_before (n : ℕ) (x : ZeroChains.Space (n + 1))
    (i : Fin (n + 1)) (hi : |x i| < 1) :
    ∃ j : Fin (n + 1), j ≤ i ∧ |x j| < 1 ∧ gradient (chain n) x j < -1 := by
  classical
  let s := Finset.univ.filter (fun j : Fin (n + 1) ↦ |x j| < 1)
  have his : i ∈ s := by simp [s, hi]
  have hs : s.Nonempty := ⟨i, his⟩
  let j := s.min' hs
  have hj : |x j| < 1 := (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
  have hprev : ∀ k : Fin (n + 1), k.val < j.val → 1 ≤ |x k| := by
    intro k hk
    by_contra h
    have hks : k ∈ s := by simp [s, lt_of_not_ge h]
    have hle : j ≤ k := Finset.min'_le s k hks
    exact (not_le_of_gt hk) hle
  exact ⟨j, Finset.min'_le s i his, hj, gradient_chain_lt_neg_one n x j hj hprev⟩

/-- A chain with any coordinate of magnitude less than one has gradient norm greater than one. -/
theorem one_lt_norm_gradient_chain (n : ℕ) (x : ZeroChains.Space (n + 1))
    (hx : ∃ i : Fin (n + 1), |x i| < 1) : 1 < ‖gradient (chain n) x‖ := by
  obtain ⟨i, hi⟩ := hx
  obtain ⟨j, _, _, hgrad⟩ := exists_gradient_chain_lt_neg_one_before n x i hi
  have hn := PiLp.norm_apply_le (gradient (chain n) x) j
  rw [Real.norm_eq_abs, abs_of_neg (by linarith : gradient (chain n) x j < 0)] at hn
  linarith

end Optimization.HardZeroChain
