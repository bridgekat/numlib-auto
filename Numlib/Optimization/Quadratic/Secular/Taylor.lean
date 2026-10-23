import Numlib.Optimization.Quadratic.Secular
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Secular derivatives and Taylor bounds

Every derivative is computed from the actual shifted-inverse spectral identity.
Alternating derivative signs and the Lagrange remainder yield all upper and lower
Taylor estimates, including strictness and negative displacements. The zero
objective gradient is handled explicitly. The final bounds concern the actual
operator-inverse secular function and its actual iterated derivatives.
-/

open scoped BigOperators Topology
open Filter
namespace QuadraticSecular.PencilBasis
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {H M : E →L[ℝ] E} (B : PencilBasis (ι := ι) H M)

/-- Every finite spectral secular sum is continuously differentiable to every finite order
above the edge. -/
theorem contDiffOn_spectralSum (g : E) (n : ℕ) : ContDiffOn ℝ n (B.spectralSum g)
    (Set.Ioi B.edge) := by
  apply ContDiffOn.sum
  intro i _
  exact contDiffOn_const.div ((contDiffOn_id.add contDiffOn_const).pow 2)
    (fun z hz => ne_of_gt (sq_pos_of_pos (B.denominator_pos hz i)))

/-- Compute every iterated derivative of the translated negative second integer power. -/
theorem shifted_power_deriv (n : ℕ) (a z : ℝ) :
    iteratedDeriv n (fun x : ℝ => (x + a) ^ (-2 : ℤ)) z =
      (∏ i ∈ Finset.range n, (-2 - (i : ℝ))) * (z + a) ^ (-2 - (n : ℤ)) := by
  calc
    _ = iteratedDeriv n (fun y : ℝ => y ^ (-2 : ℤ)) (z + a) :=
      congrFun (iteratedDeriv_comp_add_const n (fun y : ℝ => y ^ (-2 : ℤ)) a) z
    _ = _ := by
      rw [iteratedDeriv_eq_iterate, iter_deriv_zpow]
      norm_num

/-- Derive every spectral-sum derivative as a negative falling-factor product times the
positive-power sum. -/
theorem spectralSum_deriv (g : E) (n : ℕ) {z : ℝ} (hz : B.edge < z) :
    iteratedDeriv n (B.spectralSum g) z =
      (∏ i ∈ Finset.range n, (-2 - (i : ℝ))) *
        ∑ i, (inner ℝ g (B.basis i)) ^ 2 *
          (z + B.eigenvalue i) ^ (-2 - (n : ℤ)) := by
  have hf (i : ι) : ContDiffAt ℝ n
      (fun x => (inner ℝ g (B.basis i)) ^ 2 / (x + B.eigenvalue i) ^ 2) z :=
    contDiffAt_const.div ((contDiffAt_id.add contDiffAt_const).pow 2)
      (ne_of_gt (sq_pos_of_pos (B.denominator_pos hz i)))
  change iteratedDeriv n (fun x => ∑ i,
    (inner ℝ g (B.basis i)) ^ 2 / (x + B.eigenvalue i) ^ 2) z = _
  rw [iteratedDeriv_fun_sum (fun i _ => hf i), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have heq : (fun x : ℝ => (inner ℝ g (B.basis i)) ^ 2 /
      (x + B.eigenvalue i) ^ 2) =
      (fun x => (inner ℝ g (B.basis i)) ^ 2 * (x + B.eigenvalue i) ^ (-2 : ℤ)) := by
    ext x
    simp [div_eq_mul_inv, zpow_neg, zpow_ofNat]
  rw [heq, iteratedDeriv_const_mul_field, shifted_power_deriv]
  ring


/-- The product of the first n factors 2 + i is (n + 1) factorial. -/
theorem product_two_add (n : ℕ) :
    (∏ i ∈ Finset.range n, (2 + (i : ℝ))) = ((n + 1).factorial : ℝ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ (n + 1)]
    push_cast
    ring

/-- The negative falling-factor product equals (-1)^n times (n + 1) factorial. -/
theorem product_neg_two_sub (n : ℕ) :
    (∏ i ∈ Finset.range n, (-2 - (i : ℝ))) =
      (-1 : ℝ)^n * ((n + 1).factorial : ℝ) := by
  have heq (i : ℕ) : (-2 - (i : ℝ)) = -(2 + (i : ℝ)) := by ring
  simp_rw [heq]
  rw [Finset.prod_neg, Finset.card_range, product_two_add]

/-- The exact all-order derivative formula has factor (-1)^n (n + 1)! and denominators
(z + lambda_i)^(n + 2). -/
theorem spectralSum_deriv_formula (g : E) (n : ℕ) {z : ℝ} (hz : B.edge < z) :
    iteratedDeriv n (B.spectralSum g) z =
      (-1 : ℝ)^n * ((n + 1).factorial : ℝ) *
        ∑ i, (inner ℝ g (B.basis i)) ^ 2 /
          (z + B.eigenvalue i) ^ (n + 2) := by
  rw [B.spectralSum_deriv g n hz, product_neg_two_sub]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have heq : (-2 : ℤ) - (n : ℤ) = -((n + 2 : ℕ) : ℤ) := by omega
  rw [heq, zpow_neg, zpow_natCast, div_eq_mul_inv]

/-- For a nonzero gradient the finite sum in every derivative formula is strictly positive
above the edge. -/
theorem positive_derivative_sum {g : E} (hg : g ≠ 0) (n : ℕ) {z : ℝ}
    (hz : B.edge < z) :
    0 < ∑ i, (inner ℝ g (B.basis i)) ^ 2 / (z + B.eigenvalue i) ^ (n + 2) := by
  obtain ⟨i, hi⟩ := B.exists_coefficient_ne_zero hg
  apply Finset.sum_pos'
  · intro j _
    exact div_nonneg (sq_nonneg _) (pow_nonneg (B.denominator_pos hz j).le _)
  · exact ⟨i, Finset.mem_univ i,
      div_pos (sq_pos_of_ne_zero hi) (pow_pos (B.denominator_pos hz i) _)⟩

/-- Every even derivative of a nonzero secular function is positive above the edge. -/
theorem derivative_even_pos {g : E} (hg : g ≠ 0) {n : ℕ} (hn : Even n)
    {z : ℝ} (hz : B.edge < z) : 0 < iteratedDeriv n (B.spectralSum g) z := by
  rw [B.spectralSum_deriv_formula g n hz, hn.neg_one_pow, one_mul]
  exact mul_pos (by positivity) (B.positive_derivative_sum hg n hz)

/-- Every odd derivative of a nonzero secular function is negative above the edge. -/
theorem derivative_odd_neg {g : E} (hg : g ≠ 0) {n : ℕ} (hn : Odd n)
    {z : ℝ} (hz : B.edge < z) : iteratedDeriv n (B.spectralSum g) z < 0 := by
  rw [B.spectralSum_deriv_formula g n hz, hn.neg_one_pow, neg_one_mul, neg_mul]
  exact neg_neg_of_pos (mul_pos (by positivity) (B.positive_derivative_sum hg n hz))


/-- Continuous differentiability at every point strictly above the edge. -/
theorem contDiffAt_spectralSum (g : E) (n : ℕ) {z : ℝ} (hz : B.edge < z) :
    ContDiffAt ℝ n (B.spectralSum g) z :=
  (B.contDiffOn_spectralSum g n).contDiffAt (isOpen_Ioi.mem_nhds hz)

/-- The actual Taylor polynomial sum of iterated spectral derivatives divided by factorials. -/
noncomputable def taylor (g : E) (k : ℕ) (z δ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), iteratedDeriv j (B.spectralSum g) z * δ^j / j.factorial

/-- Identify the Mathlib Taylor polynomial on a unique-differentiability set with the spectral
Taylor sum. -/
theorem taylorWithinEval_eq {S : Set ℝ} (hS : UniqueDiffOn ℝ S)
    (g : E) (k : ℕ) {z : ℝ} (hz : B.edge < z) (hzS : z ∈ S) (δ : ℝ) :
    taylorWithinEval (B.spectralSum g) k S z (z + δ) = B.taylor g k z δ := by
  rw [taylor_within_apply]
  unfold taylor
  apply Finset.sum_congr rfl
  intro j _
  rw [iteratedDerivWithin_eq_iteratedDeriv hS (B.contDiffAt_spectralSum g j hz) hzS]
  simp only [add_sub_cancel_left, smul_eq_mul]
  ring

/-- The Lagrange remainder is an actual next derivative at an interior point times the
displacement power divided by factorial. -/
theorem taylor_remainder (g : E) (k : ℕ) {z δ : ℝ}
    (hz : B.edge < z) (hδ : δ ≠ 0) (hzδ : B.edge < z + δ) :
    ∃ y ∈ Set.uIoo z (z + δ), B.edge < y ∧
      B.spectralSum g (z + δ) - B.taylor g k z δ =
        iteratedDeriv (k + 1) (B.spectralSum g) y * δ^(k + 1) / (k + 1).factorial := by
  have hne : z ≠ z + δ := by intro hh; exact hδ (by linarith)
  have hI : Set.uIcc z (z + δ) ⊆ Set.Ioi B.edge := by
    intro y hy
    exact lt_of_lt_of_le (lt_min hz hzδ) hy.1
  obtain ⟨y, hy, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hne
    ((B.contDiffOn_spectralSum g (k + 1)).mono hI)
  refine ⟨y, hy, hI (Set.uIoo_subset_uIcc_self hy), ?_⟩
  rw [B.taylorWithinEval_eq (uniqueDiffOn_uIcc hne) g k hz (Set.left_mem_uIcc) δ,
    add_sub_cancel_left] at heq
  exact heq

/-- For a positive displacement every even Taylor polynomial strictly exceeds the nonzero
spectral function. -/
theorem taylor_upper_even {g : E} (hg : g ≠ 0) {k : ℕ} (hk : Even k)
    {z δ : ℝ} (hz : B.edge < z) (hδ : 0 < δ) :
    B.spectralSum g (z + δ) < B.taylor g k z δ := by
  obtain ⟨y, _, hy, heq⟩ := B.taylor_remainder g k hz hδ.ne' (by linarith)
  have hd := B.derivative_odd_neg hg hk.add_one hy
  have hh : iteratedDeriv (k + 1) (B.spectralSum g) y * δ^(k + 1) / (k + 1).factorial < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hd (pow_pos hδ _)) (by positivity)
  linarith

/-- For a positive displacement every odd Taylor polynomial is strictly below the nonzero
spectral function. -/
theorem taylor_lower_odd {g : E} (hg : g ≠ 0) {k : ℕ} (hk : Odd k)
    {z δ : ℝ} (hz : B.edge < z) (hδ : 0 < δ) :
    B.taylor g k z δ < B.spectralSum g (z + δ) := by
  obtain ⟨y, _, hy, heq⟩ := B.taylor_remainder g k hz hδ.ne' (by linarith)
  have hd := B.derivative_even_pos hg hk.add_one hy
  have hh : 0 < iteratedDeriv (k + 1) (B.spectralSum g) y * δ^(k + 1) / (k + 1).factorial :=
    div_pos (mul_pos hd (pow_pos hδ _)) (by positivity)
  linarith


/-- For a negative displacement staying above the edge every finite Taylor polynomial is
strictly below the nonzero spectral function. -/
theorem taylor_lower_negative {g : E} (hg : g ≠ 0) (k : ℕ)
    {z δ : ℝ} (hz : B.edge < z) (hδ : δ < 0) (hzδ : B.edge < z + δ) :
    B.taylor g k z δ < B.spectralSum g (z + δ) := by
  obtain ⟨y, _, hy, heq⟩ := B.taylor_remainder g k hz hδ.ne hzδ
  have hh : 0 < iteratedDeriv (k + 1) (B.spectralSum g) y * δ^(k + 1) := by
    rcases Nat.even_or_odd (k + 1) with hn | hn
    · exact mul_pos (B.derivative_even_pos hg hn hy) (hn.pow_pos hδ.ne)
    · exact mul_pos_of_neg_of_neg (B.derivative_odd_neg hg hn hy) (hn.pow_neg_iff.mpr hδ)
  have := div_pos hh (show (0 : ℝ) < (k + 1).factorial by positivity)
  linarith

omit [Nonempty ι] in
/-- Increasing Taylor order adds exactly the next actual derivative term. -/
theorem taylor_succ {g : E} (k : ℕ) (z δ : ℝ) :
    B.taylor g (k + 1) z δ = B.taylor g k z δ +
      iteratedDeriv (k + 1) (B.spectralSum g) z * δ^(k + 1) / (k + 1).factorial := by
  unfold taylor
  rw [Finset.sum_range_succ]

/-- For negative displacements the nonzero secular Taylor polynomials strictly increase with
order. -/
theorem taylor_increasing_negative {g : E} (hg : g ≠ 0) (k : ℕ)
    {z δ : ℝ} (hz : B.edge < z) (hδ : δ < 0) :
    B.taylor g k z δ < B.taylor g (k + 1) z δ := by
  rw [B.taylor_succ]
  have hh : 0 < iteratedDeriv (k + 1) (B.spectralSum g) z * δ^(k + 1) := by
    rcases Nat.even_or_odd (k + 1) with hn | hn
    · exact mul_pos (B.derivative_even_pos hg hn hz) (hn.pow_pos hδ.ne)
    · exact mul_pos_of_neg_of_neg (B.derivative_odd_neg hg hn hz) (hn.pow_neg_iff.mpr hδ)
  exact lt_add_of_pos_right _ (div_pos hh (by positivity))


omit [Nonempty ι] in
/-- The zero-gradient spectral Taylor polynomial vanishes at every order. -/
theorem taylor_zero (k : ℕ) (z δ : ℝ) : B.taylor 0 k z δ = 0 := by
  have hzero : B.spectralSum (0 : E) = (fun _ : ℝ => 0) := by
    funext x
    simp [spectralSum]
  unfold taylor
  rw [hzero]
  simp

/-- The actual inverse-defined secular function has the same iterated derivatives as its
proved spectral expression above the edge. -/
theorem iteratedDeriv_secular_eq [FiniteDimensional ℝ E] (g : E) (k : ℕ)
    {z : ℝ} (hz : B.edge < z) :
    iteratedDeriv k (secular H M g) z = iteratedDeriv k (B.spectralSum g) z := by
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
  exact B.secular_eq_sum y (fun i => ne_of_gt (B.denominator_pos hy i)) g

/-- The Taylor polynomial defined from actual inverse-based secular derivatives. -/
noncomputable def actualTaylor (H M : E →L[ℝ] E) (g : E) (k : ℕ) (z δ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), iteratedDeriv j (secular H M g) z * δ^j / j.factorial

/-- The actual inverse-based Taylor polynomial equals its spectral Taylor expression above the
edge. -/
theorem actualTaylor_eq [FiniteDimensional ℝ E] (g : E) (k : ℕ)
    {z : ℝ} (hz : B.edge < z) (δ : ℝ) :
    actualTaylor H M g k z δ = B.taylor g k z δ := by
  apply Finset.sum_congr rfl
  intro j _
  rw [B.iteratedDeriv_secular_eq g j hz]


/-- All source Taylor bounds for the actual inverse-defined secular function: alternating
estimates for positive displacements, increasing lower estimates for negative
displacements, and strictness exactly when the gradient is nonzero. -/
theorem actualTaylor_bounds [FiniteDimensional ℝ E] (g : E) (k : ℕ)
    {z δ : ℝ} (hz : B.edge < z) :
    (0 < δ →
      (Even k → secular H M g (z + δ) ≤ actualTaylor H M g k z δ ∧
        (g ≠ 0 → secular H M g (z + δ) < actualTaylor H M g k z δ)) ∧
      (Odd k → actualTaylor H M g k z δ ≤ secular H M g (z + δ) ∧
        (g ≠ 0 → actualTaylor H M g k z δ < secular H M g (z + δ)))) ∧
    (B.edge - z < δ → δ < 0 →
      actualTaylor H M g k z δ ≤ actualTaylor H M g (k + 1) z δ ∧
      actualTaylor H M g (k + 1) z δ ≤ secular H M g (z + δ) ∧
      (g ≠ 0 → actualTaylor H M g k z δ < actualTaylor H M g (k + 1) z δ ∧
        actualTaylor H M g (k + 1) z δ < secular H M g (z + δ))) := by
  have hpoly (j : ℕ) := B.actualTaylor_eq g j hz δ
  have hpi (hh : B.edge < z + δ) : secular H M g (z + δ) = B.spectralSum g (z + δ) :=
    B.secular_eq_sum (z + δ) (fun i => ne_of_gt (B.denominator_pos hh i)) g
  constructor
  · intro hδ
    rw [hpoly, hpi (by linarith)]
    by_cases hg : g = 0
    · subst g
      simp [B.taylor_zero, spectralSum]
    · exact ⟨fun hk => ⟨(B.taylor_upper_even hg hk hz hδ).le,
          fun _ => B.taylor_upper_even hg hk hz hδ⟩,
        fun hk => ⟨(B.taylor_lower_odd hg hk hz hδ).le,
          fun _ => B.taylor_lower_odd hg hk hz hδ⟩⟩
  · intro hedge hδ
    have hzδ : B.edge < z + δ := by linarith
    rw [hpoly, hpoly, hpi hzδ]
    by_cases hg : g = 0
    · subst g
      simp [B.taylor_zero, spectralSum]
    · exact ⟨(B.taylor_increasing_negative hg k hz hδ).le,
        (B.taylor_lower_negative hg (k + 1) hz hδ hzδ).le,
        fun _ => ⟨B.taylor_increasing_negative hg k hz hδ,
          B.taylor_lower_negative hg (k + 1) hz hδ hzδ⟩⟩

end QuadraticSecular.PencilBasis
