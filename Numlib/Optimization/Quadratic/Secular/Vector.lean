import Numlib.Optimization.Quadratic.Secular.Taylor

/-!
# Actual derivatives of the shifted pencil solution

Every actual vector derivative is computed from the proved spectral formula for
the genuine inverse. The differentiated shifted system and odd/even scalar
contractions follow algebraically. Nonsingular shifts include positive-definite
zero shifts, without a strict positive-shift restriction.
-/

open scoped BigOperators Topology
open Filter
namespace QuadraticSecular.PencilBasis
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι] {H M : E →L[ℝ] E} (B : PencilBasis (ι := ι) H M)

/-- The finite spectral vector expression for the actual shifted-system solution. -/
noncomputable def vectorSum (g : E) (z : ℝ) : E :=
  ∑ i, (-inner ℝ g (B.basis i) / (z + B.eigenvalue i)) • B.basis i

omit [Fintype ι] in
/-- All nonsingular spectral denominators stay nonsingular in a neighborhood. -/
theorem eventually_nonsingular [Finite ι] {z : ℝ} (hz : ∀ i, z + B.eigenvalue i ≠ 0) :
    ∀ᶠ y in 𝓝 z, ∀ i, y + B.eigenvalue i ≠ 0 := by
  apply Filter.eventually_all.mpr
  intro i
  exact (continuousAt_id.add continuousAt_const).eventually_ne (hz i)

/-- The actual inverse-defined solution has the same derivatives as its spectral vector sum. -/
theorem iteratedDeriv_solution_eq [FiniteDimensional ℝ E] (g : E) (n : ℕ)
    {z : ℝ} (hz : ∀ i, z + B.eigenvalue i ≠ 0) :
    iteratedDeriv n (solution H M g) z = iteratedDeriv n (B.vectorSum g) z := by
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [B.eventually_nonsingular hz] with y hy
  exact B.solution_eq_sum y hy g

/-- Every finite order of the spectral vector expression is continuously differentiable
at every nonsingular shift. -/
theorem contDiffAt_vectorSum (g : E) (n : ℕ) {z : ℝ}
    (hz : ∀ i, z + B.eigenvalue i ≠ 0) : ContDiffAt ℝ n (B.vectorSum g) z := by
  apply ContDiffAt.sum
  intro i _
  exact (contDiffAt_const.div (contDiffAt_id.add contDiffAt_const) (hz i)).smul
    contDiffAt_const

/-- The translated reciprocal has its actual factorial derivative at every order. -/
theorem shifted_reciprocal_deriv (n : ℕ) (a z : ℝ) :
    iteratedDeriv n (fun x : ℝ => (x + a) ^ (-1 : ℤ)) z =
      (∏ i ∈ Finset.range n, (-1 - (i : ℝ))) * (z + a) ^ (-1 - (n : ℤ)) := by
  calc _ = iteratedDeriv n (fun y : ℝ => y ^ (-1 : ℤ)) (z + a) :=
      congrFun (iteratedDeriv_comp_add_const n (fun y : ℝ => y ^ (-1 : ℤ)) a) z
    _ = _ := by
      rw [iteratedDeriv_eq_iterate, iter_deriv_zpow]
      norm_num

/-- The reciprocal falling-factor product has magnitude n factorial and alternating sign. -/
theorem product_neg_one_sub (n : ℕ) :
    (∏ i ∈ Finset.range n, (-1 - (i : ℝ))) = (-1 : ℝ)^n * (n.factorial : ℝ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ, pow_succ]
    push_cast
    ring

/-- The exact vector derivative formula, computed from the actual spectral solution. -/
theorem vectorSum_deriv_formula (g : E) (n : ℕ) {z : ℝ}
    (hz : ∀ i, z + B.eigenvalue i ≠ 0) :
    iteratedDeriv n (B.vectorSum g) z =
      ∑ i, (((-1 : ℝ)^(n + 1) * (n.factorial : ℝ) * inner ℝ g (B.basis i)) /
        (z + B.eigenvalue i) ^ (n + 1)) • B.basis i := by
  have hf (i : ι) : ContDiffAt ℝ n
      (fun x : ℝ => -inner ℝ g (B.basis i) / (x + B.eigenvalue i)) z :=
    contDiffAt_const.div (contDiffAt_id.add contDiffAt_const) (hz i)
  change iteratedDeriv n (fun x => ∑ i,
    (-inner ℝ g (B.basis i) / (x + B.eigenvalue i)) • B.basis i) z = _
  have hsum := iteratedDeriv_fun_sum
    (I := (Finset.univ : Finset ι))
    (f := fun i x => (-inner ℝ g (B.basis i) / (x + B.eigenvalue i)) • B.basis i)
    (fun i _ => (hf i).smul contDiffAt_const)
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedDeriv_smul_const (hf i)]
  have heq : (fun x : ℝ => -inner ℝ g (B.basis i) / (x + B.eigenvalue i)) =
      (fun x => -inner ℝ g (B.basis i) * (x + B.eigenvalue i) ^ (-1 : ℤ)) := by
    ext x
    simp [div_eq_mul_inv, zpow_neg]
  rw [heq, iteratedDeriv_const_mul_field, shifted_reciprocal_deriv, product_neg_one_sub]
  have he : (-1 : ℤ) - (n : ℤ) = -((n + 1 : ℕ) : ℤ) := by omega
  rw [he, zpow_neg, zpow_natCast, pow_succ]
  congr 1
  ring

/-- Every actual vector derivative is its finite resolvent spectral sum. -/
theorem iteratedDeriv_solution_formula [FiniteDimensional ℝ E] (g : E) (n : ℕ)
    {z : ℝ} (hz : ∀ i, z + B.eigenvalue i ≠ 0) :
    iteratedDeriv n (solution H M g) z =
      ∑ i, (((-1 : ℝ)^(n + 1) * (n.factorial : ℝ) * inner ℝ g (B.basis i)) /
        (z + B.eigenvalue i) ^ (n + 1)) • B.basis i := by
  rw [B.iteratedDeriv_solution_eq g n hz, B.vectorSum_deriv_formula g n hz]

omit [Fintype ι] in
/-- Every actual derivative vector solves the differentiated shifted linear system. -/
theorem shifted_iteratedDeriv_succ [Finite ι] [FiniteDimensional ℝ E] (g : E) (n : ℕ)
    {z : ℝ} (hz : ∀ i, z + B.eigenvalue i ≠ 0) :
    (H + z • M) (iteratedDeriv (n + 1) (solution H M g) z) =
      -(n + 1 : ℝ) • M (iteratedDeriv n (solution H M g) z) := by
  let := Fintype.ofFinite ι
  rw [B.iteratedDeriv_solution_formula g (n + 1) hz,
    B.iteratedDeriv_solution_formula g n hz, B.shifted_sum]
  simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  simp only [pow_succ]
  field_simp

/-- The actual scalar secular derivative at every nonsingular shift. -/
theorem iteratedDeriv_secular_formula [FiniteDimensional ℝ E] (g : E) (n : ℕ)
    {z : ℝ} (hz : ∀ i, z + B.eigenvalue i ≠ 0) :
    iteratedDeriv n (secular H M g) z =
      (-1 : ℝ)^n * ((n + 1).factorial : ℝ) *
        ∑ i, (inner ℝ g (B.basis i)) ^ 2 / (z + B.eigenvalue i) ^ (n + 2) := by
  have heq : secular H M g =ᶠ[𝓝 z] B.spectralSum g := by
    filter_upwards [B.eventually_nonsingular hz] with y hy
    exact B.secular_eq_sum y hy g
  rw [heq.iteratedDeriv_eq]
  have hf (i : ι) : ContDiffAt ℝ n
      (fun x => (inner ℝ g (B.basis i)) ^ 2 / (x + B.eigenvalue i) ^ 2) z :=
    contDiffAt_const.div ((contDiffAt_id.add contDiffAt_const).pow 2)
      (pow_ne_zero _ (hz i))
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
  rw [heq, iteratedDeriv_const_mul_field, shifted_power_deriv, product_neg_two_sub]
  have he : (-2 : ℤ) - (n : ℤ) = -((n + 2 : ℕ) : ℤ) := by omega
  rw [he, zpow_neg, zpow_natCast]
  ring

/-- Metric pairing of two finite spectral combinations is their scalar coefficient pairing. -/
theorem inner_metric_sum_pair (c d : ι → ℝ) :
    inner ℝ (∑ i, c i • B.basis i) (M (∑ i, d i • B.basis i)) = ∑ i, c i * d i := by
  rw [real_inner_comm]
  simp only [inner_sum, real_inner_smul_right, B.inner_metric_sum]

end QuadraticSecular.PencilBasis

namespace QuadraticSecular

/-- The factorial coefficient in the odd/even secular derivative contractions. -/
noncomputable def derivativeCoefficient (k : ℕ) : ℝ :=
  ((2 * k + 1).factorial : ℝ) / (k.factorial : ℝ) ^ 2

/-- The initial contraction coefficient is one. -/
@[simp] theorem derivativeCoefficient_zero : derivativeCoefficient 0 = 1 := by
  norm_num [derivativeCoefficient]

/-- The source recurrence for the actual derivative contraction coefficients. -/
theorem derivativeCoefficient_succ (k : ℕ) :
    derivativeCoefficient (k + 1) =
      2 * ((2 * k + 3 : ℝ) / (k + 1)) * derivativeCoefficient k := by
  have he : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
  unfold derivativeCoefficient
  rw [he, Nat.factorial_succ (2 * k + 1 + 1), Nat.factorial_succ (2 * k + 1),
    Nat.factorial_succ k]
  push_cast
  field_simp
  ring

/-- The factorial cancellation for odd secular derivatives. -/
theorem derivativeCoefficient_mul_factorials (k : ℕ) :
    2 * derivativeCoefficient k * (k.factorial : ℝ) * ((k + 1).factorial : ℝ) =
      ((2 * k + 2).factorial : ℝ) := by
  unfold derivativeCoefficient
  rw [Nat.factorial_succ k, show 2 * k + 2 = (2 * k + 1) + 1 by omega,
    Nat.factorial_succ (2 * k + 1)]
  push_cast
  field_simp
  ring

/-- The even contraction coefficient cancels both derivative-vector factorials. -/
theorem derivativeCoefficient_mul_sq_factorial (k : ℕ) :
    derivativeCoefficient k * (k.factorial : ℝ) ^ 2 = ((2 * k + 1).factorial : ℝ) := by
  unfold derivativeCoefficient
  exact div_mul_cancel₀ _ (by positivity)

/-- The scalar odd-order contraction identity for one spectral coordinate. -/
theorem odd_coordinate_identity (k : ℕ) (c d : ℝ) :
    (-1 : ℝ)^(2 * k + 1) * ((2 * k + 2).factorial : ℝ) * c ^ 2 / d ^ (2 * k + 3) =
      2 * derivativeCoefficient k *
        (((-1 : ℝ)^(k + 1) * (k.factorial : ℝ) * c) / d ^ (k + 1)) *
        (((-1 : ℝ)^(k + 2) * ((k + 1).factorial : ℝ) * c) / d ^ (k + 2)) := by
  rw [← derivativeCoefficient_mul_factorials k]
  have hs : ((-1 : ℝ)^k)^2 = 1 := by
    rw [← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  have hodd : (-1 : ℝ)^(2 * k + 1) = -1 := by simp [pow_add, pow_mul]
  have hone : (-1 : ℝ)^(k + 1) = -((-1 : ℝ)^k) := by rw [pow_succ]; ring
  have htwo : (-1 : ℝ)^(k + 2) = (-1 : ℝ)^k := by rw [pow_add]; norm_num
  rw [hodd, hone, htwo]
  have hn : 2 * derivativeCoefficient k *
      (-((-1 : ℝ)^k) * (k.factorial : ℝ) * c) *
      (((-1 : ℝ)^k) * ((k + 1).factorial : ℝ) * c) =
      -1 * (2 * derivativeCoefficient k * (k.factorial : ℝ) *
        ((k + 1).factorial : ℝ)) * c ^ 2 := by
    calc _ = -((-1 : ℝ)^k)^2 * (2 * derivativeCoefficient k *
          (k.factorial : ℝ) * ((k + 1).factorial : ℝ) * c ^ 2) := by ring
      _ = _ := by rw [hs]; ring
  calc
    _ = (2 * derivativeCoefficient k *
        (-((-1 : ℝ)^k) * (k.factorial : ℝ) * c) *
        (((-1 : ℝ)^k) * ((k + 1).factorial : ℝ) * c)) /
        (d ^ (k + 1) * d ^ (k + 2)) := by
      rw [← pow_add, (show k + 1 + (k + 2) = 2 * k + 3 by omega), hn]
    _ = _ := by ring

/-- The scalar even-order contraction identity for one spectral coordinate. -/
theorem even_coordinate_identity (k : ℕ) (c d : ℝ) :
    (-1 : ℝ)^(2 * k + 2) * ((2 * k + 3).factorial : ℝ) * c ^ 2 / d ^ (2 * k + 4) =
      derivativeCoefficient (k + 1) *
        ((((-1 : ℝ)^(k + 2) * ((k + 1).factorial : ℝ) * c) / d ^ (k + 2)) ^ 2) := by
  have he : 2 * k + 3 = 2 * (k + 1) + 1 := by omega
  rw [he, ← derivativeCoefficient_mul_sq_factorial (k + 1)]
  have hs : ((-1 : ℝ)^k)^2 = 1 := by
    rw [← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  simp only [pow_add, pow_mul, neg_one_sq, one_pow]
  norm_num
  rw [div_pow, mul_pow, mul_pow, hs]
  simp only [one_mul]
  rw [← pow_mul]
  ring_nf

end QuadraticSecular

namespace QuadraticSecular.PencilBasis
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι] {H M : E →L[ℝ] E} (B : PencilBasis (ι := ι) H M)

omit [Fintype ι] in
/-- Every actual odd secular derivative is a contraction of consecutive true vector derivatives. -/
theorem iteratedDeriv_secular_odd [Finite ι] [FiniteDimensional ℝ E] (g : E) (k : ℕ)
    {z : ℝ} (hz : ∀ i, z + B.eigenvalue i ≠ 0) :
    iteratedDeriv (2 * k + 1) (secular H M g) z = 2 * derivativeCoefficient k *
      inner ℝ (iteratedDeriv k (solution H M g) z)
        (M (iteratedDeriv (k + 1) (solution H M g) z)) := by
  let := Fintype.ofFinite ι
  rw [B.iteratedDeriv_secular_formula g (2 * k + 1) hz,
    B.iteratedDeriv_solution_formula g k hz,
    B.iteratedDeriv_solution_formula g (k + 1) hz, B.inner_metric_sum_pair,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  convert odd_coordinate_identity k (inner ℝ g (B.basis i)) (z + B.eigenvalue i) using 1 <;>
    ring

omit [Fintype ι] in
/-- Every actual even secular derivative is the metric squared norm of a true vector derivative. -/
theorem iteratedDeriv_secular_even [Finite ι] [FiniteDimensional ℝ E] (g : E) (k : ℕ)
    {z : ℝ} (hz : ∀ i, z + B.eigenvalue i ≠ 0) :
    iteratedDeriv (2 * k + 2) (secular H M g) z = derivativeCoefficient (k + 1) *
      inner ℝ (iteratedDeriv (k + 1) (solution H M g) z)
        (M (iteratedDeriv (k + 1) (solution H M g) z)) := by
  let := Fintype.ofFinite ι
  rw [B.iteratedDeriv_secular_formula g (2 * k + 2) hz,
    B.iteratedDeriv_solution_formula g (k + 1) hz, B.inner_metric_sum_pair,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  convert even_coordinate_identity k (inner ℝ g (B.basis i)) (z + B.eigenvalue i) using 1 <;>
    ring

omit [Fintype ι] in
/-- Positive definiteness of the actual shifted pencil makes every spectral denominator positive. -/
theorem denominator_pos_of_positive [Finite ι] {z : ℝ}
    (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ ((H + z • M) v) v) (i : ι) :
    0 < z + B.eigenvalue i := by
  have hh := hpos (B.basis i) (B.basis.ne_zero i)
  have hi := B.orthonormal i i
  simp only [ite_true] at hi
  simpa only [add_apply, smul_apply, B.eigenvector, inner_add_left,
    inner_smul_left, conj_trivial, hi, mul_one, add_comm] using hh

end QuadraticSecular.PencilBasis
