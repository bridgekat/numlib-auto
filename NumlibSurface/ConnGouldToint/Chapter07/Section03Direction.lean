import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The LINPACK hard-case direction

Section 7.3.7 of [conn2000trust]. The printed comparison of signed
forward-substitution candidates always selects the positive right-hand side.
For example, this choice misses the nullspace of the two-by-two all-ones
matrix. Comparing magnitudes gives a bound on every Cholesky pivot and
forces the normalized curvature to vanish at a singular limit.
-/

namespace ConnGouldToint.Chapter07

open Matrix Filter
open scoped Topology

/-- Choose the right-hand side sign giving the larger magnitude in the row. -/
noncomputable def linpackSign (b : ℝ) : ℝ :=
  if |1 - b| ≥ |-1 - b| then 1 else -1

theorem abs_linpackSign (b : ℝ) : |linpackSign b| = 1 := by
  unfold linpackSign
  split <;> norm_num

theorem one_le_abs_linpackSign_sub (b : ℝ) : 1 ≤ |linpackSign b - b| := by
  have ht := abs_sub_le (1 - b) 0 (-1 - b)
  have htwo : (1 : ℝ) - b - (-1 - b) = 2 := by ring
  rw [htwo, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), sub_zero,
    zero_sub, abs_neg] at ht
  unfold linpackSign
  split <;> linarith

/-- Rayleigh quotient of the back-solve vector for the shifted Hessian. -/
noncomputable def linpackCurvature {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (y : Fin n → ℝ) : ℝ :=
  (y ⬝ᵥ A *ᵥ y) / (y ⬝ᵥ y)

/-- A forward solve with the corrected row choices and its back solve
produce a direction with curvature controlled by the Cholesky determinant. -/
theorem linpackCurvature_bound {n : ℕ} (hn : 0 < n)
    {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsLowerTriangular)
    (hd : ∀ i, 0 < L i i) {v w y : Fin n → ℝ}
    (hw : L *ᵥ w = v) (hy : Lᵀ *ᵥ y = w)
    (hv : ∀ i, v i = linpackSign (v i - L i i * w i)) :
    0 ≤ linpackCurvature (L * Lᵀ) y ∧
      linpackCurvature (L * Lᵀ) y ^ n ≤ (n : ℝ) ^ n * (L * Lᵀ).det := by
  let q := linpackCurvature (L * Lᵀ) y
  have hs (i : Fin n) : 1 ≤ L i i * |w i| := by
    have hr := one_le_abs_linpackSign_sub (v i - L i i * w i)
    rw [← hv i, show v i - (v i - L i i * w i) = L i i * w i by ring,
      abs_mul, abs_of_pos (hd i)] at hr
    exact hr
  have hdprod (z : Fin n → ℝ) : z ⬝ᵥ z = ∑ i, z i ^ 2 := by
    simp [dotProduct, pow_two]
  have hnn (z : Fin n → ℝ) : 0 ≤ z ⬝ᵥ z := by
    rw [hdprod]
    exact Finset.sum_nonneg fun i _ => sq_nonneg (z i)
  have hnorm (z : Fin n → ℝ) (i : Fin n) : z i ^ 2 ≤ z ⬝ᵥ z := by
    rw [hdprod]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i)
  have hyy : 0 < y ⬝ᵥ y := by
    let i : Fin n := ⟨0, hn⟩
    have hne : y ≠ 0 := by
      intro h
      have hzero : w = 0 := by simpa [h] using hy.symm
      have := hs i
      simp [hzero] at this
      exact (not_le_of_gt zero_lt_one) this
    obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
      by_contra! hall
      exact hne (funext hall)
    exact (sq_pos_of_ne_zero hj).trans_le (hnorm y j)
  have hww : w ⬝ᵥ w = y ⬝ᵥ v := by
    rw [← hw, ← Matrix.dotProduct_transpose_mulVec, hy]
  have hq : q = (w ⬝ᵥ w) / (y ⬝ᵥ y) := by
    unfold q linpackCurvature
    rw [← Matrix.mulVec_mulVec, hy, hw, hww]
  have hq0 : 0 ≤ q := hq ▸ div_nonneg (hnn w) hyy.le
  have hvv : v ⬝ᵥ v = (n : ℝ) := by
    rw [hdprod]
    have hi (i : Fin n) : v i ^ 2 = 1 := by
      rw [← sq_abs (v i), hv i, abs_linpackSign, one_pow]
    simp [hi]
  have hcs : (w ⬝ᵥ w) ^ 2 ≤ (y ⬝ᵥ y) * (n : ℝ) := by
    rw [hww, ← hvv, hdprod y, hdprod v]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ y v
  have hmul : q * (w ⬝ᵥ w) ≤ (n : ℝ) := by
    rw [hq, div_mul_eq_mul_div, div_le_iff₀ hyy]
    simpa [pow_two, mul_comm] using hcs
  have hpiv (i : Fin n) : q ≤ (n : ℝ) * (L i i)^2 := by
    have hrow := pow_le_pow_left₀ zero_le_one (hs i) 2
    rw [one_pow, mul_pow, sq_abs] at hrow
    have hi : 1 ≤ (L i i)^2 * (w ⬝ᵥ w) :=
      hrow.trans (mul_le_mul_of_nonneg_left (hnorm w i) (sq_nonneg _))
    calc
      q = q * 1 := (mul_one q).symm
      _ ≤ q * ((L i i)^2 * (w ⬝ᵥ w)) := mul_le_mul_of_nonneg_left hi hq0
      _ = (q * (w ⬝ᵥ w)) * (L i i)^2 := by ring
      _ ≤ (n : ℝ) * (L i i)^2 := mul_le_mul_of_nonneg_right hmul (sq_nonneg _)
  refine ⟨hq0, ?_⟩
  calc
    q ^ n = ∏ _i : Fin n, q := by simp
    _ ≤ ∏ i : Fin n, (n : ℝ) * (L i i)^2 :=
      Finset.prod_le_prod₀ (fun _ _ => hq0) (fun i _ => hpiv i)
    _ = (n : ℝ) ^ n * (L * Lᵀ).det := by
      have hprod : (∏ i : Fin n, (L i i)^2) = (∏ i : Fin n, L i i)^2 :=
        Finset.prod_pow Finset.univ 2 (fun i : Fin n => L i i)
      rw [Finset.prod_mul_distrib, hprod, Matrix.det_mul,
        Matrix.det_transpose, Matrix.det_of_isLowerTriangular L hL]
      simp [pow_two]

/-- The normalized curvature tends to zero when the shifted Hessian
determinants tend to zero. This proves (7.3.16) for the magnitude comparison. -/
theorem linpackCurvature_tendsto_zero {n : ℕ} (hn : 0 < n)
    {L : ℕ → Matrix (Fin n) (Fin n) ℝ} {v w y : ℕ → Fin n → ℝ}
    (hL : ∀ k, (L k).IsLowerTriangular) (hd : ∀ k i, 0 < L k i i)
    (hw : ∀ k, L k *ᵥ w k = v k) (hy : ∀ k, (L k)ᵀ *ᵥ y k = w k)
    (hv : ∀ k i, v k i = linpackSign (v k i - L k i i * w k i))
    (hlim : Tendsto (fun k => (L k * (L k)ᵀ).det) atTop (𝓝 0)) :
    Tendsto (fun k => linpackCurvature (L k * (L k)ᵀ) (y k)) atTop (𝓝 0) := by
  have hb (k : ℕ) := linpackCurvature_bound hn (hL k) (hd k) (hw k) (hy k) (hv k)
  have ht : Tendsto (fun k => (n : ℝ)^n * (L k * (L k)ᵀ).det) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hlim (a := (n : ℝ)^n)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (ht.eventually (eventually_lt_nhds (pow_pos hε n)))
  refine ⟨K, fun k hk => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hb k).1]
  by_contra! hc
  exact (not_lt_of_ge (pow_le_pow_left₀ hε.le hc n)) ((hb k).2.trans_lt (hK k hk))

/-- The Rayleigh quotient is the quadratic form at any unit normalization of
the same direction. -/
theorem linpackCurvature_eq_of_normalization {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {u y : Fin n → ℝ} {c : ℝ}
    (hu : u = c • y) (hunit : u ⬝ᵥ u = 1) :
    linpackCurvature A y = u ⬝ᵥ A *ᵥ u := by
  rw [hu, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  rw [hu, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hunit
  have hyy : y ⬝ᵥ y ≠ 0 := by
    intro hz
    simp [hz] at hunit
  unfold linpackCurvature
  apply (div_eq_iff hyy).2
  calc
    _ = 1 * (y ⬝ᵥ A *ᵥ y) := by ring
    _ = _ := by rw [← hunit]; ring

/-- For Cholesky factors tending to a singular positive semidefinite shifted
Hessian, the quadratic forms of the normalized directions tend to zero.
The directions approach the kernel of the singular shifted Hessian, which
is the leftmost eigenspace of the unshifted Hessian. -/
theorem linpackDirection_limit {n : ℕ} (hn : 0 < n)
    {L : ℕ → Matrix (Fin n) (Fin n) ℝ} {v w y u : ℕ → Fin n → ℝ}
    (hL : ∀ k, (L k).IsLowerTriangular) (hd : ∀ k i, 0 < L k i i)
    (hw : ∀ k, L k *ᵥ w k = v k) (hy : ∀ k, (L k)ᵀ *ᵥ y k = w k)
    (hv : ∀ k i, v k i = linpackSign (v k i - L k i i * w k i))
    (hu : ∀ k, ∃ c : ℝ, u k = c • y k) (hunit : ∀ k, u k ⬝ᵥ u k = 1)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (hdet : A.det = 0)
    (hlim : Tendsto (fun k => L k * (L k)ᵀ) atTop (𝓝 A)) :
    Tendsto (fun k => u k ⬝ᵥ (L k * (L k)ᵀ) *ᵥ u k) atTop (𝓝 0) ∧
      Tendsto (fun k => Metric.infDist (u k) {z | A *ᵥ z = 0}) atTop (𝓝 0) := by
  have hdetlim : Tendsto (fun k => (L k * (L k)ᵀ).det) atTop (𝓝 0) := by
    rw [← hdet]
    exact continuous_id.matrix_det.continuousAt.tendsto.comp hlim
  have h := linpackCurvature_tendsto_zero hn hL hd hw hy hv hdetlim
  have heq (k : ℕ) :
      linpackCurvature (L k * (L k)ᵀ) (y k) = u k ⬝ᵥ (L k * (L k)ᵀ) *ᵥ u k := by
    obtain ⟨c, hc⟩ := hu k
    exact linpackCurvature_eq_of_normalization _ hc (hunit k)
  simp only [heq] at h
  have hkernel (j : ℕ → ℕ) (z : Fin n → ℝ) (hj : Tendsto j atTop atTop)
      (hz : Tendsto (u ∘ j) atTop (𝓝 z)) : A *ᵥ z = 0 := by
    have hcont : Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) =>
        p.2 ⬝ᵥ p.1 *ᵥ p.2) := by
      unfold dotProduct
      fun_prop
    have hq := hcont.continuousAt.tendsto.comp ((hlim.comp hj).prodMk_nhds hz)
    have hzero : z ⬝ᵥ A *ᵥ z = 0 := tendsto_nhds_unique hq (h.comp hj)
    exact hA.dotProduct_mulVec_zero_iff.mp (by simpa using hzero)
  let K : Set (Fin n → ℝ) := {z | A *ᵥ z = 0}
  let B : Set (Fin n → ℝ) := Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1)
  have hB : IsCompact B := isCompact_univ_pi fun _ => isCompact_Icc
  have huB (k : ℕ) : u k ∈ B := by
    intro i _
    have hs : (u k i)^2 ≤ u k ⬝ᵥ u k := by
      simp only [dotProduct, ← pow_two]
      exact Finset.single_le_sum (fun j _ => sq_nonneg (u k j)) (Finset.mem_univ i)
    rw [hunit k] at hs
    exact ⟨by nlinarith, by nlinarith⟩
  refine ⟨h, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  by_contra hE
  have hf : ∃ᶠ k in atTop, ε ≤ Metric.infDist (u k) K := by
    simpa only [Filter.Frequently, not_le, Real.dist_eq, sub_zero,
      abs_of_nonneg Metric.infDist_nonneg] using hE
  obtain ⟨j, hj, hjε⟩ := exists_seq_forall_of_frequently hf
  obtain ⟨z, _, l, hl, hz⟩ := hB.tendsto_subseq (x := u ∘ j) (fun k => huB (j k))
  have hzK : z ∈ K := hkernel (j ∘ l) z (hj.comp hl.tendsto_atTop) hz
  have hdist : Tendsto (fun k => Metric.infDist (u (j (l k))) K) atTop (𝓝 0) := by
    rw [← Metric.infDist_zero_of_mem hzK]
    exact (Metric.continuous_infDist_pt K).continuousAt.tendsto.comp hz
  have hε' := hdist.eventually (eventually_lt_nhds hε)
  exact (hε'.and (Eventually.of_forall fun k => hjε (l k))).exists.elim
    (fun _ hk => (not_lt_of_ge hk.2) hk.1)

/-- The back solve at a failed Cholesky pivot gives a kernel vector of the
rank-one corrected leading principal block. If the pivot occurs before the
last row, the zero extension can have nonzero residual in later rows, so the
kernel equation in (7.3.17) is stated on the leading principal block. -/
theorem failedCholeskyPivotDirection {n : ℕ} {L : Matrix (Fin n) (Fin n) ℝ}
    (hL : L.IsLowerTriangular) (hd : ∀ i, 0 < L i i)
    (C : Matrix Unit (Fin n) ℝ) (δ : ℝ)
    (B : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
    (e : Fin n ⊕ Unit → ℝ) (he : e = Sum.elim (0 : Fin n → ℝ) (fun _ : Unit => 1))
    (hB : B + δ • vecMulVec e e = fromRows L C * (fromRows L C)ᵀ) :
    ∃ v : Fin n ⊕ Unit → ℝ, v (Sum.inr ()) = 1 ∧
      (B + δ • vecMulVec e e) *ᵥ v = 0 ∧ v ⬝ᵥ B *ᵥ v = -δ := by
  have hdet : Lᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose, Matrix.det_of_isLowerTriangular L hL]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (hd i).ne'
  have hunit : IsUnit Lᵀ := (Matrix.isUnit_iff_isUnit_det Lᵀ).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨y, hy⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hunit
    (-(Cᵀ *ᵥ (fun _ => 1)))
  let v : Fin n ⊕ Unit → ℝ := Sum.elim y (fun _ => 1)
  have hzero : (fromRows L C)ᵀ *ᵥ v = 0 := by
    rw [Matrix.transpose_fromRows]
    change fromCols Lᵀ Cᵀ *ᵥ Sum.elim y (fun _ => 1) = 0
    rw [Matrix.fromCols_mulVec_sumElim, hy, neg_add_cancel]
  have hker : (B + δ • vecMulVec e e) *ᵥ v = 0 := by
    rw [hB, ← Matrix.mulVec_mulVec, hzero, Matrix.mulVec_zero]
  have hev : e ⬝ᵥ v = 1 := by
    rw [he]
    change Sum.elim 0 (fun _ : Unit => (1 : ℝ)) ⬝ᵥ Sum.elim y (fun _ => 1) = 1
    rw [sumElim_dotProduct_sumElim]
    simp [dotProduct]
  have hve : v ⬝ᵥ e = 1 := (dotProduct_comm _ _).trans hev
  have houter : vecMulVec e e *ᵥ v = e := by
    rw [Matrix.vecMulVec_mulVec, hev, MulOpposite.op_one, one_smul]
  have hquadratic := congrArg (fun z => v ⬝ᵥ z) hker
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, houter, dotProduct_add,
    dotProduct_smul, hve, smul_eq_mul, mul_one, dotProduct_zero] at hquadratic
  exact ⟨v, rfl, hker, by linarith⟩

/-- The computed pivot correction is the deficit between the accumulated
row square and the uncorrected pivot entry. -/
theorem failedCholeskyPivot_correction {n : ℕ} {L : Matrix (Fin n) (Fin n) ℝ}
    (hL : L.IsLowerTriangular) (hd : ∀ i, 0 < L i i)
    (C : Matrix Unit (Fin n) ℝ) (d : ℝ) (hpivot : d ≤ (C * Cᵀ) () ()) :
    let B := fromBlocks (L * Lᵀ) (L * Cᵀ) (C * Lᵀ) (Matrix.of fun _ _ : Unit => d)
    let δ := (C * Cᵀ) () () - d
    let e : Fin n ⊕ Unit → ℝ := Sum.elim (0 : Fin n → ℝ) (fun _ : Unit => 1)
    0 ≤ δ ∧ ∃ v : Fin n ⊕ Unit → ℝ, v (Sum.inr ()) = 1 ∧
      (B + δ • vecMulVec e e) *ᵥ v = 0 ∧ v ⬝ᵥ B *ᵥ v = -δ := by
  dsimp only
  refine ⟨sub_nonneg.mpr hpivot, failedCholeskyPivotDirection hL hd C _ _ _ rfl ?_⟩
  rw [Matrix.transpose_fromRows, Matrix.fromRows_mul_fromCols]
  ext (i | i) (j | j)
  · simp [vecMulVec]
  · cases j
    simp [vecMulVec]
  · cases i
    simp [vecMulVec]
  · cases i
    cases j
    simp [vecMulVec]

/-- Correcting the first pivot of this matrix kills the leading residual
but leaves the second coordinate equal to one. -/
theorem failedCholeskyPivot_full_residual_counterexample :
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 1; 1, 1]
    let e : Fin 2 → ℝ := ![1, 0]
    (B + vecMulVec e e) *ᵥ e = ![0, 1] := by
  dsimp only
  ext i
  fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two, vecMulVec]

/-- The full shifted Hessian gives the same Rayleigh quotient as its leading
principal block at the zero extension of the failed-pivot direction. The
resulting lower bound is valid even when the full residual is nonzero. -/
theorem failedCholeskyPivot_lower_bound {n : ℕ} {ι : Type*} [Fintype ι]
    {B : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ}
    (C : Matrix (Fin n ⊕ Unit) ι ℝ) (D : Matrix ι (Fin n ⊕ Unit) ℝ)
    (F : Matrix ι ι ℝ) {lam lamMin δ : ℝ} {v : Fin n ⊕ Unit → ℝ}
    (hv : v (Sum.inr ()) = 1) (hq : v ⬝ᵥ B *ᵥ v = -δ)
    (hRayleigh : ∀ z, (lam + lamMin) * (z ⬝ᵥ z) ≤
      z ⬝ᵥ fromBlocks B C D F *ᵥ z) :
    lam + δ / (v ⬝ᵥ v) ≤ -lamMin := by
  have hnorm : 0 < v ⬝ᵥ v := by
    have hs : v (Sum.inr ()) ^ 2 ≤ ∑ i, v i ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (v i)) (Finset.mem_univ _)
    rw [hv, one_pow] at hs
    have hd : v ⬝ᵥ v = ∑ i, v i ^ 2 := by simp [dotProduct, pow_two]
    rw [hd]
    exact zero_lt_one.trans_le hs
  have hr := hRayleigh (Sum.elim v 0)
  rw [Matrix.fromBlocks_mulVec] at hr
  have hl : Sum.elim v (0 : ι → ℝ) ∘ Sum.inl = v := rfl
  have ht : Sum.elim v (0 : ι → ℝ) ∘ Sum.inr = 0 := rfl
  simp only [hl, ht, Matrix.mulVec_zero, add_zero, sumElim_dotProduct_sumElim,
    zero_dotProduct, hq] at hr
  have hdiv : δ / (v ⬝ᵥ v) ≤ -(lam + lamMin) := by
    apply (div_le_iff₀ hnorm).2
    nlinarith only [hr]
  linarith

end ConnGouldToint.Chapter07
