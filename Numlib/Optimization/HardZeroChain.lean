import Numlib.Analysis.FlatGaussian
import Numlib.Optimization.ZeroChains
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The explicit smooth Gaussian chain

The scalar factors and the finite chain are actual functions. The seed is
`-psi 1 * phi x₀`, following Carmon, Duchi, Hinder and Sidford,
*Lower Bounds for Finding Stationary Points I*, arXiv:1710.11606v3,
equation (10), page 12. This corrects the transcription `-psi x₀ * phi x₀`
in the supplied OCR of Cartis, Gould and Toint, equation (4.2.6).

This module proves the scalar regularity and elementary bounds and the chain's
smoothness. The uniform all-order derivative estimates are separate obligations.
-/

noncomputable section
open scoped ContDiff Topology
open Real Analysis.FlatGaussian Filter

namespace Optimization.HardZeroChain

/-- The flat scalar switch in the Gaussian chain. -/
def psi (y : ℝ) : ℝ := exp 1 * cutoff (2 * y - 1)

/-- The positive Gaussian primitive in the chain. -/
abbrev phi := primitive

/-- The switch is zero up to and including one half. -/
theorem psi_eq_zero {y : ℝ} (hy : y ≤ 1 / 2) : psi y = 0 := by
  rw [psi, cutoff_eq_zero (by linarith), mul_zero]

/-- Above one half, the switch has the source's inverse-square exponential formula. -/
theorem psi_eq_exp {y : ℝ} (hy : 1 / 2 < y) :
    psi y = exp (1 - ((2 * y - 1)⁻¹) ^ 2) := by
  rw [psi, cutoff_eq_exp (by linarith), ← exp_add]
  simp only [sub_eq_add_neg]

/-- The scalar switch has exactly the prescribed piecewise formula. -/
theorem psi_eq_piecewise (y : ℝ) :
    psi y = if y ≤ 1 / 2 then 0 else exp (1 - ((2 * y - 1)⁻¹) ^ 2) := by
  split_ifs with hy
  · exact psi_eq_zero hy
  · exact psi_eq_exp (lt_of_not_ge hy)

/-- The scalar switch is infinitely smooth across its flat junction. -/
@[fun_prop] theorem contDiff_psi : ContDiff ℝ ∞ psi := by
  exact contDiff_const.mul
    (contDiff_cutoff.comp (contDiff_const.mul contDiff_id |>.sub contDiff_const))

/-- Every scalar derivative vanishes on the flat half-line, including the junction. -/
theorem iteratedDeriv_psi_eq_zero (q : ℕ) {y : ℝ} (hy : y ≤ 1 / 2) :
    iteratedDeriv q psi y = 0 := by
  unfold psi
  have hc : ContDiff ℝ ∞ (fun y : ℝ ↦ cutoff (2 * y - 1)) :=
    contDiff_cutoff.comp (by fun_prop)
  rw [iteratedDeriv_const_mul (f := fun y : ℝ ↦ cutoff (2 * y - 1)) _
    (hc.of_le (by simp)).contDiffAt]
  have heq : (fun y : ℝ ↦ cutoff (2 * y - 1)) =
      fun y ↦ (fun z ↦ cutoff (z - 1)) (2 * y) := rfl
  have hs : ContDiff ℝ (q : ℕ) (fun z : ℝ ↦ cutoff (z - 1)) :=
    contDiff_cutoff.comp (by fun_prop)
  rw [heq, iteratedDeriv_comp_const_mul hs (2 : ℝ), iteratedDeriv_comp_sub_const]
  dsimp only
  rw [iteratedDeriv_cutoff_eq_zero q (by linarith), mul_zero, mul_zero]

/-- The scalar switch is nonnegative. -/
theorem psi_nonneg (y : ℝ) : 0 ≤ psi y := mul_nonneg (exp_pos _).le (cutoff_nonneg _)

/-- The scalar switch is bounded above by `e`. -/
theorem psi_le_exp_one (y : ℝ) : psi y ≤ exp 1 := by
  by_cases hy : y ≤ 1 / 2
  · rw [psi_eq_zero hy]
    positivity
  · rw [psi_eq_exp (lt_of_not_ge hy)]
    exact exp_le_exp.mpr (sub_le_self _ (sq_nonneg _))

/-- The scalar switch is positive exactly above its junction. -/
theorem psi_pos_iff (y : ℝ) : 0 < psi y ↔ 1 / 2 < y := by
  rw [psi, mul_pos_iff_of_pos_left (exp_pos _), cutoff_pos_iff]
  constructor <;> intro h <;> linarith

/-- The scalar switch is normalized to one at one. -/
@[simp] theorem psi_one : psi 1 = 1 := by
  rw [psi_eq_exp (by norm_num : (1 / 2 : ℝ) < 1)]
  norm_num

/-- The scalar switch is monotone. -/
theorem monotone_psi : Monotone psi := by
  intro x y hxy
  by_cases hx : x ≤ 1 / 2
  · rw [psi_eq_zero hx]
    exact psi_nonneg y
  · have hx' : 0 < 2 * x - 1 := by linarith
    have hy' : 0 < 2 * y - 1 := by linarith
    rw [psi_eq_exp (lt_of_not_ge hx), psi_eq_exp (by linarith)]
    apply exp_le_exp.mpr
    have h := (inv_le_inv₀ hy' hx').mpr (show 2 * x - 1 ≤ 2 * y - 1 by linarith)
    have hxinv := inv_nonneg.mpr hx'.le
    have hyinv := inv_nonneg.mpr hy'.le
    nlinarith

/-- The derivative of the scalar switch is nonnegative. -/
theorem deriv_psi_nonneg (y : ℝ) : 0 ≤ deriv psi y := monotone_psi.deriv_nonneg

/-- In the active region the switch is at least its normalized value. -/
theorem one_le_psi {y : ℝ} (hy : 1 ≤ y) : 1 ≤ psi y := by
  simpa using monotone_psi hy

/-- The interaction between two adjacent coordinates. -/
def interaction (a b : ℝ) : ℝ := psi (-a) * phi (-b) - psi a * phi b

/-- An interaction vanishes whenever its preceding coordinate lies in the flat region. -/
theorem interaction_eq_zero {a : ℝ} (ha : |a| ≤ 1 / 2) (b : ℝ) :
    interaction a b = 0 := by
  have h := abs_le.mp ha
  simp [interaction, psi_eq_zero h.2, psi_eq_zero (by linarith : -a ≤ 1 / 2)]

/-- Interactions vanish locally when the preceding coordinate lies strictly in the flat region.
Only continuity of that coordinate is needed. -/
theorem interaction_eventuallyEq_zero {E : Type*} [TopologicalSpace E]
    {a b : E → ℝ} {x : E} (ha : ContinuousAt a x) (hx : |a x| < 1 / 2) :
    (fun y ↦ interaction (a y) (b y)) =ᶠ[𝓝 x] (fun _ ↦ 0) := by
  filter_upwards [ha.abs (gt_mem_nhds hx)] with y hy
  exact interaction_eq_zero hy.le (b y)

/-- Every derivative of a locally flat interaction vanishes, in arbitrary normed spaces. -/
theorem iteratedFDeriv_interaction_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b : E → ℝ} {x : E}
    (ha : ContinuousAt a x) (hx : |a x| < 1 / 2) (q : ℕ) :
    iteratedFDeriv ℝ q (fun y ↦ interaction (a y) (b y)) x = 0 := by
  rw [((interaction_eventuallyEq_zero (b := b) ha hx).iteratedFDeriv ℝ q).eq_of_nhds]
  simp

/-- The two-variable interaction is infinitely smooth. -/
@[fun_prop] theorem contDiff_interaction :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦ interaction z.1 z.2) := by
  unfold interaction
  exact ((contDiff_psi.comp contDiff_fst.neg).mul
    (contDiff_primitive.comp contDiff_snd.neg)).sub
    ((contDiff_psi.comp contDiff_fst).mul (contDiff_primitive.comp contDiff_snd))

/-- An interaction pulled back by two linear coordinates vanishes on any derivative tensor
with a slot in the common kernel of those coordinates. -/
theorem iteratedFDeriv_interaction_apply_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (a b : E →L[ℝ] ℝ) (x : E) {q : ℕ} (v : Fin q → E)
    (j : Fin q) (ha : a (v j) = 0) (hb : b (v j) = 0) :
    iteratedFDeriv ℝ q (fun y ↦ interaction (a y) (b y)) x v = 0 := by
  change iteratedFDeriv ℝ q ((fun z : ℝ × ℝ ↦ interaction z.1 z.2) ∘ (a.prod b)) x v = 0
  rw [(a.prod b).iteratedFDeriv_comp_right contDiff_interaction x (by simp)]
  change (iteratedFDeriv ℝ q (fun z : ℝ × ℝ ↦ interaction z.1 z.2) (a x, b x))
    (fun l ↦ (a (v l), b (v l))) = 0
  exact ContinuousMultilinearMap.map_coord_zero _ j (Prod.ext ha hb)

/-- The explicit chain with `n + 1` coordinates and `n` adjacent-coordinate interactions.
The seed follows equation (10) of Carmon et al., correcting the supplied OCR seed. -/
def chain (n : ℕ) (x : ZeroChains.Space (n + 1)) : ℝ :=
  -psi 1 * phi (x 0) + ∑ i : Fin n,
    (psi (-x i.castSucc) * phi (-x i.succ) - psi (x i.castSucc) * phi (x i.succ))

/-- The explicit chain evaluates to the seed and its adjacent-coordinate sum. -/
theorem chain_apply (n : ℕ) (x : ZeroChains.Space (n + 1)) :
    chain n x = -phi (x 0) + ∑ i : Fin n,
      (psi (-x i.castSucc) * phi (-x i.succ) - psi (x i.castSucc) * phi (x i.succ)) := by
  simp [chain]

/-- Every finite-dimensional explicit chain is infinitely smooth. -/
@[fun_prop] theorem contDiff_chain (n : ℕ) : ContDiff ℝ ∞ (chain n) := by
  unfold chain
  apply ContDiff.add
  · apply ContDiff.mul contDiff_const
    exact contDiff_primitive.comp (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (n + 1)) 0).contDiff
  · apply ContDiff.sum
    intro i _
    apply ContDiff.sub
    · exact (contDiff_psi.comp (EuclideanSpace.proj (𝕜 := ℝ) i.castSucc).contDiff.neg).mul
        (contDiff_primitive.comp (EuclideanSpace.proj (𝕜 := ℝ) i.succ).contDiff.neg)
    · exact (contDiff_psi.comp (EuclideanSpace.proj (𝕜 := ℝ) i.castSucc).contDiff).mul
        (contDiff_primitive.comp (EuclideanSpace.proj (𝕜 := ℝ) i.succ).contDiff)

/-- At the origin every interaction vanishes; only the Gaussian seed remains. -/
theorem chain_zero (n : ℕ) : chain n 0 = -phi 0 := by
  simp [chain, psi_eq_zero (show (0 : ℝ) ≤ 1 / 2 by norm_num)]

/-- Every positive-order oracle sees at most the next coordinate of the explicit chain. -/
theorem isZeroChain (n p : ℕ) : ZeroChains.IsZeroChain p (chain n) := by
  rw [ZeroChains.isZeroChain_iff]
  refine ⟨contDiff_chain n |>.of_le (by simp), ?_⟩
  rintro k x hx q _ _ v ⟨a, ha⟩
  let w : Fin q → ZeroChains.Space (n + 1) :=
    fun j ↦ EuclideanSpace.single (v j) 1
  have hseed : iteratedFDeriv ℝ q (fun y : ZeroChains.Space (n + 1) ↦ -phi (y 0)) x w = 0 := by
    let L := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (n + 1)) 0
    change iteratedFDeriv ℝ q ((fun t : ℝ ↦ -phi t) ∘ L) x w = 0
    rw [L.iteratedFDeriv_comp_right contDiff_primitive.neg x (by simp)]
    change (iteratedFDeriv ℝ q (fun t : ℝ ↦ -phi t) (L x)) (fun j ↦ L (w j)) = 0
    apply ContinuousMultilinearMap.map_coord_zero _ a
    have hne : (0 : Fin (n + 1)) ≠ v a := by
      intro h
      rw [← h] at ha
      simp at ha
    simp [L, w, hne]
  have hterm : ∀ i : Fin n,
      iteratedFDeriv ℝ q (fun y : ZeroChains.Space (n + 1) ↦
        interaction (y i.castSucc) (y i.succ)) x w = 0 := by
    intro i
    by_cases hi : k ≤ i.val
    · have hz : x i.castSucc = 0 := hx i.castSucc hi
      rw [iteratedFDeriv_interaction_eq_zero
        (a := fun y : ZeroChains.Space (n + 1) ↦ y i.castSucc)
        (b := fun y : ZeroChains.Space (n + 1) ↦ y i.succ) (x := x)
        (EuclideanSpace.proj (𝕜 := ℝ) i.castSucc).continuous.continuousAt
        (by rw [hz]; norm_num) q]
      simp
    · apply iteratedFDeriv_interaction_apply_eq_zero
        (EuclideanSpace.proj (𝕜 := ℝ) i.castSucc)
        (EuclideanSpace.proj (𝕜 := ℝ) i.succ) x w a
      · have hne : i.castSucc ≠ v a := by
          intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_castSucc] at hv
          omega
        simp [w, hne]
      · have hne : i.succ ≠ v a := by
          intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_succ] at hv
          omega
        simp [w, hne]
  have hs : ContDiff ℝ (q : ℕ) (fun y : ZeroChains.Space (n + 1) ↦ -phi (y 0)) :=
    (contDiff_primitive.comp
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (n + 1)) 0).contDiff).neg.of_le (by simp)
  have ht : ∀ i : Fin n, ContDiff ℝ (q : ℕ)
      (fun y : ZeroChains.Space (n + 1) ↦ interaction (y i.castSucc) (y i.succ)) := by
    intro i
    exact (contDiff_interaction.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) i.castSucc).prod
        (EuclideanSpace.proj (𝕜 := ℝ) i.succ)).contDiff).of_le (by simp)
  have heq : chain n = (fun y ↦ -phi (y 0)) +
      (fun y ↦ ∑ i : Fin n, interaction (y i.castSucc) (y i.succ)) := by
    funext y
    simp [chain, interaction]
  unfold ZeroChains.mixedPartial
  change iteratedFDeriv ℝ q (chain n) x w = 0
  rw [heq, iteratedFDeriv_add_apply hs.contDiffAt
    ((ContDiff.sum fun i _ ↦ ht i).contDiffAt)]
  simp only [add_apply]
  rw [hseed]
  have hh := iteratedFDeriv_fun_sum_apply (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) ↦
    (ht i).contDiffAt) (x := x)
  rw [hh]
  simp [hterm]

/-- The product of the two source scalar amplitude bounds is less than twelve. -/
theorem scalar_amplitude_lt_twelve :
    exp 1 * (exp (1 / 2 : ℝ) * Real.sqrt (2 * Real.pi)) < 12 := by
  have he : exp 1 < (11 / 4 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have he3 : (exp 1) ^ 3 < (11 / 4 : ℝ) ^ 3 := by gcongr
  have hexp : (exp 1 * exp (1 / 2 : ℝ)) ^ 2 = (exp 1) ^ 3 := by
    rw [← exp_add, ← exp_nat_mul, ← exp_nat_mul]
    congr 1
    norm_num
  have hm : (exp 1 * (exp (1 / 2 : ℝ) * Real.sqrt (2 * Real.pi))) ^ 2 < (12 : ℝ) ^ 2 := by
    rw [← mul_assoc, mul_pow, hexp, Real.sq_sqrt (by positivity)]
    calc
      exp 1 ^ 3 * (2 * Real.pi) < (11 / 4 : ℝ) ^ 3 * (2 * 3.15) := by
        gcongr
        exact Real.pi_lt_d2
      _ < (12 : ℝ) ^ 2 := by norm_num
  nlinarith [mul_nonneg (exp_pos (1 : ℝ)).le
    (mul_nonneg (exp_pos (1 / 2 : ℝ)).le (Real.sqrt_nonneg (2 * Real.pi)))]

/-- Every product appearing as a negative interaction is bounded by twelve. -/
theorem psi_mul_phi_le_twelve (a b : ℝ) : psi a * phi b ≤ 12 := by
  apply le_trans (mul_le_mul (psi_le_exp_one a) (primitive_le b)
    (primitive_pos b).le (exp_pos 1).le)
  exact scalar_amplitude_lt_twelve.le

/-- Each adjacent-coordinate interaction is bounded below by negative twelve. -/
theorem interaction_lower_bound (a b : ℝ) : -12 ≤ interaction a b := by
  have hn := mul_nonneg (psi_nonneg (-a)) (primitive_pos (-b)).le
  have hb := psi_mul_phi_le_twelve a b
  unfold interaction
  linarith

/-- The entire chain is bounded below by twelve times its coordinate dimension. -/
theorem chain_lower_bound (n : ℕ) (x : ZeroChains.Space (n + 1)) :
    -12 * (n + 1 : ℝ) ≤ chain n x := by
  have hseed : -12 ≤ -phi (x 0) := by
    have h := psi_mul_phi_le_twelve 1 (x 0)
    simp only [psi_one, one_mul] at h
    linarith
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (fun i _ ↦ interaction_lower_bound (x i.castSucc) (x i.succ))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  rw [chain_apply]
  change -12 * (n + 1 : ℝ) ≤ -phi (x 0) + ∑ i : Fin n,
    interaction (x i.castSucc) (x i.succ)
  linarith

/-- The explicit chain has a genuine finite lower bound on its whole range. -/
theorem bddBelow_chain (n : ℕ) : BddBelow (Set.range (chain n)) := by
  refine ⟨-12 * (n + 1 : ℝ), ?_⟩
  rintro _ ⟨x, rfl⟩
  exact chain_lower_bound n x

/-- The gap from the origin to the actual infimum is at most twelve times the dimension. -/
theorem chain_initial_gap (n : ℕ) :
    chain n 0 - sInf (Set.range (chain n)) ≤ 12 * (n + 1 : ℝ) := by
  have hi : -12 * (n + 1 : ℝ) ≤ sInf (Set.range (chain n)) :=
    le_csInf (Set.range_nonempty _) (by rintro _ ⟨x, rfl⟩; exact chain_lower_bound n x)
  rw [chain_zero]
  have hp := primitive_pos 0
  linarith

end Optimization.HardZeroChain
