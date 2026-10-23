import Numlib.Optimization.Quadratic.Derivatives
import Numlib.Optimization.LineSearch.ExactGradient
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Slow exact steepest descent on positive quadratic objectives

An anisotropic positive quadratic has a constant exact global line-search step.
The explicit alternating geometric gradient gives an inverse-square lower bound
while the objective gap and gradient Lipschitz constant stay uniformly bounded.
-/

open Set
open scoped Matrix
noncomputable section
namespace ExactGradientLineSearch.QuadraticSharpness

/-- The genuine Euclidean plane used by the quadratic family. -/
abbrev E := EuclideanSpace ℝ (Fin 2)

/-- Cartesian-coordinate vectors in the Euclidean plane. -/
def vec (a b : ℝ) : E := WithLp.toLp 2 ![a,b]

/-- The small positive eigenvalue of the accuracy-dependent quadratic. -/
def eigenvalue (ε : ℝ) : ℝ := ε^2/16

/-- The genuine bounded diagonal Hessian of the quadratic objective. -/
def H (ε : ℝ) : E →L[ℝ] E :=
  (Matrix.toEuclideanLin
    (![![eigenvalue ε,0],![0,1]] : Matrix (Fin 2) (Fin 2) ℝ)).toContinuousLinearMap

/-- The actual objective is one half of the Hessian quadratic form. -/
def objective (ε : ℝ) : E → ℝ := QuadraticOptimality.model (H ε) 0

/-- The actual Hessian action has the declared two diagonal coordinates. -/
theorem H_apply (ε : ℝ) (x : E) : H ε x = vec (eigenvalue ε*x 0) (x 1) := by
  change WithLp.toLp 2
    ((![![eigenvalue ε,0],![0,1]] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ WithLp.ofLp x) = _
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,vec]

/-- The actual diagonal Hessian is symmetric. -/
theorem H_symmetric (ε : ℝ) : (H ε).toLinearMap.IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe,H_apply]
  simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,vec]
  ring

/-- The genuine objective has its usual scalar quadratic formula. -/
theorem objective_eq (ε : ℝ) (x : E) :
    objective ε x = (eigenvalue ε*(x 0)^2+(x 1)^2)/2 := by
  simp [objective,QuadraticOptimality.model_eq,H_apply,
    EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,vec]
  ring

/-- The true gradient is the actual Hessian action. -/
theorem objective_gradient (ε : ℝ) (x : E) : gradient (objective ε) x = H ε x := by
  simpa [objective] using QuadraticOptimality.gradient_model (H_symmetric ε) (0 : E) x

/-- The genuine family is smooth to every finite order. -/
theorem objective_contDiff (ε : ℝ) (n : ℕ) : ContDiff ℝ n (objective ε) :=
  QuadraticOptimality.contDiff_model _ _ n

/-- Every objective in the family has the common global lower bound zero. -/
theorem objective_nonneg (ε : ℝ) (x : E) : 0 ≤ objective ε x := by
  rw [objective_eq]
  unfold eigenvalue
  positivity

/-- The small eigenvalue is positive and at most one sixteenth for legal accuracies. -/
theorem eigenvalue_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < eigenvalue ε ∧ eigenvalue ε ≤ 1/16 := by
  unfold eigenvalue
  have hs : 0 < ε^2 := sq_pos_of_pos hε
  have hs1 : ε^2 ≤ 1 := pow_le_one₀ hε.le hε1
  constructor <;> linarith

/-- The actual Hessian is a linear contraction, uniformly over all legal accuracies. -/
theorem H_norm_apply_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (x : E) :
    ‖H ε x‖ ≤ ‖x‖ := by
  have hlam := eigenvalue_bounds hε hε1
  have hs : ‖H ε x‖^2 ≤ ‖x‖^2 := by
    rw [H_apply,EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
    simp [vec,Fin.sum_univ_two,Real.norm_eq_abs,sq_abs]
    nlinarith [sq_nonneg (x 0),mul_nonneg (sq_nonneg (x 0))
      (show 0 ≤ 1-(eigenvalue ε)^2 by nlinarith [hlam.1,hlam.2])]
  nlinarith [norm_nonneg (H ε x),norm_nonneg x]

/-- The true gradients have the common global Lipschitz constant one. -/
theorem objective_gradient_lipschitz {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (x y : E) :
    ‖gradient (objective ε) x-gradient (objective ε) y‖ ≤ ‖x-y‖ := by
  rw [objective_gradient,objective_gradient,← map_sub]
  exact H_norm_apply_le hε hε1 _

/-- The constant exact global line-search step. -/
def stepLength (ε : ℝ) : ℝ := 2/(1+eigenvalue ε)

/-- The geometric contraction factor of the actual alternating gradients. -/
def contraction (ε : ℝ) : ℝ := (1-eigenvalue ε)/(1+eigenvalue ε)

/-- The actual prescribed infinite sequence for the positive quadratic. -/
def point (ε : ℝ) (k : ℕ) : E :=
  vec (ε/eigenvalue ε*contraction ε^k) (ε*(-contraction ε)^k)

/-- The genuine gradient along the explicit sequence has alternating equal-magnitude entries. -/
theorem gradient_point {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    gradient (objective ε) (point ε k) =
      vec (ε*contraction ε^k) (ε*(-contraction ε)^k) := by
  rw [objective_gradient,H_apply]
  have hlam : eigenvalue ε ≠ 0 := by unfold eigenvalue; positivity
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [point,vec]
  field_simp

/-- Every explicit point is the actual negative-gradient update by the constant step. -/
theorem point_succ {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    point ε (k+1) = point ε k-stepLength ε • gradient (objective ε) (point ε k) := by
  rw [gradient_point hε]
  have hlam : eigenvalue ε ≠ 0 := by unfold eigenvalue; positivity
  have hd : 1+eigenvalue ε ≠ 0 := by unfold eigenvalue; positivity
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [point,vec,stepLength,contraction,pow_succ]
  all_goals field_simp
  all_goals ring

/-- The exact alternating-coordinate squares agree at every iterate. -/
theorem contraction_neg_square (ε : ℝ) (k : ℕ) :
    ((-contraction ε)^k)^2 = (contraction ε^k)^2 := by
  rw [←pow_mul,Nat.mul_comm k 2,pow_mul,neg_sq,←pow_mul,Nat.mul_comm 2 k,pow_mul]

/-- The actual objective on each full real search line has the explicit positive quadratic form. -/
theorem objective_line_value {ε : ℝ} (hε : 0 < ε) (k : ℕ) (u : ℝ) :
    objective ε (point ε k-u • gradient (objective ε) (point ε k)) =
      (ε^2*(contraction ε^k)^2)/2 *
        ((1-u*eigenvalue ε)^2/eigenvalue ε+(1-u)^2) := by
  rw [objective_eq,gradient_point hε]
  have hlam : eigenvalue ε ≠ 0 := by unfold eigenvalue; positivity
  have hs := contraction_neg_square ε k
  simp only [point,vec,PiLp.sub_apply,PiLp.smul_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,smul_eq_mul]
  rw [show (ε*(-contraction ε)^k-u*(ε*(-contraction ε)^k))^2 =
      ε^2*((-contraction ε)^k)^2*(1-u)^2 by ring,hs]
  field_simp

/-- Completing the square derives global line optimality from the actual objective. -/
theorem objective_line_difference {ε : ℝ} (hε : 0 < ε) (k : ℕ) (u : ℝ) :
    objective ε (point ε k-u • gradient (objective ε) (point ε k)) -
      objective ε (point ε k-stepLength ε • gradient (objective ε) (point ε k)) =
        (ε^2*(contraction ε^k)^2)*(1+eigenvalue ε)/2*(u-stepLength ε)^2 := by
  rw [objective_line_value hε,objective_line_value hε]
  have hlam : eigenvalue ε ≠ 0 := by unfold eigenvalue; positivity
  have hd : 1+eigenvalue ε ≠ 0 := by unfold eigenvalue; positivity
  unfold stepLength
  field_simp
  ring

/-- The selected step genuinely minimizes the objective on the whole real line. -/
theorem line_minimum {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    IsMinOn (fun u : ℝ => objective ε
      (point ε k-u • gradient (objective ε) (point ε k))) univ (stepLength ε) := by
  intro u _
  have he := objective_line_difference hε k u
  change objective ε (point ε k-stepLength ε • gradient (objective ε) (point ε k)) ≤
    objective ε (point ε k-u • gradient (objective ε) (point ε k))
  have hs : 0 ≤ (ε^2*(contraction ε^k)^2)*(1+eigenvalue ε)/2*(u-stepLength ε)^2 := by
    unfold eigenvalue
    positivity
  linarith

/-- The actual contraction is strictly between zero and one for every legal accuracy. -/
theorem contraction_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < contraction ε ∧ contraction ε < 1 := by
  have hlam := eigenvalue_bounds hε hε1
  unfold contraction
  constructor
  · exact div_pos (by linarith) (by linarith)
  · apply (div_lt_one (by linarith : 0 < 1+eigenvalue ε)).mpr
    linarith

/-- The exact gradient norm along the actual sequence has its geometric formula. -/
theorem gradient_norm_sq {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    ‖gradient (objective ε) (point ε k)‖^2 = 2*ε^2*(contraction ε^k)^2 := by
  rw [gradient_point hε,EuclideanSpace.norm_sq_eq]
  simp only [vec,Fin.sum_univ_two,WithLp.ofLp_toLp,Matrix.cons_val_zero,
    Matrix.cons_val_one,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [contraction_neg_square]
  ring

/-- Bernoulli's inequality gives a quantitative lower bound before the source iteration budget. -/
theorem contraction_pow_lower {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {k : ℕ} (hk : k ≤ ⌊(ε ^ 2)⁻¹⌋₊) : (7/8 : ℝ) ≤ contraction ε^k := by
  have hlam := eigenvalue_bounds hε hε1
  have hc := contraction_bounds hε hε1
  have hd : 0 < 1+eigenvalue ε := by linarith
  have hb : 1-2*eigenvalue ε ≤ contraction ε := by
    unfold contraction
    apply (le_div_iff₀ hd).mpr
    nlinarith [sq_nonneg (eigenvalue ε)]
  have hber := one_add_mul_sub_le_pow (by linarith : -1 ≤ contraction ε) k
  have hmul := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α := ℝ) k)
  have hfloor : (k : ℝ) ≤ (ε ^ 2)⁻¹ :=
    (Nat.cast_le.mpr hk).trans (Nat.floor_le (by positivity))
  have hs : 0 < ε^2 := sq_pos_of_pos hε
  have hsq := mul_le_mul_of_nonneg_right hfloor hs.le
  rw [inv_mul_cancel₀ hs.ne'] at hsq
  unfold eigenvalue at hmul
  nlinarith

/-- Every iterate through the source inverse-square budget genuinely fails its gradient test. -/
theorem gradient_large_through_budget {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {k : ℕ} (hk : k ≤ ⌊(ε ^ 2)⁻¹⌋₊) :
    ε < ‖gradient (objective ε) (point ε k)‖ := by
  have hp := contraction_pow_lower hε hε1 hk
  have hs : (7/8 : ℝ)^2 ≤ (contraction ε^k)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg ε)
  have hg := gradient_norm_sq hε k
  nlinarith [sq_pos_of_pos hε,norm_nonneg (gradient (objective ε) (point ε k))]

/-- The actual initial objective gap is uniformly bounded by seventeen halves. -/
theorem objective_initial_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    objective ε (point ε 0) ≤ 17/2 := by
  have he : objective ε (point ε 0) = (16+ε^2)/2 := by
    rw [objective_eq]
    simp only [point,vec,pow_zero,mul_one,Matrix.cons_val_zero,Matrix.cons_val_one]
    unfold eigenvalue
    field_simp
  rw [he]
  have hs : ε^2 ≤ 1 := pow_le_one₀ hε.le hε1
  linarith

/-- Actual finite prefixes obey every primitive global exact-line-search rule. -/
theorem run_of_prefix {ε : ℝ} (hε : 0 < ε) (N : ℕ)
    (hnot : ∀ i < N, ε < ‖gradient (objective ε) (point ε i)‖) :
    ExactGradientLineSearch.Run (objective ε) (gradient (objective ε))
      (point ε) (fun _ => stepLength ε) ε N where
  derivative := fun y => by
    rw [objective_gradient]
    simpa only [objective,zero_add] using
      QuadraticOptimality.hasFDerivAt_model (H_symmetric ε) (0 : E) y
  accuracy_pos := hε
  not_terminated := hnot
  step_nonneg := fun _ _ => by unfold stepLength eigenvalue; positivity
  minimum := fun i _ => by
    intro u _
    exact line_minimum hε i (mem_univ u)
  step := fun i _ => point_succ hε i

/-- The actual quadratic family is globally infinitely continuously differentiable. -/
theorem objective_contDiff_infty (ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (objective ε) :=
  contDiff_infty.mpr (objective_contDiff ε)

/-- The actual line minimizer is unique, so it also satisfies the source's
first-global-minimizer tie convention. -/
theorem line_minimum_strict {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (k : ℕ) {u : ℝ} (hu : u ≠ stepLength ε) :
    objective ε (point ε k-stepLength ε • gradient (objective ε) (point ε k)) <
      objective ε (point ε k-u • gradient (objective ε) (point ε k)) := by
  have hc := (contraction_bounds hε hε1).1
  have hlam := (eigenvalue_bounds hε hε1).1
  have hcoef : 0 < (ε^2*(contraction ε^k)^2)*(1+eigenvalue ε)/2 := by positivity
  have hsq : 0 < (u-stepLength ε)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hu)
  have hp := mul_pos hcoef hsq
  have he := objective_line_difference hε k u
  linarith

/-- The actual global exact-line-search execution has a genuine first stopping
index strictly beyond the floored inverse-square source lower bound. Existence
is obtained from the objective budget and then the least index via Nat.find. -/
theorem exists_first_stop {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ K : ℕ, ‖gradient (objective ε) (point ε K)‖ ≤ ε ∧
      ExactGradientLineSearch.Run (objective ε) (gradient (objective ε))
        (point ε) (fun _ => stepLength ε) ε K ∧ ⌊ε^(-(2 : ℝ))⌋₊ < K := by
  obtain ⟨K,hstop,hrun,_⟩ := ExactGradientLineSearch.exists_termination
    (fun N hnot => run_of_prefix hε N hnot)
    (L := 1) (fun x y => by simpa only [one_mul] using
      objective_gradient_lipschitz hε hε1 x y) zero_lt_one (objective_nonneg ε)
  refine ⟨K,hstop,hrun,?_⟩
  rw [Real.rpow_neg hε.le,Real.rpow_two]
  by_contra hn
  have hk : K ≤ ⌊(ε ^ 2)⁻¹⌋₊ := Nat.le_of_not_gt hn
  exact (not_lt_of_ge hstop) (gradient_large_through_budget hε hε1 hk)

/-- Fixed smoothness, objective-gap and lower-bound constants precede all
accuracies. The actual positive quadratic and its global line minimizers require
at least the source inverse-square number of iterations before genuine termination. -/
theorem exists_uniform_global_witness : ∃ L > 0, ∃ B > 0,
    ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
    ∃ (f : E → ℝ) (x : ℕ → E) (t : ℕ → ℝ) (K : ℕ),
      ContDiff ℝ (⊤ : ℕ∞) f ∧ (∀ z, 0 ≤ f z) ∧ f (x 0) ≤ B ∧
      (∀ y z, ‖gradient f y-gradient f z‖ ≤ L*‖y-z‖) ∧
      ExactGradientLineSearch.Run f (gradient f) x t ε K ∧
      ‖gradient f (x K)‖ ≤ ε ∧ ⌊ε^(-(2 : ℝ))⌋₊ ≤ K ∧
      ε^(-(2 : ℝ)) ≤ (K : ℝ) := by
  refine ⟨1,zero_lt_one,17/2,by norm_num,?_⟩
  intro ε hε hε1
  obtain ⟨K,hstop,hrun,hK⟩ := exists_first_stop hε hε1
  have hnat : (⌊ε^(-(2 : ℝ))⌋₊ : ℝ)+1 ≤ K := by
    exact_mod_cast Nat.succ_le_of_lt hK
  have hreal : ε^(-(2 : ℝ)) < (K : ℝ) :=
    (Nat.lt_floor_add_one _).trans_le hnat
  exact ⟨objective ε,point ε,(fun _ => stepLength ε),K,
    objective_contDiff_infty ε,objective_nonneg ε,objective_initial_le hε hε1,
    (fun y z => by simpa only [one_mul] using objective_gradient_lipschitz hε hε1 y z),
    hrun,hstop,hK.le,hreal.le⟩

end ExactGradientLineSearch.QuadraticSharpness
