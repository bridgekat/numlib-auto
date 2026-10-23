import Numlib.Analysis.Calculus.TaylorModel.Derivative
import Numlib.Analysis.Calculus.TaylorModel.Holder
import Mathlib.Tactic

/-!
# Derivatives and sharp derivative remainders of finite Taylor polynomials

The finite `C^p` Schwarz theorem identifies the derivative of a diagonal tensor
polynomial with the Taylor polynomial of the actual derivative. Iterating through
the canonical curry isometries gives all derivative orders. The same isometries
preserve differences of derivative tensors, so the sharp vector-valued value
remainder applies to each genuine derivative-valued map. No derivative identity
or remainder estimate is assumed.
-/
open Set Function
open scoped BigOperators
namespace TaylorModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Differentiate a diagonal derivative tensor using finite-order symmetry. -/
theorem hasFDerivAt_diagonal_iteratedFDeriv {f : E → F} {p n : ℕ} {x : E}
    (hf : ContDiffAt ℝ p f x) (hn : n + 1 ≤ p) (s : E) :
    HasFDerivAt (fun y : E => iteratedFDeriv ℝ (n + 1) f x (fun _ => y))
      ((n + 1 : ℕ) • iteratedFDeriv ℝ n (fderiv ℝ f) x (fun _ => s)) s := by
  let A := iteratedFDeriv ℝ (n + 1) f x
  let J : E →L[ℝ] (Fin (n + 1) → E) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ E
  have hd := (A.hasFDerivAt (fun _ => s)).comp s J.hasFDerivAt
  convert hd using 1
  · rfl
  ext v
  change (n + 1 : ℕ) • (iteratedFDeriv ℝ n (fderiv ℝ f) x (fun _ => s)) v =
    (A.linearDeriv (fun _ => s)) (fun _ => v)
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  have hterm (i : Fin (n + 1)) : A (Function.update (fun _ => s) i v) =
      A (Function.update (fun _ => s) (Fin.last n) v) := by
    have hsym := iteratedFDeriv_comp_perm hf hn
      (Function.update (fun _ => s) (Fin.last n) v) (Equiv.swap i (Fin.last n))
    rw [Function.update_comp_equiv] at hsym
    simpa [A, Function.comp_def] using hsym
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [iteratedFDeriv_succ_apply_right]
  simp only [Function.update_self, Fin.init_update_last]
  rfl

/-- Separate the constant term from a positive-degree Taylor polynomial. -/
theorem eval_eq_add_sum_succ (f : E → F) (p : ℕ) (x s : E) :
    eval f (p + 1) x s = f x + ∑ i ∈ Finset.range (p + 1),
      (((i + 1).factorial : ℝ)⁻¹) • iteratedFDeriv ℝ (i + 1) f x (fun _ => s) := by
  rw [eval_eq_sum, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, iteratedFDeriv_zero_apply, one_smul]
  rw [add_comm]

/-- The derivative of the actual Taylor polynomial is the Taylor polynomial of
the actual derivative; only the corresponding finite regularity at the center is used. -/
theorem hasFDerivAt_eval_succ {f : E → F} {p : ℕ} {x : E}
    (hf : ContDiffAt ℝ (p + 1 : ℕ) f x) (s : E) :
    HasFDerivAt (eval f (p + 1) x) (eval (fderiv ℝ f) p x s) s := by
  have hterms : ∀ i ∈ Finset.range (p + 1),
      HasFDerivAt (fun y : E => (((i + 1).factorial : ℝ)⁻¹) •
        iteratedFDeriv ℝ (i + 1) f x (fun _ => y))
        (((i.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ i (fderiv ℝ f) x (fun _ => s)) s := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hd := (hasFDerivAt_diagonal_iteratedFDeriv hf
      (by omega : i + 1 ≤ p + 1) s).const_smul (((i + 1).factorial : ℝ)⁻¹)
    convert hd using 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  have hsum := (HasFDerivAt.fun_sum hterms).const_add (f x)
  have heq : (fun y => f x + ∑ i ∈ Finset.range (p + 1),
      (((i + 1).factorial : ℝ)⁻¹) • iteratedFDeriv ℝ (i + 1) f x (fun _ => y)) =
      eval f (p + 1) x := by
    funext y
    exact (eval_eq_add_sum_succ f p x y).symm
  rw [heq] at hsum
  simpa only [eval_eq_sum] using hsum

/-- Function-level first derivative identity for finite Taylor polynomials. -/
theorem fderiv_eval_succ {f : E → F} {p : ℕ} {x : E}
    (hf : ContDiffAt ℝ (p + 1 : ℕ) f x) :
    fderiv ℝ (eval f (p + 1) x) = eval (fderiv ℝ f) p x := by
  funext s
  exact (hasFDerivAt_eval_succ hf s).fderiv

/-- The order-`j` derivative of the degree-`j+k` Taylor polynomial is the
degree-`k` Taylor polynomial of the order-`j` derivative. -/
theorem iteratedFDeriv_eval_add {j k : ℕ} {f : E → F} {x : E}
    (hf : ContDiffAt ℝ (j + k : ℕ) f x) (s : E) :
    iteratedFDeriv ℝ j (eval f (j + k) x) s = eval (iteratedFDeriv ℝ j f) k x s := by
  induction j generalizing k s with
  | zero =>
    simp only [Nat.zero_add, iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    simpa using (map_eval (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap hf s).symm
  | succ j ih =>
    have hf' : ContDiffAt ℝ (k + 1 : ℕ) (iteratedFDeriv ℝ j f) x :=
      hf.iteratedFDeriv_right (by exact_mod_cast (show k + 1 + j ≤ j + 1 + k by omega))
    have heq : iteratedFDeriv ℝ j (eval f (j + 1 + k) x) =
        eval (iteratedFDeriv ℝ j f) (k + 1) x := by
      funext y
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf) y
    rw [iteratedFDeriv_succ_eq_comp_left]
    simp only [Function.comp_apply]
    rw [heq, fderiv_eval_succ hf']
    rw [iteratedFDeriv_succ_eq_comp_left]
    exact (map_eval (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).symm.toLinearIsometry.toContinuousLinearMap
      (hf'.fderiv_right (m := k) (by simp)) s).symm

/-- A fixed isometric equivalence preserves differences of all derivative tensors.
Equivalences also preserve nondifferentiability, so no regularity hypothesis is needed. -/
theorem norm_iteratedFDeriv_sub_comp_isometryEquiv
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F ≃ₗᵢ[ℝ] G) (f : E → F) (q : ℕ) (x y : E) :
    ‖iteratedFDeriv ℝ q (L ∘ f) x - iteratedFDeriv ℝ q (L ∘ f) y‖ =
      ‖iteratedFDeriv ℝ q f x - iteratedFDeriv ℝ q f y‖ := by
  change ‖iteratedFDeriv ℝ q (L.toContinuousLinearEquiv ∘ f) x -
    iteratedFDeriv ℝ q (L.toContinuousLinearEquiv ∘ f) y‖ = _
  rw [L.toContinuousLinearEquiv.iteratedFDeriv_comp_left,
    L.toContinuousLinearEquiv.iteratedFDeriv_comp_left]
  have heq : (L.toContinuousLinearEquiv.toContinuousLinearMap).compContinuousMultilinearMap
      (iteratedFDeriv ℝ q f x) - (L.toContinuousLinearEquiv.toContinuousLinearMap).compContinuousMultilinearMap
      (iteratedFDeriv ℝ q f y) = L.toLinearIsometry.toContinuousLinearMap.compContinuousMultilinearMap
      (iteratedFDeriv ℝ q f x - iteratedFDeriv ℝ q f y) := by
    ext v
    simp
  rw [heq]
  exact L.toLinearIsometry.norm_compContinuousMultilinearMap _

/-- The right curry isometry preserves differences of iterated derivatives of `fderiv`. -/
theorem norm_iteratedFDeriv_fderiv_sub (f : E → F) (q : ℕ) (x y : E) :
    ‖iteratedFDeriv ℝ q (fderiv ℝ f) x - iteratedFDeriv ℝ q (fderiv ℝ f) y‖ =
      ‖iteratedFDeriv ℝ (q + 1) f x - iteratedFDeriv ℝ (q + 1) f y‖ := by
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp_apply]
  change ‖_‖ = ‖(continuousMultilinearCurryRightEquiv' ℝ q E F).symm.toLinearEquiv _ -
    (continuousMultilinearCurryRightEquiv' ℝ q E F).symm.toLinearEquiv _‖
  rw [← map_sub]
  exact ((continuousMultilinearCurryRightEquiv' ℝ q E F).symm.norm_map _).symm

/-- Repeated curry isometries identify the norm of differences of the genuine
derivatives of a derivative-valued map with that of the total-order derivative. -/
theorem norm_iteratedFDeriv_iteratedFDeriv_sub (f : E → F) (q j : ℕ) (x y : E) :
    ‖iteratedFDeriv ℝ q (iteratedFDeriv ℝ j f) x -
      iteratedFDeriv ℝ q (iteratedFDeriv ℝ j f) y‖ =
      ‖iteratedFDeriv ℝ (q + j) f x - iteratedFDeriv ℝ (q + j) f y‖ := by
  induction j generalizing q with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp, norm_iteratedFDeriv_sub_comp_isometryEquiv]
    simp only [Nat.add_zero]
  | succ j ih =>
    rw [show iteratedFDeriv ℝ (j + 1) f =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).symm ∘
        fderiv ℝ (iteratedFDeriv ℝ j f) from iteratedFDeriv_succ_eq_comp_left]
    have hnorm := norm_iteratedFDeriv_sub_comp_isometryEquiv
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).symm
      (fderiv ℝ (iteratedFDeriv ℝ j f)) q x y
    rw [hnorm, norm_iteratedFDeriv_fderiv_sub, ih]
    rw [show q + 1 + j = q + (j + 1) by omega]
/-- The exact all-order derivative identity, with the total degree as parameter. -/
theorem iteratedFDeriv_eval {p j : ℕ} {f : E → F} {x : E}
    (hf : ContDiffAt ℝ p f x) (hj : j ≤ p) (s : E) :
    iteratedFDeriv ℝ j (eval f p x) s = eval (iteratedFDeriv ℝ j f) (p - j) x s := by
  have heq : j + (p - j) = p := by omega
  have h := iteratedFDeriv_eval_add (j := j) (k := p - j) (by rwa [heq]) s
  simpa only [heq] using h

/-- A degree-zero Taylor polynomial is constant in its increment. -/
@[simp] theorem eval_degree_zero (f : E → F) (x s : E) : eval f 0 x s = f x := by
  simp [eval_eq_sum]

/-- Sharp Hölder error bound for every derivative of the actual Taylor polynomial.
The top-order case is the Hölder assumption; lower orders use the vector-valued
Taylor remainder for the actual derivative-valued function. -/
theorem norm_iteratedFDeriv_sub_eval_le_holder {f : E → F} {p j : ℕ}
    {C D : Set E} (hD : IsOpen D) (hCD : C ⊆ D) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p f D) {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β)
    (hholder : ∀ u ∈ C, ∀ v ∈ C,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ H * ‖u - v‖ ^ β)
    (hj : j ≤ p) {x s : E} (hx : x ∈ C) (hxs : x + s ∈ C) :
    ‖iteratedFDeriv ℝ j f (x + s) - iteratedFDeriv ℝ j (eval f p x) s‖ ≤
      H / Real.shiftedFactorial (p - j) β * ‖s‖ ^ ((p - j : ℕ) + β) := by
  rw [iteratedFDeriv_eval (hf.contDiffAt (hD.mem_nhds (hCD hx))) hj]
  by_cases heq : j = p
  · subst j
    simpa [eval_degree_zero, Real.shiftedFactorial, norm_sub_rev] using hholder (x + s) hxs x hx
  · obtain ⟨q, hq⟩ : ∃ q, p - j = q + 1 := ⟨p - j - 1, by omega⟩
    have hgj : ContDiffOn ℝ (q + 1) (iteratedFDeriv ℝ j f) D := by
      intro y hy
      exact ((hf.contDiffAt (hD.mem_nhds hy)).iteratedFDeriv_right
        (by exact_mod_cast (show q + 1 + j ≤ p by omega))).contDiffWithinAt
    have hgH : ∀ u ∈ C, ∀ v ∈ C,
        ‖iteratedFDeriv ℝ (q + 1) (iteratedFDeriv ℝ j f) u -
          iteratedFDeriv ℝ (q + 1) (iteratedFDeriv ℝ j f) v‖ ≤ H * ‖u - v‖ ^ β := by
      intro u hu v hv
      rw [norm_iteratedFDeriv_iteratedFDeriv_sub, show q + 1 + j = p by omega]
      exact hholder u hu v hv
    simpa only [hq] using norm_sub_eval_le_holder hD hCD hC hgj hH hβ hgH hx hxs

/-- The all-order derivative remainder bound in the Lipschitz case. -/
theorem norm_iteratedFDeriv_sub_eval_le_lipschitz {f : E → F} {p j : ℕ}
    {C D : Set E} (hD : IsOpen D) (hCD : C ⊆ D) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p f D) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ u ∈ C, ∀ v ∈ C,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (hj : j ≤ p) {x s : E} (hx : x ∈ C) (hxs : x + s ∈ C) :
    ‖iteratedFDeriv ℝ j f (x + s) - iteratedFDeriv ℝ j (eval f p x) s‖ ≤
      L * ‖s‖ ^ (p - j + 1) / (p - j + 1).factorial := by
  have hh : ∀ u ∈ C, ∀ v ∈ C,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖ ^ (1 : ℝ) := by
    simpa only [Real.rpow_one] using hlip
  have hb := norm_iteratedFDeriv_sub_eval_le_holder hD hCD hC hf hL
    (by norm_num : (0 : ℝ) ≤ 1) hh hj hx hxs
  simpa only [Real.shiftedFactorial_one,
    show ((p - j : ℕ) : ℝ) + (1 : ℝ) = ((p - j + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, div_mul_eq_mul_div] using hb

end TaylorModel

namespace TaylorModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- The explicit finite Taylor polynomial derivative formula. All coefficients
are genuine derivative tensors, with the remaining powers of the increment
placed before the differentiation directions. -/
theorem iteratedFDeriv_eval_apply {f : E → F} {p j : ℕ} {x : E}
    (hf : ContDiffAt ℝ p f x) (hj : j ≤ p) (s : E) (v : Fin j → E) :
    iteratedFDeriv ℝ j (eval f p x) s v = ∑ q ∈ Finset.range (p - j + 1),
      ((q.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ (q + j) f x
        (Fin.append (fun _ : Fin q => s) v) := by
  rw [iteratedFDeriv_eval hf hj, eval_eq_sum]
  simp only [sum_apply, smul_apply]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [iteratedFDeriv_iteratedFDeriv]
end TaylorModel
