import Numlib.Analysis.Calculus.TaylorModel.PolynomialDerivative
import Numlib.Analysis.Calculus.TaylorModel.Smooth
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Numlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic
/-!
# Finite Taylor coefficients along polynomial curves

Multilinearity expands an actual finite Taylor model along a polynomial curve
into ordered positive integer compositions. Finite-order chain rules identify
its coefficients with the actual derivatives of the original function along
the curve. Only local finite smoothness is needed for that identity.
-/

open scoped BigOperators
open Polynomial
namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- The degree-q polynomial curve with vector coefficients indexed from one. -/
noncomputable def polynomialCurve (s : ℕ → E) (q : ℕ) (t : ℝ) : E :=
  ∑ i ∈ Finset.Icc 1 q, t ^ i • s i
/-- Ordered k-tuples of positive integers summing to n, represented as a finite set. -/
noncomputable def orderedCompositions (n k : ℕ) : Finset (Fin k → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin k => Finset.Icc 1 n).filter (fun l => ∑ i, l i = n)
/-- Membership gives the exact positivity, degree bounds and total-degree equation. -/
theorem mem_orderedCompositions {n k : ℕ} {l : Fin k → ℕ} :
    l ∈ orderedCompositions n k ↔ (∀ i, 1 ≤ l i ∧ l i ≤ n) ∧ ∑ i, l i = n := by
  classical
  simp [orderedCompositions, Fintype.mem_piFinset]
/-- An ambient degree cap larger than the total degree does not change the tuples. -/
theorem orderedCompositions_filter {q n k : ℕ} (hn : n ≤ q) :
    (Fintype.piFinset fun _ : Fin k => Finset.Icc 1 q).filter (fun l => ∑ i, l i = n) =
      orderedCompositions n k := by
  classical
  ext l
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc,
    mem_orderedCompositions]
  constructor
  · rintro ⟨hl, hs⟩
    refine ⟨fun i => ⟨(hl i).1, ?_⟩, hs⟩
    calc l i ≤ ∑ a, l a := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      _ = n := hs
  · rintro ⟨hl, hs⟩
    exact ⟨fun i => ⟨(hl i).1, (hl i).2.trans hn⟩, hs⟩
/-- A positive composition cannot have more entries than its total degree. -/
theorem orderedCompositions_eq_empty {n k : ℕ} (hnk : n < k) :
    orderedCompositions n k = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro l hl
  rcases mem_orderedCompositions.mp hl with ⟨hb, hs⟩
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hb i).1)
  have hk : k ≤ n := by simpa [hs] using h
  omega
/-- The scalar polynomial obtained by expanding a multilinear form on a polynomial
curve. -/
noncomputable def tensorCurvePolynomial {k : ℕ} (A : E [×k]→L[ℝ] ℝ)
    (q : ℕ) (s : ℕ → E) : ℝ[X] :=
  ∑ l ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 q),
    C (A (fun i => s (l i))) * X ^ (∑ i, l i)
/-- Evaluating the expanded polynomial recovers the actual multilinear evaluation. -/
theorem tensorCurvePolynomial_eval {k : ℕ} (A : E [×k]→L[ℝ] ℝ)
    (q : ℕ) (s : ℕ → E) (t : ℝ) :
    (tensorCurvePolynomial A q s).eval t = A (fun _ => polynomialCurve s q t) := by
  classical
  rw [tensorCurvePolynomial, Polynomial.eval_finsetSum]
  unfold polynomialCurve
  rw [A.map_sum_finset]
  apply Finset.sum_congr rfl
  intro l _
  rw [A.map_smul_univ]
  simp only [eval_mul, eval_C, eval_pow, eval_X, smul_eq_mul,
    Finset.prod_pow_eq_pow_sum]
  ring
/-- Each coefficient is the sum over the corresponding ordered positive compositions. -/
theorem tensorCurvePolynomial_coeff {k q n : ℕ} (hn : n ≤ q)
    (A : E [×k]→L[ℝ] ℝ) (s : ℕ → E) :
    (tensorCurvePolynomial A q s).coeff n =
      ∑ l ∈ orderedCompositions n k, A (fun i => s (l i)) := by
  classical
  simp only [tensorCurvePolynomial, Polynomial.finsetSum_coeff, coeff_C_mul_X_pow]
  rw [← Finset.sum_filter]
  congr 1
  simpa only [eq_comm] using (orderedCompositions_filter (k := k) hn)
/-- The normalized Taylor coefficient along a polynomial curve, including a zero-order
term. -/
noncomputable def curveCoefficient (f : E → ℝ) (x : E) (s : ℕ → E) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℝ)⁻¹) *
    ∑ l ∈ orderedCompositions n k, iteratedFDeriv ℝ k f x (fun i => s (l i))
/-- The finite scalar polynomial obtained from the actual Taylor model along the curve. -/
noncomputable def curveTaylorPolynomial (f : E → ℝ) (x : E) (s : ℕ → E)
    (q : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (q + 1), C ((k.factorial : ℝ)⁻¹) *
    tensorCurvePolynomial (iteratedFDeriv ℝ k f x) q s
/-- The expanded scalar polynomial equals the actual Taylor model along the curve. -/
theorem curveTaylorPolynomial_eval (f : E → ℝ) (x : E) (s : ℕ → E) (q : ℕ) (t : ℝ) :
    (curveTaylorPolynomial f x s q).eval t = eval f q x (polynomialCurve s q t) := by
  classical
  rw [curveTaylorPolynomial, Polynomial.eval_finsetSum, eval_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [eval_mul, eval_C, tensorCurvePolynomial_eval, smul_eq_mul]
/-- Every coefficient within the Taylor degree is its ordered-composition sum. -/
theorem curveTaylorPolynomial_coeff {q n : ℕ} (hn : n ≤ q)
    (f : E → ℝ) (x : E) (s : ℕ → E) :
    (curveTaylorPolynomial f x s q).coeff n = curveCoefficient f x s n := by
  classical
  simp only [curveTaylorPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    tensorCurvePolynomial_coeff hn, curveCoefficient]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hn))
  intro k _ hk
  have hnk : n < k := by simpa using hk
  rw [orderedCompositions_eq_empty hnk, Finset.sum_empty, mul_zero]
/-- Every polynomial curve defined here starts at zero. -/
theorem polynomialCurve_zero (s : ℕ → E) (q : ℕ) : polynomialCurve s q 0 = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  have hip : i ≠ 0 := by have := (Finset.mem_Icc.mp hi).1; omega
  simp [hip]

/-- A polynomial curve is smooth to every order. -/
theorem polynomialCurve_contDiff (s : ℕ → E) (q : ℕ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (polynomialCurve s q) := by
  unfold polynomialCurve
  fun_prop

/-- Actual derivatives along the curve equal factorial times the ordered-composition
coefficient, under exactly the required local finite smoothness. -/
theorem iteratedDeriv_polynomialCurve {q n : ℕ} (hn : n ≤ q)
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ q f x) (s : ℕ → E) :
    iteratedDeriv n (fun t => f (x + polynomialCurve s q t)) 0 =
      (n.factorial : ℝ) * curveCoefficient f x s n := by
  classical
  let c := polynomialCurve s q
  have hc : ContDiffAt ℝ q c 0 := polynomialCurve_contDiff s q |>.contDiffAt
  have hc0 : c 0 = 0 := polynomialCurve_zero s q
  have hg : ContDiffAt ℝ q (fun y : E => f (x + y)) (c 0) := by
    rw [hc0]
    have hf' : ContDiffAt ℝ q f (x + (0 : E)) := by simpa using hf
    exact hf'.comp 0 (contDiffAt_const.add contDiffAt_id)
  have hT : ContDiffAt ℝ q (eval f q x) (c 0) := (contDiff_eval f q x q).contDiffAt
  have he : iteratedDeriv n ((fun y : E => f (x + y)) ∘ c) 0 =
      iteratedDeriv n ((eval f q x) ∘ c) 0 := by
    rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition hg hc (by exact_mod_cast hn),
      iteratedDeriv_vcomp_eq_sum_orderedFinpartition hT hc (by exact_mod_cast hn)]
    apply Finset.sum_congr rfl
    intro a _
    rw [hc0, iteratedFDeriv_comp_add_left, add_zero,
      iteratedFDeriv_eval hf (a.length_le.trans hn), eval_zero]
  change iteratedDeriv n ((fun y : E => f (x + y)) ∘ c) 0 = _
  rw [he]
  have heval : (eval f q x) ∘ c = fun t => (curveTaylorPolynomial f x s q).eval t := by
    funext t
    exact (curveTaylorPolynomial_eval f x s q t).symm
  rw [heval, Polynomial.iteratedDeriv_eval]
  dsimp only
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  rw [curveTaylorPolynomial_coeff hn]
/-- A positive total degree cannot have a composition with no entries. -/
theorem orderedCompositions_zero_length {n : ℕ} (hn : 0 < n) :
    orderedCompositions n 0 = ∅ := by
  classical
  ext l
  simp [mem_orderedCompositions, Ne.symm hn.ne']

/-- For positive degree, the coefficient is precisely the sum from tensor order one to
that degree. -/
theorem curveCoefficient_eq_sum_Icc {n : ℕ} (hn : 0 < n)
    (f : E → ℝ) (x : E) (s : ℕ → E) :
    curveCoefficient f x s n =
      ∑ k ∈ Finset.Icc 1 n, ((k.factorial : ℝ)⁻¹) *
        ∑ l ∈ orderedCompositions n k, iteratedFDeriv ℝ k f x (fun i => s (l i)) := by
  classical
  unfold curveCoefficient
  symm
  apply Finset.sum_subset
  · intro k hk
    exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hk).2; omega)
  · intro k hk hkn
    have hk0 : k = 0 := by
      have hkup := Finset.mem_range.mp hk
      simp only [Finset.mem_Icc, not_and_or, not_le] at hkn
      omega
    subst k
    rw [orderedCompositions_zero_length hn, Finset.sum_empty, mul_zero]
end TaylorModel
