import Numlib.Analysis.Calculus.TaylorRemainder
import Numlib.Optimization.TaylorModelRemainder
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Taylor's theorem

The univariate remainders use ordinary derivatives determined by smoothness at every point of
the segment and oriented integrals for arbitrary real increments. The multivariate polynomial
is the canonical Taylor model of the backbone.
-/

namespace CartisGouldToint.AppendixA.Section08

open Set
open scoped Nat NNReal
open Optimization.RegularizedTaylorModel

/-- The book's finite-product factorial `(k + β)!`, with `β! = 1`. -/
def fractionalFactorial (k : ℕ) (β : ℝ) : ℝ :=
  ∏ i ∈ Finset.range k, (((i + 1 : ℕ) : ℝ) + β)

@[simp] theorem fractionalFactorial_zero (β : ℝ) : fractionalFactorial 0 β = 1 := by
  simp [fractionalFactorial]

/-- Increasing the integer part adds its final factor. -/
theorem fractionalFactorial_succ (k : ℕ) (β : ℝ) :
    fractionalFactorial (k + 1) β = fractionalFactorial k β * ((k + 1 : ℕ) + β) := by
  exact Finset.prod_range_succ (fun i : ℕ => ((i + 1 : ℕ) : ℝ) + β) k

@[simp] theorem fractionalFactorial_beta_zero (k : ℕ) :
    fractionalFactorial k 0 = (k ! : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih => rw [fractionalFactorial_succ, ih, Nat.factorial_succ]; push_cast; ring

@[simp] theorem fractionalFactorial_beta_one (k : ℕ) :
    fractionalFactorial k 1 = ((k + 1)! : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [fractionalFactorial_succ, ih, Nat.factorial_succ (k + 1)]
    push_cast
    ring

/-- Equation (A.10), using the canonical iterated-Fréchet-derivative Taylor polynomial. -/
noncomputable def taylorPolynomial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (p : ℕ) (x s : E) : ℝ := taylorModel f p x s

/-- The polynomial in (A.10) is the backbone's canonical model. -/
theorem taylorPolynomial_eq_taylorModel {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) (p : ℕ) (x s : E) :
    taylorPolynomial f p x s = taylorModel f p x s := rfl

/-- Theorem A.8.1, with positive degree written `k + 1` and arbitrary signed increment. -/
theorem theorem_A_8_1 {ψ : ℝ → ℝ} {k : ℕ} {t h : ℝ}
    (hψ : ∀ u ∈ uIcc t (t + h), ContDiffAt ℝ (k + 1) ψ u) :
    ψ (t + h) - taylorPolynomial ψ (k + 1) t h =
      1 / (k ! : ℝ) * ∫ ξ in (0 : ℝ)..h,
        (h - ξ) ^ k * (iteratedDeriv (k + 1) ψ (t + ξ) - iteratedDeriv (k + 1) ψ t) := by
  calc
    _ = ∫ u in t..t+h, (t + h - u) ^ k / (k ! : ℝ) *
        (iteratedDeriv (k + 1) ψ u - iteratedDeriv (k + 1) ψ t) := by
      simpa [taylorPolynomial, taylorModel_real, smul_eq_mul] using
        sub_sum_taylor_eq_integral_deriv_sub hψ
    _ = ∫ ξ in (0 : ℝ)..h, (h - ξ) ^ k / (k ! : ℝ) *
        (iteratedDeriv (k + 1) ψ (t + ξ) - iteratedDeriv (k + 1) ψ t) := by
      have hi := intervalIntegral.integral_comp_add_left
        (fun u => (t + h - u) ^ k / (k ! : ℝ) *
          (iteratedDeriv (k + 1) ψ u - iteratedDeriv (k + 1) ψ t))
        (a := 0) (b := h) t
      simp only [add_zero] at hi
      rw [← hi]
      apply intervalIntegral.integral_congr
      intro ξ _
      ring
    _ = _ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro ξ _
      ring

/-- Theorem A.8.2, including the degenerate increment and either interval orientation. -/
theorem theorem_A_8_2 {ψ : ℝ → ℝ} {k : ℕ} {t h : ℝ}
    (hψ : ∀ u ∈ uIcc t (t + h), ContDiffAt ℝ (k + 1) ψ u) :
    ∃ ξ ∈ uIcc t (t + h),
      ψ (t + h) - taylorPolynomial ψ k t h =
        iteratedDeriv (k + 1) ψ ξ * h ^ (k + 1) / ((k + 1)! : ℝ) := by
  rcases eq_or_ne t (t + h) with heq | hne
  · have hh : h = 0 := by linarith
    subst h
    exact ⟨t, by simp, by simp [taylorPolynomial]⟩
  obtain ⟨ξ, hξ, hT⟩ := exists_taylorWithinEval_add_iteratedDeriv_mul hne
    (fun u hu => (hψ u hu).contDiffWithinAt)
  refine ⟨ξ, Ioo_subset_Icc_self hξ, ?_⟩
  rw [taylorWithinEval_eq_sum_of_contDiffAt hne
    ((hψ t left_mem_uIcc).of_le (by exact_mod_cast Nat.le_succ k))] at hT
  simp only [add_sub_cancel_left] at hT
  simp only [taylorPolynomial, taylorModel_real, smul_eq_mul]
  linarith

/-- The mixed-unit characterization of the tensor norm in the second maximum of (A.7).
This bridge justifies using the standard multilinear operator norm in the following theorem. -/
theorem tensor_operatorNorm_le_iff_unit {n p : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin p => EuclideanSpace ℝ (Fin n)) ℝ)
    {L : ℝ} (hL : 0 ≤ L) :
    ‖A‖ ≤ L ↔ ∀ v : Fin p → EuclideanSpace ℝ (Fin n),
      (∀ i, ‖v i‖ = 1) → |A v| ≤ L := by
  simpa only [Real.norm_eq_abs] using A.opNorm_le_iff_unit_norm hL

/-- Theorem A.8.5, using the mixed-unit induced tensor norm in (A.7). -/
theorem theorem_A_8_5 {n p : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hC : IsOpen C) (hconv : Convex ℝ C) (hf : ContDiffOn ℝ (p + 1) f C) :
    (∀ x ∈ C, ∀ y ∈ C,
      ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ ≤ L * ‖x - y‖) ↔
      ∀ x ∈ C, ‖iteratedFDeriv ℝ (p + 1) f x‖ ≤ L := by
  rw [← lipschitzOnWith_iff_norm_sub_le]
  exact lipschitzOnWith_iteratedFDeriv_iff hC hconv hf


/-- Equation (A.16), including both endpoints of the Hölder exponent interval. -/
theorem fractionalFactorial_beta_kernel {β : ℝ} (hβ : 0 ≤ β) (k : ℕ) :
    (∫ t : ℝ in 0..1, t ^ β * (1 - t) ^ k) =
      (k ! : ℝ) / fractionalFactorial (k + 1) β := by
  exact integral_rpow_mul_one_sub_pow hβ k

/-- Equation (A.11). Terms of degree less than `j` vanish; every surviving term
contracts the original derivative with `j` directions and `k - j` copies of the step. -/
theorem taylorPolynomial_iteratedFDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} {p j : ℕ} {x : E}
    (hf : ContDiffAt ℝ p f x) (s : E) (v : Fin j → E) :
    iteratedFDeriv ℝ j (taylorPolynomial f p x) s v =
      ∑ k ∈ Finset.range (p + 1), if _h : j ≤ k then
        ((k - j)! : ℝ)⁻¹ • iteratedFDeriv ℝ k f x
          (fun l ↦ if h : (l : ℕ) < j then v ⟨l, h⟩ else s)
        else 0 := by
  exact iteratedFDeriv_taylorModel_contraction hf s v

/-- Theorem A.8.3, including the value estimate and every derivative order `1 ≤ j ≤ p`.
The tensor norm is the mixed-unit operator norm characterized above. -/
theorem theorem_A_8_3 {n p : ℕ} {C D : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {H β : ℝ} {x s : EuclideanSpace ℝ (Fin n)}
    (hC : Convex ℝ C) (hD : IsOpen D) (hCD : C ⊆ D)
    (hf : ContDiffOn ℝ p f D) (hβ : β ∈ Icc (0 : ℝ) 1)
    (hH : ∀ u ∈ C, ∀ v ∈ C,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ H * ‖u - v‖ ^ β)
    (hx : x ∈ C) (hxs : x + s ∈ C) :
    |f (x + s) - taylorPolynomial f p x s| ≤
      H / fractionalFactorial p β * ‖s‖ ^ ((p : ℝ) + β) ∧
    ∀ j, 1 ≤ j → j ≤ p →
      ‖iteratedFDeriv ℝ j f (x + s) - iteratedFDeriv ℝ j (taylorPolynomial f p x) s‖ ≤
        H / fractionalFactorial (p - j) β * ‖s‖ ^ (((p - j : ℕ) : ℝ) + β) := by
  have hbound (j : ℕ) (hj : j ≤ p) :
      ‖iteratedFDeriv ℝ j f (x + s) - iteratedFDeriv ℝ j (taylorPolynomial f p x) s‖ ≤
        H / fractionalFactorial (p - j) β * ‖s‖ ^ (((p - j : ℕ) : ℝ) + β) := by
    apply norm_iteratedFDeriv_sub_taylorModel_le_holder hj hβ.1
    · intro t ht
      exact hf.contDiffAt (hD.mem_nhds (hCD (hC.add_smul_mem hx hxs ht)))
    · intro t ht
      simpa using hH (x + t • s) (hC.add_smul_mem hx hxs ht) x hx
  constructor
  · have h := hbound 0 (Nat.zero_le p)
    rw [norm_iteratedFDeriv_zero_sub] at h
    simpa only [Nat.sub_zero, Real.norm_eq_abs] using h
  · intro j _ hj
    exact hbound j hj

/-- Corollary A.8.4: the Lipschitz specialization, including every derivative order. -/
theorem corollary_A_8_4 {n p : ℕ} {C D : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ} {x s : EuclideanSpace ℝ (Fin n)}
    (hC : Convex ℝ C) (hD : IsOpen D) (hCD : C ⊆ D)
    (hf : ContDiffOn ℝ p f D)
    (hL : ∀ u ∈ C, ∀ v ∈ C,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (hx : x ∈ C) (hxs : x + s ∈ C) :
    |f (x + s) - taylorPolynomial f p x s| ≤
      L / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) ∧
    ∀ j, 1 ≤ j → j ≤ p →
      ‖iteratedFDeriv ℝ j f (x + s) - iteratedFDeriv ℝ j (taylorPolynomial f p x) s‖ ≤
        L / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) := by
  simpa only [fractionalFactorial_beta_one, ← Nat.cast_add_one, Real.rpow_natCast] using
    theorem_A_8_3 hC hD hCD hf (by simp : (1 : ℝ) ∈ Icc 0 1)
      (by simpa using hL) hx hxs

end CartisGouldToint.AppendixA.Section08
