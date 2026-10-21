import Numlib.Optimization.AdaptiveInverseIteration
import Numlib.Eigen.ShiftedInverseRayleigh

/-!
# Spectral invariants for adaptive inverse iteration

A positive-shift prefix preserves a uniform lower bound on every initially present lowest
spectral coordinate. This supplies a fixed constant in the actual Rayleigh-error estimate,
independent of the number of outer iterations. Eventually constant batch counts have a
finite global bound even when the admissible parameter permits arbitrarily large counts.
-/

noncomputable section
open scoped InnerProductSpace
open Filter
namespace Optimization.AdaptiveInverseIteration

/-- An eventually constant actual batch stream has a finite global bound, including its
early prefix. No finite upper bound in the admissible algorithm parameters is needed. -/
theorem exists_count_bound_of_eventually_constant (c : ℕ → Choice) (nbar : ℕ)
    (hc : ∀ᶠ k in atTop, (c k).count = nbar) :
    ∃ B : ℕ, ∀ k, (c k).count ≤ B := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp hc
  refine ⟨max nbar ((Finset.range K).sup fun k => (c k).count), ?_⟩
  intro k
  by_cases hk : k < K
  · exact (Finset.le_sup (f := fun k => (c k).count)
      (Finset.mem_range.mpr hk)).trans (le_max_right _ _)
  · rw [hK k (Nat.le_of_not_gt hk)]
    exact le_max_left _ _

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)

/-- Every initially present lowest spectral coordinate has a uniform absolute lower bound
along each positive-shift prefix of the actual adaptive iteration. -/
theorem abs_repr_iterate_vector_ge (s : State E) (c : ℕ → Choice)
    (h0 : ‖s.vector‖ = 1) {i : Fin (Module.finrank ℝ E)}
    (hlo : ∀ j, hA.eigenvalues rfl i ≤ hA.eigenvalues rfl j) (k : ℕ)
    (hshift : ∀ j < k, 0 < (iterate A s c j).shift + hA.eigenvalues rfl i) :
    |(hA.eigenvectorBasis rfl).repr s.vector i| ≤
      |(hA.eigenvectorBasis rfl).repr (iterate A s c k).vector i| := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    have hprefix := fun j hj => hshift j (Nat.lt_succ_of_lt hj)
    have hn := norm_iterate_vector A s c h0 k (fun j hj =>
      Optimization.SecularResolvent.isUnit_shift hA _ (fun l =>
        ne_of_gt (by linarith [hprefix j hj, hlo l])))
    exact (ih hprefix).trans (by
      simpa only [iterate_succ, update_vector] using
        Krylov.abs_repr_shiftedInverseBatch_ge hA hn (hshift k (Nat.lt_succ_self k))
          hlo (c k).count)

/-- A fixed initial lowest-coordinate constant controls the actual Rayleigh error of the
next batch at every positive-shift prefix. The spectrum may have a repeated minimum. -/
theorem iterate_rayleighError_le (s : State E) (c : ℕ → Choice)
    (h0 : ‖s.vector‖ = 1) {i : Fin (Module.finrank ℝ E)}
    (hi : (hA.eigenvectorBasis rfl).repr s.vector i ≠ 0)
    {d L : ℝ} (hd : 0 < d) (hL : 0 ≤ L)
    (hlo : ∀ j, hA.eigenvalues rfl i ≤ hA.eigenvalues rfl j)
    (hgap : ∀ j, hA.eigenvalues rfl j ≠ hA.eigenvalues rfl i →
      d ≤ hA.eigenvalues rfl j - hA.eigenvalues rfl i)
    (hwidth : ∀ j, hA.eigenvalues rfl j - hA.eigenvalues rfl i ≤ L) (k : ℕ)
    (hshift : ∀ j ≤ k, 0 < (iterate A s c j).shift + hA.eigenvalues rfl i) :
    inner ℝ (iterate A s c (k + 1)).vector (A (iterate A s c (k + 1)).vector) -
      hA.eigenvalues rfl i ≤
        (L / ((hA.eigenvectorBasis rfl).repr s.vector i) ^ 2) *
          (((iterate A s c k).shift + hA.eigenvalues rfl i) / d) ^
            (2 * (c k).count) := by
  have hreg : ∀ j < k, ∀ l,
      (iterate A s c j).shift + hA.eigenvalues rfl l ≠ 0 :=
    fun j hj l => ne_of_gt (by linarith [hshift j hj.le, hlo l])
  have hn := norm_iterate_vector A s c h0 k (fun j hj =>
    Optimization.SecularResolvent.isUnit_shift hA _ (hreg j hj))
  have hik := repr_iterate_vector_ne_zero hA s c hi k hreg
  have habs := abs_repr_iterate_vector_ge hA s c h0 hlo k
    (fun j hj => hshift j hj.le)
  have hsq : ((hA.eigenvectorBasis rfl).repr s.vector i) ^ 2 ≤
      ((hA.eigenvectorBasis rfl).repr (iterate A s c k).vector i) ^ 2 :=
    (sq_le_sq).mpr habs
  have he := Krylov.inner_shiftedInverseBatch_sub_le hA (iterate A s c k).vector
    hik (hshift k le_rfl) hd hL hlo hgap hwidth (c k).count
  rw [hn, one_pow, mul_one] at he
  simp only [iterate_succ, update_vector]
  exact he.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left hL (sq_pos_of_ne_zero hi) hsq)
    (pow_nonneg (div_nonneg (hshift k le_rfl).le hd.le) _))

/-- Eventual constancy of the actual counts supplies a single finite Rayleigh-error
constant for all positive-shift prefixes, even when the allowed batch bound is infinite.
The coefficient and spectral gap are derived from the operator and starting vector, and
the same constant works for every initial shift. -/
theorem exists_uniform_iterate_rayleighError_constant (v : E) (c : ℕ → Choice)
    (h0 : ‖v‖ = 1) {i : Fin (Module.finrank ℝ E)}
    (hi : (hA.eigenvectorBasis rfl).repr v i ≠ 0)
    (hlo : ∀ j, hA.eigenvalues rfl i ≤ hA.eigenvalues rfl j)
    (nbar : ℕ) (hc : ∀ᶠ k in atTop, (c k).count = nbar) :
    ∃ C : ℝ, 0 < C ∧ ∀ t k,
      (∀ j ≤ k, 0 < (iterate A ⟨t, v⟩ c j).shift + hA.eigenvalues rfl i) →
      inner ℝ (iterate A ⟨t, v⟩ c (k + 1)).vector (A (iterate A ⟨t, v⟩ c (k + 1)).vector) -
        hA.eigenvalues rfl i ≤
          C * ((iterate A ⟨t, v⟩ c k).shift + hA.eigenvalues rfl i) ^ (2 * (c k).count) := by
  classical
  obtain ⟨B, hB⟩ := exists_count_bound_of_eventually_constant c nbar hc
  obtain ⟨d, hd, hgap⟩ := Krylov.exists_spectralGap hA hlo
  obtain ⟨L, hL, hwidth⟩ := Krylov.exists_spectralWidth hA (hA.eigenvalues rfl i)
  let b : ℕ → ℝ := fun m =>
    L / ((hA.eigenvectorBasis rfl).repr v i) ^ 2 / d ^ (2 * m)
  have hb : ∀ m, 0 ≤ b m := fun m => by dsimp [b]; positivity
  refine ⟨1 + ∑ m ∈ Finset.range (B + 1), b m, by positivity, ?_⟩
  intro t k hshift
  have he := iterate_rayleighError_le hA ⟨t, v⟩ c h0 hi hd hL hlo hgap hwidth k hshift
  have hbk : b (c k).count ≤ 1 + ∑ m ∈ Finset.range (B + 1), b m := by
    have hs := Finset.single_le_sum (fun m _ => hb m)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (hB k)))
    linarith
  calc
    _ ≤ b (c k).count *
        ((iterate A ⟨t, v⟩ c k).shift + hA.eigenvalues rfl i) ^ (2 * (c k).count) := by
      convert he using 1
      dsimp [b]
      rw [div_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbk (pow_nonneg (hshift k le_rfl).le _)

omit [FiniteDimensional ℝ E] in
/-- The shift error after one actual update separates the Rayleigh error and damping term. -/
theorem update_shift_error (s : State E) (c : Choice) (a : ℝ) :
    (update A s c).shift + a =
      -(inner ℝ (update A s c).vector (A (update A s c).vector) - a) +
        c.damping * ((s.shift + a) +
          (inner ℝ (update A s c).vector (A (update A s c).vector) - a)) ^
            c.exponent := by
  rw [show (s.shift + a) +
      (inner ℝ (update A s c).vector (A (update A s c).vector) - a) =
      s.shift + inner ℝ (update A s c).vector (A (update A s c).vector) by ring]
  rw [update_shift]
  ring

/-- For a constant spectrum, the actual adaptive update has the exact scalar power
recurrence. The new Rayleigh quotient is derived from the inverse batch. -/
theorem update_shift_add_of_spectrum_eq (s : State E) (c : Choice) (a : ℝ)
    (hx : s.vector ≠ 0) (ht : s.shift + a ≠ 0)
    (ha : ∀ j, hA.eigenvalues rfl j = a) :
    (update A s c).shift + a = c.damping * (s.shift + a) ^ c.exponent := by
  have hr := Krylov.inner_shiftedInverseBatch_eq_of_spectrum_eq hA
    s.vector hx s.shift a ht ha c.count
  rw [update_shift]
  simp only [update_vector, hr]
  ring

/-- A scalar smallness test involving the actual spectral error bound guarantees that
the next computed shift stays strictly above the lowest spectral boundary. The positivity
is a conclusion of the inverse/Rayleigh update, not an input invariant. -/
theorem update_shift_pos_of_spectral_smallness (s : State E) (p : Parameters) (c : Choice)
    (hc : c.Legal p) {i : Fin (Module.finrank ℝ E)}
    (hi : (hA.eigenvectorBasis rfl).repr s.vector i ≠ 0)
    {d L : ℝ} (ht : 0 < s.shift + hA.eigenvalues rfl i) (hd : 0 < d) (hL : 0 ≤ L)
    (hlo : ∀ j, hA.eigenvalues rfl i ≤ hA.eigenvalues rfl j)
    (hgap : ∀ j, hA.eigenvalues rfl j ≠ hA.eigenvalues rfl i →
      d ≤ hA.eigenvalues rfl j - hA.eigenvalues rfl i)
    (hwidth : ∀ j, hA.eigenvalues rfl j - hA.eigenvalues rfl i ≤ L)
    (hsmall : (L * ‖s.vector‖ ^ 2 / ((hA.eigenvectorBasis rfl).repr s.vector i) ^ 2) *
      ((s.shift + hA.eigenvalues rfl i) / d) ^ (2 * c.count) <
        c.damping * (s.shift + hA.eigenvalues rfl i) ^ c.exponent) :
    0 < (update A s c).shift + hA.eigenvalues rfl i := by
  have hx : s.vector ≠ 0 := by intro h; apply hi; simp [h]
  have hreg : ∀ j, s.shift + hA.eigenvalues rfl j ≠ 0 :=
    fun j => ne_of_gt (by linarith [hlo j])
  have hr0 := sub_nonneg.mpr (Krylov.inner_shiftedInverseBatch_ge hA
    s.vector hx hreg hlo c.count)
  have hrle := Krylov.inner_shiftedInverseBatch_sub_le hA s.vector
    hi ht hd hL hlo hgap hwidth c.count
  have hdamp : 0 < c.damping := p.damping_pos.trans_le hc.2.2.1.1
  have hexp : 0 ≤ c.exponent := (lt_trans zero_lt_one p.exponent_lt).le.trans hc.2.2.2.1
  have hpow := Real.rpow_le_rpow ht.le
    (show s.shift + hA.eigenvalues rfl i ≤
      (s.shift + hA.eigenvalues rfl i) +
        (inner ℝ (update A s c).vector (A (update A s c).vector) -
          hA.eigenvalues rfl i) by exact le_add_of_nonneg_right hr0) hexp
  have hpay := (hrle.trans_lt hsmall).trans_le (mul_le_mul_of_nonneg_left hpow hdamp.le)
  rw [update_shift_error]
  simpa only [sub_eq_add_neg, add_comm, update_vector] using sub_pos.mpr hpay

end Optimization.AdaptiveInverseIteration
