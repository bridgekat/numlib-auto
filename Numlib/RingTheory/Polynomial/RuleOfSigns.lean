import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# The parity clause of Descartes' rule of signs

Mathlib's `Mathlib/Algebra/Polynomial/RuleOfSigns.lean` defines `Polynomial.signVariations`, the
number of sign changes in the coefficients (zero coefficients ignored), and proves the bound
`P.roots.countP (0 < ·) ≤ signVariations P` over any linearly ordered commutative ring
(`roots_countP_pos_le_signVariations`). The second half of the rule as textbooks state it
([quarteroni2000numerical] Property 6.5; [isaacson1994analysis] §3.4) — the number of positive
roots differs from the number of sign changes by an *even* number — is absent from Mathlib and is
proved here over `ℝ`.

The combinatorial half is `signVariations_mod_two_eq`: the parity of the number of sign changes is
the parity of the comparison of the leading and trailing coefficients, by walking the nonzero
coefficients from the top with `signVariations_eq_eraseLead_add_ite`. The analytic half is
`sign_leadingCoeff_eq_sign_trailingCoeff_of_forall_pos`: a real polynomial with no positive root
has leading and trailing coefficients of the same sign, since `P.eval` keeps one sign on `(0, ∞)`
(intermediate value theorem), the sign of the leading coefficient for large `x`
(`tendsto_atTop_of_leadingCoeff_nonneg`) and of the trailing coefficient near `0⁺`. Factoring out
the positive roots one by one, each factor `X - η` flips the trailing sign and hence the parity,
which gives `signVariations_mod_two_eq_roots_countP_pos_mod_two` and the clause
`even_signVariations_sub_roots_countP_pos`. Upstreaming candidate (natural home: Mathlib's
`RuleOfSigns.lean`).
-/

open Filter Topology

namespace Polynomial

section Semiring

variable {R : Type*} [Semiring R] [LinearOrder R]

omit [LinearOrder R] in
/-- The trailing coefficient of a monomial is its coefficient. -/
theorem trailingCoeff_monomial (n : ℕ) {a : R} (ha : a ≠ 0) :
    (monomial n a).trailingCoeff = a := by
  rw [trailingCoeff, natTrailingDegree_monomial ha, coeff_monomial]
  simp

omit [LinearOrder R] in
/-- Erasing the leading term of a polynomial with at least two nonzero coefficients does not change
its trailing coefficient. -/
theorem trailingCoeff_eraseLead {P : R[X]} (h : P.eraseLead ≠ 0) :
    P.eraseLead.trailingCoeff = P.trailingCoeff := by
  have hP : P ≠ 0 := fun h0 => h (by simp [h0])
  have hlt : P.natTrailingDegree < P.natDegree := by
    obtain ⟨i, hi⟩ : ∃ i, P.eraseLead.coeff i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact h (Polynomial.ext fun i => by simp [hcon i])
    have hi' : i ≠ P.natDegree := fun heq => hi (by simp [heq])
    rw [eraseLead_coeff_of_ne i hi'] at hi
    exact (natTrailingDegree_le_of_ne_zero hi).trans_lt
      (lt_of_le_of_ne (le_natDegree_of_ne_zero hi) hi')
  have hntd : P.eraseLead.natTrailingDegree = P.natTrailingDegree := by
    refine le_antisymm (natTrailingDegree_le_of_ne_zero ?_) (le_natTrailingDegree h fun m hm => ?_)
    · rw [eraseLead_coeff_of_ne _ hlt.ne]
      exact trailingCoeff_nonzero_iff_nonzero.2 hP
    · rw [eraseLead_coeff_of_ne _ (hm.trans hlt).ne]
      exact coeff_eq_zero_of_lt_natTrailingDegree hm
  rw [trailingCoeff, trailingCoeff, hntd, eraseLead_coeff_of_ne _ hlt.ne]

/-- The parity bookkeeping of a chain of two sign comparisons. -/
private theorem signType_parity (a b c : SignType) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ((if b = c then 0 else 1) + if a = -b then 1 else 0) % 2 = if a = c then 0 else 1 := by
  revert a b c
  decide

/-- **The parity of the number of sign changes** is that of the comparison between the leading and
the trailing coefficient: for `P ≠ 0`, `signVariations P % 2 = 0` if they have the same sign and
`1` otherwise. Induction through `signVariations_eq_eraseLead_add_ite`, which walks the nonzero
coefficients from the top. -/
theorem signVariations_mod_two_eq {P : R[X]} (hP : P ≠ 0) :
    signVariations P % 2 =
      if SignType.sign P.leadingCoeff = SignType.sign P.trailingCoeff then 0 else 1 := by
  generalize hd : P.natDegree = d
  induction d using Nat.strong_induction_on generalizing P with
  | _ d ih =>
  by_cases hE : P.eraseLead = 0
  · -- a monomial: no sign change, and the two coefficients coincide
    have hmono : P = monomial P.natDegree P.leadingCoeff := by
      conv_lhs => rw [← P.eraseLead_add_monomial_natDegree_leadingCoeff]
      rw [hE, zero_add]
    have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hP
    rw [hmono, signVariations_monomial, leadingCoeff_monomial, trailingCoeff_monomial _ hlc]
    simp
  · have hlt : P.eraseLead.natDegree < d := by
      rcases eraseLead_natDegree_lt_or_eraseLead_eq_zero P with h | h
      · rwa [hd] at h
      · exact absurd h hE
    have ihE := ih _ hlt hE rfl
    rw [signVariations_eq_eraseLead_add_ite hP, Nat.add_mod, ihE, trailingCoeff_eraseLead hE]
    have h1 : (if SignType.sign P.leadingCoeff = -SignType.sign P.eraseLead.leadingCoeff then 1
        else 0) % 2 = if SignType.sign P.leadingCoeff = -SignType.sign P.eraseLead.leadingCoeff
        then 1 else 0 := by
      split_ifs <;> norm_num
    rw [h1]
    exact signType_parity _ _ _ (sign_ne_zero.2 (leadingCoeff_ne_zero.2 hP))
      (sign_ne_zero.2 (leadingCoeff_ne_zero.2 hE))
      (sign_ne_zero.2 (trailingCoeff_nonzero_iff_nonzero.2 hP))

end Semiring

section Real

variable {P : ℝ[X]}

/-- Two nonzero reals have the same sign iff their product is positive. -/
private theorem sign_eq_sign_iff_of_ne_zero {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) :
    SignType.sign u = SignType.sign v ↔ 0 < u * v := by
  rcases lt_or_gt_of_ne hu with hu' | hu' <;> rcases lt_or_gt_of_ne hv with hv' | hv'
  · simp [sign_neg hu', sign_neg hv', mul_pos_of_neg_of_neg hu' hv']
  · simp [sign_neg hu', sign_pos hv', (mul_neg_of_neg_of_pos hu' hv').not_gt]
  · simp [sign_pos hu', sign_neg hv', (mul_neg_of_pos_of_neg hu' hv').not_gt]
  · simp [sign_pos hu', sign_pos hv', mul_pos hu' hv']

/-- **A real polynomial with no positive root has leading and trailing coefficients of the same
sign.** The values `P.eval x`, `x > 0`, have a constant sign by the intermediate value theorem; it
is the sign of the leading coefficient for large `x` and, writing `P = X ^ t Q` with
`Q(0) = P.trailingCoeff`, the sign of the trailing coefficient for small `x > 0`. -/
theorem sign_leadingCoeff_eq_sign_trailingCoeff_of_forall_pos (hP : P ≠ 0)
    (h : ∀ x, 0 < x → P.eval x ≠ 0) :
    SignType.sign P.leadingCoeff = SignType.sign P.trailingCoeff := by
  -- the sign of `P` near `0⁺` is that of the trailing coefficient
  obtain ⟨Q, hQ⟩ : X ^ P.natTrailingDegree ∣ P :=
    X_pow_dvd_iff.2 fun d hd => coeff_eq_zero_of_lt_natTrailingDegree hd
  have hQ0 : Q.eval 0 = P.trailingCoeff := by
    have := coeff_X_pow_mul Q P.natTrailingDegree 0
    rw [zero_add, ← hQ] at this
    rw [← coeff_zero_eq_eval_zero, ← this]
    rfl
  have htc : P.trailingCoeff ≠ 0 := trailingCoeff_nonzero_iff_nonzero.2 hP
  have hnear : ∀ᶠ x in 𝓝 (0 : ℝ), 0 < Q.eval x * P.trailingCoeff := by
    have hc : ContinuousAt (fun x => Q.eval x * P.trailingCoeff) 0 :=
      (Q.continuous.mul continuous_const).continuousAt
    refine hc.eventually (lt_mem_nhds ?_)
    change (0 : ℝ) < Q.eval 0 * P.trailingCoeff
    rw [hQ0]
    exact mul_self_pos.2 htc
  obtain ⟨x₀, hx₀, hx₀pos⟩ := ((hnear.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)))).exists
  have hPx : P.eval x₀ = x₀ ^ P.natTrailingDegree * Q.eval x₀ := by
    conv_lhs => rw [hQ]
    simp
  have hsign₀ : SignType.sign (P.eval x₀) = SignType.sign P.trailingCoeff := by
    rw [sign_eq_sign_iff_of_ne_zero (h x₀ hx₀pos) htc, hPx, mul_assoc]
    exact mul_pos (pow_pos hx₀pos _) hx₀
  -- the sign of `P` for large `x` is that of the leading coefficient
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hP
  obtain ⟨x₁, hx₁pos, hx₁⟩ : ∃ x₁, 0 < x₁ ∧ 0 < P.eval x₁ * P.leadingCoeff := by
    rcases eq_or_lt_of_le (zero_le_degree_iff.2 hP) with hdeg | hdeg
    · -- a nonzero constant
      refine ⟨1, one_pos, ?_⟩
      have hc0 : P.coeff 0 ≠ 0 := fun h0 => hP (by rw [eq_C_of_degree_eq_zero hdeg.symm, h0, C_0])
      rw [eq_C_of_degree_eq_zero hdeg.symm, eval_C, leadingCoeff_C]
      exact mul_self_pos.2 hc0
    · have hev : ∀ᶠ x in atTop, 0 < P.eval x * P.leadingCoeff := by
        rcases lt_or_gt_of_ne hlc with hneg | hpos
        · filter_upwards [(P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hneg.le).eventually
            (eventually_lt_atBot 0)] with x hx
          exact mul_pos_of_neg_of_neg hx hneg
        · filter_upwards [(P.tendsto_atTop_of_leadingCoeff_nonneg hdeg hpos.le).eventually
            (eventually_gt_atTop 0)] with x hx
          exact mul_pos hx hpos
      obtain ⟨x₁, hx₁, hx₁'⟩ := ((eventually_gt_atTop 0).and hev).exists
      exact ⟨x₁, hx₁, hx₁'⟩
  have hsign₁ : SignType.sign (P.eval x₁) = SignType.sign P.leadingCoeff :=
    (sign_eq_sign_iff_of_ne_zero (h x₁ hx₁pos) hlc).2 hx₁
  -- no sign change between `x₀` and `x₁` without a root
  have hsame : SignType.sign (P.eval x₀) = SignType.sign (P.eval x₁) := by
    rw [sign_eq_sign_iff_of_ne_zero (h x₀ hx₀pos) (h x₁ hx₁pos)]
    by_contra hcon
    have hneg : P.eval x₀ * P.eval x₁ < 0 :=
      lt_of_le_of_ne (not_lt.1 hcon) (mul_ne_zero (h x₀ hx₀pos) (h x₁ hx₁pos))
    have hmem : (0 : ℝ) ∈ Set.uIcc (P.eval x₀) (P.eval x₁) := by
      rcases mul_neg_iff.1 hneg with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Set.mem_uIcc.2 (Or.inr ⟨h2.le, h1.le⟩)
      · exact Set.mem_uIcc.2 (Or.inl ⟨h1.le, h2.le⟩)
    obtain ⟨y, hy, hy0⟩ := intermediate_value_uIcc (f := fun x => P.eval x)
      P.continuous.continuousOn hmem
    have hypos : 0 < y := by
      rcases Set.mem_uIcc.1 hy with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hx₀pos.trans_le h1
      · exact hx₁pos.trans_le h1
    exact h y hypos hy0
  rw [← hsign₁, ← hsame, hsign₀]

/-- Multiplying by `X - η` with `η > 0` flips the sign of the trailing coefficient. -/
theorem sign_trailingCoeff_X_sub_C_mul {η : ℝ} (hη : 0 < η) (Q : ℝ[X]) :
    SignType.sign ((X - C η) * Q).trailingCoeff = -SignType.sign Q.trailingCoeff := by
  have h1 : (X - C η).trailingCoeff = -η := by
    rw [trailingCoeff_eq_coeff_zero (by simp [hη.ne'])]
    simp
  rw [trailingCoeff_mul, h1, sign_mul, Left.sign_neg, sign_pos hη]
  simp

/-- The parity flip of a chain of comparisons against a negated sign. -/
private theorem signType_parity_neg (a c : SignType) (ha : a ≠ 0) (hc : c ≠ 0) :
    (if a = -c then 0 else 1) = ((if a = c then 0 else 1) + 1) % 2 := by
  revert a c
  decide

/-- **The parity clause of Descartes' rule of signs**, in the form
`signVariations P % 2 = P.roots.countP (0 < ·) % 2`: the number of sign changes and the number of
positive roots (with multiplicity) of a nonzero real polynomial have the same parity. Induction on
the number of positive roots, each factor `X - η` flipping the parity
(`sign_trailingCoeff_X_sub_C_mul`), with `sign_leadingCoeff_eq_sign_trailingCoeff_of_forall_pos`
for a polynomial without positive roots. -/
theorem signVariations_mod_two_eq_roots_countP_pos_mod_two (hP : P ≠ 0) :
    signVariations P % 2 = P.roots.countP (0 < ·) % 2 := by
  generalize hn : P.roots.countP (0 < ·) = n
  induction n generalizing P with
  | zero =>
    have hroot : ∀ x, 0 < x → P.eval x ≠ 0 := fun x hx hx0 => by
      have : 0 < P.roots.countP (0 < ·) :=
        Multiset.countP_pos.2 ⟨x, (mem_roots hP).2 hx0, hx⟩
      omega
    rw [signVariations_mod_two_eq hP,
      sign_leadingCoeff_eq_sign_trailingCoeff_of_forall_pos hP hroot]
    simp
  | succ n ih =>
    obtain ⟨η, hη, hηpos⟩ : ∃ x, x ∈ P.roots ∧ 0 < x :=
      Multiset.countP_pos.1 (by rw [hn]; exact Nat.succ_pos n)
    obtain ⟨Q, rfl⟩ := dvd_iff_isRoot.mpr (isRoot_of_mem_roots hη)
    have hQ : Q ≠ 0 := right_ne_zero_of_mul hP
    have hcount : Q.roots.countP (0 < ·) = n := by
      rw [roots_mul hP, roots_X_sub_C, Multiset.singleton_add,
        Multiset.countP_cons_of_pos _ hηpos] at hn
      exact Nat.succ_injective hn
    have ihQ := ih hQ hcount
    rw [signVariations_mod_two_eq hP, signVariations_mod_two_eq hQ] at *
    rw [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul, sign_trailingCoeff_X_sub_C_mul hηpos,
      signType_parity_neg _ _ (sign_ne_zero.2 (leadingCoeff_ne_zero.2 hQ))
        (sign_ne_zero.2 (trailingCoeff_nonzero_iff_nonzero.2 hQ)), ihQ]
    omega

/-- **Descartes' rule of signs, parity clause** ([quarteroni2000numerical] Property 6.5, second
half): for a nonzero real polynomial, `ν - k` is even, where `ν` is the number of sign changes in
the coefficients and `k` the number of positive roots counted with multiplicity (`k ≤ ν` by
Mathlib's `roots_countP_pos_le_signVariations`, so the natural subtraction is the difference). -/
theorem even_signVariations_sub_roots_countP_pos (hP : P ≠ 0) :
    Even (signVariations P - P.roots.countP (0 < ·)) := by
  have h1 := roots_countP_pos_le_signVariations P
  have h2 := signVariations_mod_two_eq_roots_countP_pos_mod_two hP
  rw [Nat.even_iff]
  omega

end Real

end Polynomial
