import Numlib.Approximation.Quadrature

/-!
# The Gauss quadrature remainder on an unbounded interval

`Quadrature.exists_gauss_error_eq` gives the mean value form of the Gauss quadrature error for a
weight carried by a *compact* interval `[a, b]`: the error is `f^{(2n)}(ξ)/(2n)!` times
`∫ p_n² ∂μ` for some `ξ ∈ [a, b]`. Its proof squeezes the error between the minimum and the maximum
of `f^{(2n)}/(2n)!` on `[a, b]`, which is where compactness enters. The Laguerre weight `e^{-x}` on
`(0, ∞)` and the Hermite weight `e^{-x²}` on `ℝ` are not carried by a compact interval, and their
top derivatives need not be bounded, so that argument does not apply to them.

This file proves the same formula for a weight carried by an arbitrary interval, with no
boundedness assumption on the top derivative. The extremum step is replaced by a strict-positivity
argument: if `f^{(2n)}(ξ)/(2n)!` stayed strictly above the average `c` of the error, the continuous
function `f - H - c p_n²` (`H` the Hermite interpolant with double nodes) would be nonnegative on
the interval and strictly positive off the `n` roots of `p_n`, so its integral against the weight
could not vanish — but it does, by the very definition of `c`. The same argument below `c` gives a
second point, and the intermediate value theorem on the interval joining the two produces `ξ`.

The file also records the half-line forms of `OrthogonalPolynomial.root_family_mem_Ioo`, which
locate the roots of the orthogonal polynomials relative to a one-sided bound on the carrier of the
weight; they are what puts the Gauss–Laguerre nodes in `(0, ∞)`.

## Main results

* `OrthogonalPolynomial.lt_root_family`, `OrthogonalPolynomial.root_family_lt` — a root of
  `family μ n` lies strictly inside any one-sided bound on the carrier of `μ`.
* `Quadrature.exists_gauss_error_eq_of_convex` — the Gauss remainder for a weight carried by a
  convex set.

Reference: [quarteroni2000numerical] (10.41)–(10.42); [kress1998numerical] §9.3.
-/

open MeasureTheory Polynomial

namespace OrthogonalPolynomial

variable {μ : Measure ℝ}

/-- **A root of an orthogonal polynomial is strictly to the right of a left bound of the weight.**
If `μ`-almost every point is at least `a` and `x₀` is a root of `family μ n`, then `a < x₀`.

Write `family μ n = (X - x₀) q` with `q` of degree less than `n`; orthogonality of `family μ n` to
`q` gives `∫ (t - x₀) q(t)² ∂μ = 0`. Were `x₀ ≤ a`, the integrand would be nonnegative
`μ`-almost everywhere, and a nonzero polynomial of constant sign cannot integrate to zero against a
weight.

This is the half-line form of `OrthogonalPolynomial.root_family_mem_Ioo`, needed for the Laguerre
weight, whose carrier `(0, ∞)` is unbounded above.

Reference: [quarteroni2000numerical] §10.2; [kress1998numerical] §9.3. -/
theorem lt_root_family (hw : IsWeight μ) {a : ℝ} (hae : ∀ᵐ t ∂μ, a ≤ t) {n : ℕ} {x₀ : ℝ}
    (hx₀ : (family μ n).eval x₀ = 0) : a < x₀ := by
  obtain ⟨q, hq⟩ : ∃ q : ℝ[X], family μ n = (X - C x₀) * q :=
    ⟨_, (mul_divByMonic_eq_iff_isRoot.mpr hx₀).symm⟩
  have hq0 : q ≠ 0 := fun h => family_ne_zero μ n (by rw [hq, h, mul_zero])
  have hqdeg : q.degree < n := by
    have hnat : (family μ n).natDegree = n := natDegree_eq_of_degree_eq_some (degree_family μ n)
    rw [hq, natDegree_mul (X_sub_C_ne_zero _) hq0, natDegree_X_sub_C] at hnat
    exact (natDegree_lt_iff_degree_lt hq0).mp (by omega)
  have hzero : ∫ t, ((X - C x₀) * q ^ 2).eval t ∂μ = 0 := by
    rw [← integral_family_mul_of_degree_lt hw hqdeg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    rw [hq]
    simp only [eval_mul, eval_sub, eval_X, eval_C, eval_pow]
    ring
  have hne : (X - C x₀) * q ^ 2 ≠ 0 := mul_ne_zero (X_sub_C_ne_zero _) (pow_ne_zero 2 hq0)
  by_contra h
  push Not at h
  refine (hw.integral_eval_pos_of_ae_nonneg hne ?_).ne' hzero
  filter_upwards [hae] with t ht
  simp only [eval_mul, eval_sub, eval_X, eval_C, eval_pow]
  exact mul_nonneg (by linarith) (sq_nonneg _)

/-- **A root of an orthogonal polynomial is strictly to the left of a right bound of the weight.**
If `μ`-almost every point is at most `b` and `x₀` is a root of `family μ n`, then `x₀ < b`; the
mirror image of `OrthogonalPolynomial.lt_root_family`.

Reference: [quarteroni2000numerical] §10.2; [kress1998numerical] §9.3. -/
theorem root_family_lt (hw : IsWeight μ) {b : ℝ} (hae : ∀ᵐ t ∂μ, t ≤ b) {n : ℕ} {x₀ : ℝ}
    (hx₀ : (family μ n).eval x₀ = 0) : x₀ < b := by
  obtain ⟨q, hq⟩ : ∃ q : ℝ[X], family μ n = (X - C x₀) * q :=
    ⟨_, (mul_divByMonic_eq_iff_isRoot.mpr hx₀).symm⟩
  have hq0 : q ≠ 0 := fun h => family_ne_zero μ n (by rw [hq, h, mul_zero])
  have hqdeg : q.degree < n := by
    have hnat : (family μ n).natDegree = n := natDegree_eq_of_degree_eq_some (degree_family μ n)
    rw [hq, natDegree_mul (X_sub_C_ne_zero _) hq0, natDegree_X_sub_C] at hnat
    exact (natDegree_lt_iff_degree_lt hq0).mp (by omega)
  have hzero : ∫ t, ((X - C x₀) * q ^ 2).eval t ∂μ = 0 := by
    rw [← integral_family_mul_of_degree_lt hw hqdeg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    rw [hq]
    simp only [eval_mul, eval_sub, eval_X, eval_C, eval_pow]
    ring
  have hne : (X - C x₀) * q ^ 2 ≠ 0 := mul_ne_zero (X_sub_C_ne_zero _) (pow_ne_zero 2 hq0)
  by_contra h
  push Not at h
  have hzero' : ∫ t, (-((X - C x₀) * q ^ 2)).eval t ∂μ = 0 := by
    simp only [eval_neg]
    rw [integral_neg, hzero, neg_zero]
  refine (hw.integral_eval_pos_of_ae_nonneg (neg_ne_zero.mpr hne) ?_).ne' hzero'
  filter_upwards [hae] with t ht
  simp only [eval_neg, eval_mul, eval_sub, eval_X, eval_C, eval_pow]
  rw [neg_mul_eq_neg_mul]
  exact mul_nonneg (by linarith) (sq_nonneg _)

end OrthogonalPolynomial

namespace Quadrature

open OrthogonalPolynomial

variable {μ : Measure ℝ}

/-- A function that is nonnegative on a carrier `s` of the weight `μ` and vanishes there only at
roots of a nonzero polynomial `p` has nonzero integral against `μ`: were the integral zero, the
function would vanish `μ`-almost everywhere, so the complement of the finite root set of `p` would
be `μ`-null, which no weight allows. -/
private theorem integral_ne_zero_of_ne_zero_off_roots (hw : IsWeight μ) {s : Set ℝ}
    (hsupp : μ sᶜ = 0) {p : ℝ[X]} (hp : p ≠ 0) {g : ℝ → ℝ} (hgint : Integrable g μ)
    (hg : ∀ t ∈ s, 0 ≤ g t) (hgne : ∀ t ∈ s, p.eval t ≠ 0 → g t ≠ 0) :
    ∫ t, g t ∂μ ≠ 0 := by
  intro h0
  have hae : ∀ᵐ t ∂μ, t ∈ s := by
    rw [MeasureTheory.ae_iff]; exact hsupp
  have hae0 : 0 ≤ᵐ[μ] g := by filter_upwards [hae] with t ht using hg t ht
  have hzero : g =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg_ae hae0 hgint).mp h0
  have hmeas : μ {t | g t ≠ 0} = 0 := by
    have hz := hzero
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at hz
    simpa using hz
  refine hw.measure_compl_ne_zero (Polynomial.finite_setOfPred_isRoot hp) ?_
  refine measure_mono_null (fun t ht => ?_) (measure_union_null hmeas hsupp)
  by_cases hts : t ∈ s
  · exact Or.inl (hgne t hts ht)
  · exact Or.inr hts

/-- **The Gauss remainder on an arbitrary interval.** Let `μ` be a weight carried by a convex set
`s ⊆ ℝ` (`μ sᶜ = 0`), let `x : Fin n → ℝ` be distinct nodes in `s` and `w` weights whose rule is
exact on the polynomials of degree less than `2n` — the Gauss rule of `Quadrature.exists_gauss` —
and let `f` be `μ`-integrable of class `C^{2n}`. Then

`(∫ f ∂μ) - ∑ i, w i * f (x i) = f^{(2n)}(ξ) / (2n)! * ∫ p_n² ∂μ`

for some `ξ ∈ s`, where `p_n = family μ n` is the nodal polynomial of the rule.

This is `Quadrature.exists_gauss_error_eq` with the compact carrier `[a, b]` replaced by any
interval and the implicit boundedness of `f^{(2n)}` removed. The rule is exact on the Hermite
interpolant `H` of `f` with double nodes at the `x i`, whose degree is less than `2n` and which
agrees with `f` at the nodes, so the error is `∫ (f - H) ∂μ`; and
`Hermite.exists_sub_interpolate_eq`, applied on the compact interval spanned by `t` and the nodes,
writes `f t - H t = f^{(2n)}(ξ_t)/(2n)! · p_n(t)²` for `t ∈ s`. Writing `c` for the error divided
by `∫ p_n² ∂μ`, the function `f - H - c p_n²` has zero integral; if `f^{(2n)}/(2n)!` were
everywhere above `c` on `s` that function would be nonnegative on `s` and nonzero off the roots of
`p_n`, which `integral_ne_zero_of_ne_zero_off_roots` forbids, and symmetrically below `c`. The
intermediate value theorem on the interval joining the two witnesses produces `ξ`.

Reference: [quarteroni2000numerical] (10.41)–(10.42); [kress1998numerical] §9.3. -/
theorem exists_gauss_error_eq_of_convex (hw : IsWeight μ) {s : Set ℝ} (hs : Convex ℝ s)
    (hsupp : μ sᶜ = 0) {n : ℕ} {x w : Fin n → ℝ} (hx : Function.Injective x)
    (hxmem : ∀ i, x i ∈ s)
    (hexact : ∀ p : ℝ[X], p.degree < ((2 * n : ℕ) : WithBot ℕ) →
      ∑ i, w i * p.eval (x i) = ∫ t, p.eval t ∂μ)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ((2 * n : ℕ) : WithTop ℕ∞) f) (hfint : Integrable f μ) :
    ∃ ξ ∈ s, (∫ t, f t ∂μ) - ∑ i, w i * f (x i) =
      iteratedDeriv (2 * n) f ξ / (2 * n).factorial * normSq μ n := by
  classical
  have := hw.isFiniteMeasure
  set D : ℝ → ℝ := fun ξ => iteratedDeriv (2 * n) f ξ / (2 * n).factorial with hD
  have hDcont : Continuous D := (hf.continuous_iteratedDeriv (2 * n) le_rfl).div_const _
  set H : ℝ[X] := Hermite.interpolate x (fun _ => 1) f with hH
  have hHdeg : H.degree < ((2 * n : ℕ) : WithBot ℕ) := by
    have hd := Hermite.degree_interpolate_lt hx (fun _ => 1) f
    simpa [Finset.sum_const, mul_comm] using hd
  have hHnode : ∀ i, H.eval (x i) = f (x i) := by
    intro i
    have hi := Hermite.eval_iterate_derivative_interpolate (f := f) (m := fun _ => 1) hx i
      (Nat.zero_le 1)
    simpa using hi
  have hint_H : Integrable (fun t => H.eval t) μ := hw.integrable_eval H
  have hIpos : 0 < normSq μ n := normSq_pos hw n
  -- the error is the integral of `f - H`
  have hsum : ∑ i, w i * f (x i) = ∫ t, H.eval t ∂μ := by
    rw [← hexact H hHdeg]
    exact Finset.sum_congr rfl fun i _ => by rw [hHnode i]
  have hint_fH : Integrable (fun t => f t - H.eval t) μ := hfint.sub hint_H
  have hEeq : (∫ t, f t ∂μ) - ∑ i, w i * f (x i) = ∫ t, (f t - H.eval t) ∂μ := by
    rw [hsum, ← integral_sub hfint hint_H]
  set c : ℝ := ((∫ t, f t ∂μ) - ∑ i, w i * f (x i)) / normSq μ n with hcdef
  have hc : (∫ t, f t ∂μ) - ∑ i, w i * f (x i) = c * normSq μ n := by
    rw [hcdef, div_mul_cancel₀ _ hIpos.ne']
  -- the pointwise error formula, on the compact interval spanned by `t` and the nodes
  have hpt : ∀ t ∈ s, ∃ ξ ∈ s, f t - H.eval t = D ξ * (family μ n).eval t ^ 2 := by
    intro t ht
    cases n with
    | zero =>
      refine ⟨t, ht, ?_⟩
      have hH0 : H = 0 := by
        rw [← degree_eq_bot]
        exact Nat.WithBot.lt_zero_iff.mp (by simpa using hHdeg)
      simp [hH0, hD]
    | succ m =>
      obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty x
      obtain ⟨i₁, -, hi₁⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x
      set a : ℝ := min t (x i₀) with ha
      set b : ℝ := max t (x i₁) with hb
      have hamem : a ∈ s := by
        rcases min_cases t (x i₀) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [ha, h]
        · exact ht
        · exact hxmem i₀
      have hbmem : b ∈ s := by
        rcases max_cases t (x i₁) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [hb, h]
        · exact ht
        · exact hxmem i₁
      have hsub : Set.Icc a b ⊆ s := hs.ordConnected.out hamem hbmem
      have htmem : t ∈ Set.Icc a b := ⟨min_le_left _ _, le_max_left _ _⟩
      have hxmem' : ∀ i, x i ∈ Set.Icc a b := by
        intro i
        refine ⟨le_trans (min_le_right _ _) ?_, le_trans ?_ (le_max_right _ _)⟩
        · rw [← hi₀]; exact Finset.inf'_le _ (Finset.mem_univ i)
        · rw [← hi₁]; exact Finset.le_sup' _ (Finset.mem_univ i)
      have hf' : ContDiff ℝ ((2 * m + 1 + 1 : ℕ) : WithTop ℕ∞) f := by
        rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring]; exact hf
      obtain ⟨ξ, hξ, hξeq⟩ := Hermite.exists_sub_interpolate_eq (N := 2 * m + 1) hf' hx hxmem'
        (m := fun _ => 1) (by simp; ring) htmem
      refine ⟨ξ, hsub hξ, ?_⟩
      have hnodal : Lagrange.nodal Finset.univ x = family μ (m + 1) :=
        ((isExactOnMeasure_two_mul_add_one_iff hw hx w).mp
          (isExactOnMeasure_iff_forall_degree_lt.mpr
            (by rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring]; exact hexact))).1
      rw [hξeq, ← hnodal, Lagrange.eval_nodal, hD]
      simp only [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, Finset.prod_pow]
  -- the error minus `c` times `∫ p_n²` integrates to zero
  have hsqint : Integrable (fun t => c * (family μ n).eval t ^ 2) μ :=
    (hw.integrable_eval_sq _).const_mul c
  have hgint : Integrable (fun t => f t - H.eval t - c * (family μ n).eval t ^ 2) μ :=
    hint_fH.sub hsqint
  have hIeq : ∫ t, c * (family μ n).eval t ^ 2 ∂μ = c * normSq μ n := by
    rw [integral_const_mul]; rfl
  have hgzero : ∫ t, (f t - H.eval t - c * (family μ n).eval t ^ 2) ∂μ = 0 := by
    rw [integral_sub hint_fH hsqint, hIeq, ← hEeq, hc, sub_self]
  -- the scaled top derivative takes values on both sides of `c`
  have hA : ∃ ξ ∈ s, D ξ ≤ c := by
    by_contra hcon
    push Not at hcon
    refine integral_ne_zero_of_ne_zero_off_roots hw hsupp (family_ne_zero μ n) hgint ?_ ?_ hgzero
    · intro t ht
      obtain ⟨ξ, hξ, hξeq⟩ := hpt t ht
      have h1 : 0 ≤ (D ξ - c) * (family μ n).eval t ^ 2 :=
        mul_nonneg (by linarith [hcon ξ hξ]) (sq_nonneg _)
      rw [sub_mul] at h1
      rw [hξeq]
      linarith
    · intro t ht hnz
      obtain ⟨ξ, hξ, hξeq⟩ := hpt t ht
      have h1 : 0 < (D ξ - c) * (family μ n).eval t ^ 2 :=
        mul_pos (by linarith [hcon ξ hξ])
          (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hnz)))
      rw [sub_mul] at h1
      rw [hξeq]
      exact ne_of_gt (by linarith)
  have hB : ∃ ξ ∈ s, c ≤ D ξ := by
    by_contra hcon
    push Not at hcon
    have hgzero' : ∫ t, -(f t - H.eval t - c * (family μ n).eval t ^ 2) ∂μ = 0 := by
      rw [integral_neg, hgzero, neg_zero]
    have hgintneg : Integrable (fun t => -(f t - H.eval t - c * (family μ n).eval t ^ 2)) μ :=
      hgint.neg
    refine integral_ne_zero_of_ne_zero_off_roots hw hsupp (family_ne_zero μ n) hgintneg ?_ ?_
      hgzero'
    · intro t ht
      obtain ⟨ξ, hξ, hξeq⟩ := hpt t ht
      have h1 : 0 ≤ (c - D ξ) * (family μ n).eval t ^ 2 :=
        mul_nonneg (by linarith [hcon ξ hξ]) (sq_nonneg _)
      rw [sub_mul] at h1
      rw [hξeq]
      linarith
    · intro t ht hnz
      obtain ⟨ξ, hξ, hξeq⟩ := hpt t ht
      have h1 : 0 < (c - D ξ) * (family μ n).eval t ^ 2 :=
        mul_pos (by linarith [hcon ξ hξ])
          (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hnz)))
      rw [sub_mul] at h1
      rw [hξeq]
      exact ne_of_gt (by linarith)
  obtain ⟨ξ₁, hξ₁, hle₁⟩ := hA
  obtain ⟨ξ₂, hξ₂, hle₂⟩ := hB
  have hmem : c ∈ Set.uIcc (D ξ₁) (D ξ₂) := Set.mem_uIcc.mpr (Or.inl ⟨hle₁, hle₂⟩)
  obtain ⟨ξ, hξmem, hξeq⟩ := intermediate_value_uIcc hDcont.continuousOn hmem
  refine ⟨ξ, hs.ordConnected.uIcc_subset hξ₁ hξ₂ hξmem, ?_⟩
  change _ = D ξ * normSq μ n
  rw [hξeq, hcdef, div_mul_cancel₀ _ hIpos.ne']

end Quadrature
