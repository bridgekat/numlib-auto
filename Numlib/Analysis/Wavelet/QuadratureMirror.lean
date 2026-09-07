import Numlib.Analysis.InnerProductSpace.OrthonormalSeries

/-!
# Quadrature mirror filters and the two-channel decomposition

A **quadrature mirror filter** is a real sequence `p : ℤ → ℝ` satisfying

`∑_k p_k p_{k - 2l} = δ_{0l}`,

the condition that the even translates of `p` are orthonormal in `ℓ²(ℤ)`. Attached to it is the
**high-pass filter** `q_k = (-1)^k p_{1-k}`. The point of this module is that the single condition
above already forces the *combined* family of even translates of `p` and of `q` to be an orthonormal
**basis**: nothing else is needed, and in particular no Fourier analysis.

Transported along an orthonormal family `e : ℤ → E` in a Hilbert space, that says: if `f l` is the
sum of `∑_k p_{k-2l} e_k` and `g l` the sum of `∑_k q_{k-2l} e_k`, then `f` and `g` together form an
orthonormal family whose closed span is the closed span of `e`. Applied to the level-`1` scaling
system of a multiresolution analysis, with `p` the dilation coefficients, this is the whole
algebraic content of Mallat's theorem; see `Numlib/Analysis/Wavelet/Multiresolution`.

## Main definitions

* `IsQMFCoeff p`: the condition `∑_k p_k p_{k - 2l} = δ_{0l}`.
* `qmfHigh p`: the high-pass filter `q_k = (-1)^k p_{1-k}`.

## Main statements

* `IsQMFCoeff.hasSum_low_low`, `IsQMFCoeff.hasSum_high_high`, `IsQMFCoeff.hasSum_low_high`: the
  three orthonormality relations of the two-channel family. The last is a pure involution argument:
  the substitution `k ↦ 1 + 2l + 2m - k` sends the summand to its negative.
* `IsQMFCoeff.hasSum_sumElim_sq`: the **completeness relation** `∑_l (p_{k-2l}² + q_{k-2l}²) = 1`,
  which is the splitting of `∑_k p_k² = 1` into the two parities: `k - 2l` runs over the integers
  congruent to `k`, and `1 - k + 2l` over the others.
* `IsQMFCoeff.orthonormal_sumElim` and `IsQMFCoeff.topologicalClosure_span_sumElim`: the two-channel
  family in a Hilbert space is orthonormal and has the same closed span as the family it is built
  from.
-/

noncomputable section

variable {p : ℤ → ℝ}

/-! ### The filters -/

/-- **A quadrature mirror filter**: a coefficient sequence `p : ℤ → ℝ` whose even translates are
orthonormal in `ℓ²(ℤ)`, that is, `∑_k p_k p_{k - 2l} = δ_{0l}`. -/
def IsQMFCoeff (p : ℤ → ℝ) : Prop :=
  ∀ l : ℤ, HasSum (fun k : ℤ => p k * p (k - 2 * l)) (if l = 0 then 1 else 0)

/-- The **high-pass filter** attached to a low-pass filter `p`: `q_k = (-1)^k p_{1-k}`. -/
def qmfHigh (p : ℤ → ℝ) (k : ℤ) : ℝ := (-1 : ℝ) ^ k * p (1 - k)

/-! ### The alternating sign -/

private theorem neg_one_zpow_mul_self (k : ℤ) : ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1 := by
  rcases Int.even_or_odd k with hk | hk
  · rw [hk.neg_one_zpow]; norm_num
  · rw [hk.neg_one_zpow]; norm_num

private theorem neg_one_zpow_sub_two_mul (k l : ℤ) :
    (-1 : ℝ) ^ (k - 2 * l) = (-1 : ℝ) ^ k := by
  have h : Even (-(2 * l)) := ⟨-l, by ring⟩
  rw [sub_eq_add_neg, zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), h.neg_one_zpow, mul_one]

private theorem neg_one_zpow_one_sub (k : ℤ) : (-1 : ℝ) ^ (1 - k) = -((-1 : ℝ) ^ k) := by
  rcases Int.even_or_odd k with hk | hk
  · have h1 : Odd (1 - k) := by obtain ⟨r, rfl⟩ := hk; exact ⟨-r, by ring⟩
    rw [h1.neg_one_zpow, hk.neg_one_zpow]
  · have h1 : Even (1 - k) := by obtain ⟨r, rfl⟩ := hk; exact ⟨-r, by ring⟩
    rw [h1.neg_one_zpow, hk.neg_one_zpow]
    norm_num

/-- The high-pass filter has the same squares as the low-pass filter, reflected. -/
theorem qmfHigh_sq (p : ℤ → ℝ) (k : ℤ) : qmfHigh p k ^ 2 = p (1 - k) ^ 2 := by
  rw [qmfHigh, mul_pow, pow_two ((-1 : ℝ) ^ k), neg_one_zpow_mul_self, one_mul]

/-- The even translates of the high-pass filter, with the sign taken out. -/
theorem qmfHigh_sub_two_mul (p : ℤ → ℝ) (k l : ℤ) :
    qmfHigh p (k - 2 * l) = (-1 : ℝ) ^ k * p (1 - k + 2 * l) := by
  rw [qmfHigh, neg_one_zpow_sub_two_mul, show (1 : ℤ) - (k - 2 * l) = 1 - k + 2 * l by ring]

/-! ### Summability -/

private theorem summable_mul_of_summable_sq {f g : ℤ → ℝ} (hf : Summable fun k => f k ^ 2)
    (hg : Summable fun k => g k ^ 2) : Summable fun k => f k * g k := by
  refine Summable.of_abs (Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
    ((hf.add hg).div_const 2))
  rw [abs_mul]
  nlinarith [sq_nonneg (|f k| - |g k|), abs_nonneg (f k), abs_nonneg (g k), sq_abs (f k),
    sq_abs (g k)]

namespace IsQMFCoeff

/-- The squares of the coefficients of a quadrature mirror filter sum to one. -/
theorem hasSum_sq (hp : IsQMFCoeff p) : HasSum (fun k : ℤ => p k ^ 2) 1 := by
  have h := hp 0
  simp only [mul_zero, sub_zero] at h
  exact h.congr_fun fun k => pow_two (p k)

theorem summable_sq (hp : IsQMFCoeff p) : Summable fun k : ℤ => p k ^ 2 :=
  hp.hasSum_sq.summable

theorem summable_low_sq (hp : IsQMFCoeff p) (l : ℤ) :
    Summable fun k : ℤ => p (k - 2 * l) ^ 2 := by
  have hinj : Function.Injective (fun k : ℤ => k - 2 * l) := fun a b hab => by
    have h : a - 2 * l = b - 2 * l := hab
    omega
  exact hp.summable_sq.comp_injective hinj

theorem summable_high_sq (hp : IsQMFCoeff p) (l : ℤ) :
    Summable fun k : ℤ => qmfHigh p (k - 2 * l) ^ 2 := by
  have hinj : Function.Injective (fun k : ℤ => 1 - k + 2 * l) := fun a b hab => by
    have h : 1 - a + 2 * l = 1 - b + 2 * l := hab
    omega
  refine (hp.summable_sq.comp_injective hinj).congr fun k => ?_
  simp only [Function.comp_apply]
  rw [qmfHigh_sq, show (1 : ℤ) - (k - 2 * l) = 1 - k + 2 * l by ring]

/-! ### The orthonormality relations -/

/-- The even translates of the low-pass filter are orthonormal: this is the defining condition,
rewritten with both indices shifted. -/
theorem hasSum_low_low (hp : IsQMFCoeff p) (l m : ℤ) :
    HasSum (fun k : ℤ => p (k - 2 * l) * p (k - 2 * m)) (if l = m then 1 else 0) := by
  have h := hp (l - m)
  rw [show (if l - m = 0 then (1 : ℝ) else 0) = (if l = m then 1 else 0) by
    by_cases hlm : l = m <;> simp [hlm, sub_eq_zero]] at h
  rw [← Equiv.hasSum_iff (Equiv.subRight (2 * m))] at h
  refine h.congr_fun fun k => ?_
  simp only [Function.comp_apply, Equiv.subRight_apply]
  rw [show k - 2 * m - 2 * (l - m) = k - 2 * l by ring, mul_comm]

/-- The even translates of the high-pass filter are orthonormal. The substitution
`k ↦ 1 + 2m - k` turns the sum into the defining condition at `m - l`. -/
theorem hasSum_high_high (hp : IsQMFCoeff p) (l m : ℤ) :
    HasSum (fun k : ℤ => qmfHigh p (k - 2 * l) * qmfHigh p (k - 2 * m))
      (if l = m then 1 else 0) := by
  have h := hp (m - l)
  rw [show (if m - l = 0 then (1 : ℝ) else 0) = (if l = m then 1 else 0) by
    by_cases hlm : l = m <;> simp [hlm, sub_eq_zero, eq_comm]] at h
  rw [← Equiv.hasSum_iff (Equiv.subLeft (1 + 2 * m))] at h
  refine h.congr_fun fun k => ?_
  simp only [Function.comp_apply, Equiv.subLeft_apply]
  rw [qmfHigh_sub_two_mul, qmfHigh_sub_two_mul,
    show (1 : ℤ) + 2 * m - k - 2 * (m - l) = 1 - k + 2 * l by ring,
    show (1 : ℤ) + 2 * m - k = 1 - k + 2 * m by ring]
  linear_combination (p (1 - k + 2 * l) * p (1 - k + 2 * m)) * neg_one_zpow_mul_self k

/-- The even translates of the low-pass and of the high-pass filter are orthogonal to each other.
The involution `k ↦ 1 + 2l + 2m - k` sends the summand to its negative, so the sum is its own
negative. -/
theorem hasSum_low_high (hp : IsQMFCoeff p) (l m : ℤ) :
    HasSum (fun k : ℤ => p (k - 2 * l) * qmfHigh p (k - 2 * m)) 0 := by
  have hneg : ∀ k : ℤ, p (1 + 2 * m + 2 * l - k - 2 * l)
      * qmfHigh p (1 + 2 * m + 2 * l - k - 2 * m)
      = -(p (k - 2 * l) * qmfHigh p (k - 2 * m)) := by
    intro k
    have e1 : 1 + 2 * m + 2 * l - k - 2 * l = 1 + 2 * m - k := by ring
    have e2 : 1 + 2 * m + 2 * l - k - 2 * m = 1 + 2 * l - k := by ring
    have hA : qmfHigh p (1 + 2 * l - k) = -((-1 : ℝ) ^ k * p (k - 2 * l)) := by
      rw [qmfHigh, show (1 : ℤ) - (1 + 2 * l - k) = k - 2 * l by ring,
        show (1 : ℤ) + 2 * l - k = 1 - k - 2 * (-l) by ring, neg_one_zpow_sub_two_mul,
        neg_one_zpow_one_sub]
      ring
    rw [e1, e2, hA, qmfHigh_sub_two_mul, show (1 : ℤ) + 2 * m - k = 1 - k + 2 * m by ring]
    ring
  obtain ⟨a, ha⟩ := summable_mul_of_summable_sq (hp.summable_low_sq l) (hp.summable_high_sq m)
  have hτ : HasSum (fun k : ℤ => -(p (k - 2 * l) * qmfHigh p (k - 2 * m))) a :=
    ((Equiv.hasSum_iff (Equiv.subLeft (1 + 2 * m + 2 * l))).mpr ha).congr_fun fun k => by
      simpa only [Function.comp_apply, Equiv.subLeft_apply] using (hneg k).symm
  have hna : HasSum (fun k : ℤ => p (k - 2 * l) * qmfHigh p (k - 2 * m)) (-a) := by
    simpa using hτ.neg
  have hself : a = -a := ha.unique hna
  rwa [show a = 0 by linarith] at ha

/-! ### The completeness relation -/

/-- The two branches `l ↦ k - 2l` and `l ↦ 1 - k + 2l` together enumerate `ℤ`: the first hits the
integers congruent to `k` mod `2`, the second the rest. -/
private def splitEquiv (k : ℤ) : ℤ ⊕ ℤ ≃ ℤ :=
  Equiv.ofBijective (Sum.elim (fun l : ℤ => k - 2 * l) (fun l : ℤ => 1 - k + 2 * l)) <| by
    constructor
    · rintro (a | a) (b | b) hab
      · simp only [Sum.elim_inl] at hab
        simp only [Sum.inl.injEq]
        omega
      · simp only [Sum.elim_inl, Sum.elim_inr] at hab
        exact absurd hab (by omega)
      · simp only [Sum.elim_inl, Sum.elim_inr] at hab
        exact absurd hab (by omega)
      · simp only [Sum.elim_inr] at hab
        simp only [Sum.inr.injEq]
        omega
    · intro n
      rcases Int.even_or_odd (k - n) with ⟨r, hr⟩ | ⟨r, hr⟩
      · exact ⟨Sum.inl r, by simp only [Sum.elim_inl]; omega⟩
      · exact ⟨Sum.inr (k - r - 1), by simp only [Sum.elim_inr]; omega⟩

/-- **The completeness relation of a quadrature mirror filter**: for every `k`,
`∑_l (p_{k-2l}² + q_{k-2l}²) = 1`. It is nothing but the splitting of `∑_k p_k² = 1` into the two
residue classes mod `2`, and it is what makes the two-channel family complete. -/
theorem hasSum_sumElim_sq (hp : IsQMFCoeff p) (k : ℤ) :
    HasSum (Sum.elim (fun l : ℤ => p (k - 2 * l) ^ 2)
      (fun l : ℤ => qmfHigh p (k - 2 * l) ^ 2)) 1 := by
  refine ((Equiv.hasSum_iff (splitEquiv k)).mpr hp.hasSum_sq).congr_fun ?_
  rintro (l | l)
  · rfl
  · change qmfHigh p (k - 2 * l) ^ 2 = p (1 - k + 2 * l) ^ 2
    rw [qmfHigh_sq, show (1 : ℤ) - (k - 2 * l) = 1 - k + 2 * l by ring]

end IsQMFCoeff

/-! ### The two-channel family in a Hilbert space -/

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {e f g : ℤ → E}

namespace IsQMFCoeff

variable (hp : IsQMFCoeff p) (he : Orthonormal ℝ e)
  (hf : ∀ l, HasSum (fun k : ℤ => p (k - 2 * l) • e k) (f l))
  (hg : ∀ l, HasSum (fun k : ℤ => qmfHigh p (k - 2 * l) • e k) (g l))
include hp he hf hg

omit [CompleteSpace E] in
/-- **The two-channel family is orthonormal.** -/
theorem orthonormal_sumElim : Orthonormal ℝ (Sum.elim f g) := by
  rw [orthonormal_iff_ite]
  rintro (l | l) (m | m)
  · simpa using (he.hasSum_mul_of_hasSum (hf l) (hf m)).unique (hp.hasSum_low_low l m)
  · simpa using (he.hasSum_mul_of_hasSum (hf l) (hg m)).unique (hp.hasSum_low_high l m)
  · have h := (he.hasSum_mul_of_hasSum (hg l) (hf m)).unique
      ((hp.hasSum_low_high m l).congr_fun fun k => mul_comm _ _)
    simpa using h
  · simpa using (he.hasSum_mul_of_hasSum (hg l) (hg m)).unique (hp.hasSum_high_high l m)

/-- **The two-channel family spans what the original family spans.** With
`IsQMFCoeff.orthonormal_sumElim` this says that the low-pass and high-pass channels together are an
orthonormal basis of the closed span of `e`. -/
theorem topologicalClosure_span_sumElim :
    (Submodule.span ℝ (Set.range (Sum.elim f g))).topologicalClosure
      = (Submodule.span ℝ (Set.range e)).topologicalClosure := by
  refine le_antisymm (Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_)
    (Submodule.isClosed_topologicalClosure _))
    (Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_)
      (Submodule.isClosed_topologicalClosure _))
  · rintro _ ⟨l | l, rfl⟩
    · exact mem_topologicalClosure_span_of_hasSum (hf l)
    · exact mem_topologicalClosure_span_of_hasSum (hg l)
  · rintro _ ⟨k, rfl⟩
    refine (orthonormal_sumElim hp he hf hg).mem_topologicalClosure_span_of_hasSum_inner_sq ?_
    rw [show ‖e k‖ ^ 2 = 1 by rw [he.1 k, one_pow]]
    refine (hp.hasSum_sumElim_sq k).congr_fun ?_
    rintro (l | l)
    · rw [Sum.elim_inl, Sum.elim_inl, real_inner_comm, he.inner_eq_of_hasSum (hf l) k]
    · rw [Sum.elim_inr, Sum.elim_inr, real_inner_comm, he.inner_eq_of_hasSum (hg l) k]

end IsQMFCoeff

end Hilbert
