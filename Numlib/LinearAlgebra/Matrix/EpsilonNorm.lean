/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Matrix.Normed`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.LinearAlgebra.Matrix.Complexify

/-!
# Norms in which a matrix is within `ε` of its spectral radius

The spectral radius is a lower bound for every operator norm of a matrix, and it is the *greatest*
such lower bound: for every `ε > 0` there is a vector norm on `ℝⁿ` whose induced operator norm of
`A` is at most `ρ(A) + ε`. Consequently `ρ(A)` is the infimum of `‖A‖` over the operator norms.

The vector norm is built from Gelfand's formula rather than from a triangularization: pick `k` with
`‖Aᵏ‖ ≤ cᵏ`, where `c = ρ(A) + ε`, and set

`p x = ∑_{j < k} c⁻ʲ ‖Aʲ x‖`.

Then `c p x - p (A x) = c ‖x‖ - c¹⁻ᵏ ‖Aᵏ x‖ ≥ 0`, so `A` is `c`-Lipschitz for `p`; and `p ≥ ‖·‖`
because the term `j = 0` is `‖x‖`, so `p` is a norm equivalent to the original one. The classical
argument — Schur triangularization followed by the diagonal scaling `diag(δ, δ², …)` — gives the
same conclusion with `p x = ‖D⁻¹ Qᴴ x‖`, but needs the triangular form; this one needs only that
some power of `A` is small, which is what Gelfand's formula provides.

## Main results

* `Matrix.exists_seminorm_forall_mulVec_le`: the norm `p` above, with the equivalence bounds
  `‖x‖ ≤ p x ≤ C ‖x‖` and `p (A x) ≤ (ρ(A) + ε) p x`.
* `Matrix.complexSpectralRadius_toReal_le_of_forall_mulVec_le`: the converse bound, that a constant
  `c ≥ 0` with `p (A x) ≤ c p x` for a norm `p` equivalent to the original is at least `ρ(A)`. This
  is the spectral radius bounding an operator norm, for an arbitrary vector norm; together the two
  say that the operator norm of `A` for `p` lies in `[ρ(A), ρ(A) + ε]`.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A constant `c ≥ 0` for which `A` is `c`-Lipschitz in a norm `p` equivalent to the supremum norm
is at least the spectral radius of `A`. Applied to the operator norm induced by `p`, this is the
statement that the spectral radius is a lower bound for every operator norm.

The proof scales: `c'⁻¹ A` has all its entries bounded by `(M/m) (c/c')ᵏ` in the `k`-th power, so
its powers tend to `0` and its spectral radius is less than one; hence `ρ(A) < c'` for every
`c' > c`. -/
theorem complexSpectralRadius_toReal_le_of_forall_mulVec_le (A : Matrix n n ℝ)
    (p : Seminorm ℝ (n → ℝ)) {m M c : ℝ} (hm : 0 < m) (hlow : ∀ x, m * ‖x‖ ≤ p x)
    (hup : ∀ x, p x ≤ M * ‖x‖) (hc : 0 ≤ c) (hA : ∀ x, p (A *ᵥ x) ≤ c * p x) :
    (complexSpectralRadius A).toReal ≤ c := by
  -- `A` is `cʲ`-Lipschitz for `p` in the `j`-th power.
  have hpow : ∀ (j : ℕ) (x : n → ℝ), p ((A ^ j) *ᵥ x) ≤ c ^ j * p x := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      calc p ((A ^ (j + 1)) *ᵥ x) = p (A *ᵥ ((A ^ j) *ᵥ x)) := by rw [mulVec_mulVec, ← pow_succ']
        _ ≤ c * p ((A ^ j) *ᵥ x) := hA _
        _ ≤ c * (c ^ j * p x) := by
          have := ih x
          nlinarith [apply_nonneg p ((A ^ j) *ᵥ x), apply_nonneg p x]
        _ = c ^ (j + 1) * p x := by ring
  -- hence its entries are bounded by `(M/m) cʲ`, by testing against the standard basis.
  have hent : ∀ (j : ℕ) (i l : n), |(A ^ j) i l| ≤ M / m * c ^ j := by
    intro j i l
    set e : n → ℝ := Pi.single l 1 with he
    have hx : ‖e‖ = 1 := by
      refine le_antisymm (pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun i => ?_) ?_
      · rcases eq_or_ne i l with rfl | h
        · simp [he]
        · simp [he, h]
      · simpa [he] using norm_le_pi_norm e l
    have h1 : m * ‖(A ^ j) *ᵥ e‖ ≤ c ^ j * M := by
      calc m * ‖(A ^ j) *ᵥ e‖ ≤ p ((A ^ j) *ᵥ e) := hlow _
        _ ≤ c ^ j * p e := hpow _ _
        _ ≤ c ^ j * (M * ‖e‖) := by
          have := hup e
          have hcj : (0 : ℝ) ≤ c ^ j := pow_nonneg hc j
          nlinarith
        _ = c ^ j * M := by rw [hx, mul_one]
    have h2 : |(A ^ j) i l| ≤ ‖(A ^ j) *ᵥ e‖ := by
      rw [he, mulVec_single_one]
      simpa using norm_le_pi_norm ((A ^ j).col l) i
    rw [div_mul_eq_mul_div, le_div_iff₀ hm]
    calc |(A ^ j) i l| * m = m * |(A ^ j) i l| := by ring
      _ ≤ m * ‖(A ^ j) *ᵥ e‖ := by nlinarith
      _ ≤ c ^ j * M := h1
      _ = M * c ^ j := by ring
  -- so `ρ(A) < c'` for every `c' > c`, by scaling.
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set c' := c + δ with hc'
  have hc'0 : 0 < c' := by positivity
  have hlt : c / c' < 1 := by rw [div_lt_one hc'0]; linarith
  have htend : Tendsto (fun k => ((c'⁻¹ : ℝ) • A) ^ k) atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun l => ?_
    have hg : Tendsto (fun k : ℕ => M / m * (c / c') ^ k) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hlt).const_mul (M / m)
    refine squeeze_zero_norm (fun k => ?_) hg
    have hk : (((c'⁻¹ : ℝ) • A) ^ k) i l = (c'⁻¹) ^ k * (A ^ k) i l := by
      rw [smul_pow]; simp
    rw [hk, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (by positivity : (0:ℝ) ≤ c'⁻¹)]
    calc c'⁻¹ ^ k * |(A ^ k) i l| ≤ c'⁻¹ ^ k * (M / m * c ^ k) := by
          have := hent k i l
          nlinarith [pow_nonneg (le_of_lt (inv_pos.2 hc'0)) k, abs_nonneg ((A ^ k) i l)]
      _ = M / m * (c / c') ^ k := by rw [div_pow]; ring
  have hρ : complexSpectralRadius ((c'⁻¹ : ℝ) • A) < 1 :=
    (tendsto_pow_iff_complexSpectralRadius_lt_one _).1 htend
  rw [complexSpectralRadius_smul] at hρ
  have hne : (‖(c'⁻¹ : ℝ)‖₊ : ℝ≥0∞) * complexSpectralRadius A ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (complexSpectralRadius_ne_top A)
  have hlt' : ((‖(c'⁻¹ : ℝ)‖₊ : ℝ≥0∞) * complexSpectralRadius A).toReal < 1 := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal hne (by simp)).2 hρ
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, coe_nnnorm, Real.norm_eq_abs,
    abs_of_nonneg (le_of_lt (inv_pos.2 hc'0))] at hlt'
  rw [inv_mul_eq_div, div_lt_one hc'0] at hlt'
  linarith

section Operator

open scoped Matrix.Norms.Operator

/-- **The `ε`-norm theorem.** For every `ε > 0` there is a norm `p` on `ℝⁿ`, equivalent to the
supremum norm, in which `A` is `(ρ(A) + ε)`-Lipschitz: the operator norm of `A` induced by `p` is at
most `ρ(A) + ε`. With `Matrix.complexSpectralRadius_toReal_le_of_forall_mulVec_le` for the reverse
inequality, this says that the spectral radius is the infimum of `‖A‖` over the operator norms.

The norm is `p x = ∑_{j < k} c⁻ʲ ‖Aʲ x‖` with `c = ρ(A) + ε` and `k` chosen by Gelfand's formula so
that `‖Aᵏ‖ ≤ cᵏ`; the telescoping identity `p (A x) = c (p x + c⁻ᵏ ‖Aᵏ x‖ - ‖x‖)` then gives the
Lipschitz bound. -/
theorem exists_seminorm_forall_mulVec_le (A : Matrix n n ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Seminorm ℝ (n → ℝ), (∀ x, ‖x‖ ≤ p x) ∧ (∃ C, ∀ x, p x ≤ C * ‖x‖) ∧
      ∀ x, p (A *ᵥ x) ≤ ((complexSpectralRadius A).toReal + ε) * p x := by
  set c : ℝ := (complexSpectralRadius A).toReal + ε with hcdef
  have hc0 : 0 < c := by
    have := ENNReal.toReal_nonneg (a := complexSpectralRadius A)
    linarith
  -- Gelfand's formula gives a power with `‖Aᵏ‖ ≤ cᵏ`.
  obtain ⟨k, hk1, hk⟩ : ∃ k : ℕ, 1 ≤ k ∧ ‖A ^ k‖ ^ (1 / k : ℝ) < c := by
    have h := (tendsto_pow_rpow_linfty_opNorm A).eventually_lt_const (by linarith : _ < c)
    exact ((eventually_ge_atTop 1).and h).exists
  have hAk : ‖A ^ k‖ ≤ c ^ k := by
    have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have h1 : (‖A ^ k‖ ^ (1 / k : ℝ)) ^ k = ‖A ^ k‖ := by
      rw [← Real.rpow_natCast (‖A ^ k‖ ^ (1 / k : ℝ)) k, ← Real.rpow_mul (norm_nonneg _), one_div,
        inv_mul_cancel₀ hkne, Real.rpow_one]
    calc ‖A ^ k‖ = (‖A ^ k‖ ^ (1 / k : ℝ)) ^ k := h1.symm
      _ ≤ c ^ k := pow_le_pow_left₀ (by positivity) hk.le k
  have hAkx : ∀ x : n → ℝ, ‖(A ^ k) *ᵥ x‖ ≤ c ^ k * ‖x‖ := fun x =>
    (linfty_opNorm_mulVec (A ^ k) x).trans (by gcongr)
  -- the weighted sum of the norms of the first `k` iterates
  set f : (n → ℝ) → ℕ → ℝ := fun x j => (c ^ j)⁻¹ * ‖(A ^ j) *ᵥ x‖ with hf
  have hadd : ∀ x y : n → ℝ, ∑ j ∈ Finset.range k, f (x + y) j
      ≤ (∑ j ∈ Finset.range k, f x j) + ∑ j ∈ Finset.range k, f y j := by
    intro x y
    calc ∑ j ∈ Finset.range k, f (x + y) j ≤ ∑ j ∈ Finset.range k, (f x j + f y j) := by
          refine Finset.sum_le_sum fun j _ => ?_
          simp only [hf, mulVec_add]
          have h : ‖(A ^ j) *ᵥ x + (A ^ j) *ᵥ y‖ ≤ ‖(A ^ j) *ᵥ x‖ + ‖(A ^ j) *ᵥ y‖ :=
            norm_add_le _ _
          have hcj : (0 : ℝ) < (c ^ j)⁻¹ := by positivity
          nlinarith
      _ = (∑ j ∈ Finset.range k, f x j) + ∑ j ∈ Finset.range k, f y j := Finset.sum_add_distrib
  have hsmul : ∀ (a : ℝ) (x : n → ℝ), ∑ j ∈ Finset.range k, f (a • x) j
      = ‖a‖ * ∑ j ∈ Finset.range k, f x j := by
    intro a x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hf, mulVec_smul, norm_smul, Real.norm_eq_abs]
    ring
  have hnorm_le : ∀ x : n → ℝ, ‖x‖ ≤ ∑ j ∈ Finset.range k, f x j := by
    intro x
    have h0 : f x 0 = ‖x‖ := by simp [hf]
    calc ‖x‖ = f x 0 := h0.symm
      _ ≤ ∑ j ∈ Finset.range k, f x j :=
        Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_range.2 (by omega))
  have hle_norm : ∀ x : n → ℝ, ∑ j ∈ Finset.range k, f x j
      ≤ (∑ j ∈ Finset.range k, (c ^ j)⁻¹ * ‖A ^ j‖) * ‖x‖ := by
    intro x
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    have hcj : (0 : ℝ) < (c ^ j)⁻¹ := by positivity
    have h := linfty_opNorm_mulVec (A ^ j) x
    simp only [hf]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h hcj.le
  have hkey : ∀ x : n → ℝ, ∑ j ∈ Finset.range k, f (A *ᵥ x) j
      ≤ c * ∑ j ∈ Finset.range k, f x j := by
    intro x
    -- the telescoping identity
    have hshift : ∀ j, f (A *ᵥ x) j = c * f x (j + 1) := by
      intro j
      simp only [hf]
      rw [mulVec_mulVec, ← pow_succ]
      field_simp
      ring
    have hsum : ∑ j ∈ Finset.range k, f x (j + 1)
        = (∑ j ∈ Finset.range k, f x j) + f x k - f x 0 := by
      have h1 : ∑ j ∈ Finset.range (k + 1), f x j = (∑ j ∈ Finset.range k, f x (j + 1)) + f x 0 :=
        Finset.sum_range_succ' _ k
      have h2 : ∑ j ∈ Finset.range (k + 1), f x j = (∑ j ∈ Finset.range k, f x j) + f x k :=
        Finset.sum_range_succ _ k
      linarith
    have hfk : f x k ≤ f x 0 := by
      have h0 : f x 0 = ‖x‖ := by simp [hf]
      have : (c ^ k)⁻¹ * ‖(A ^ k) *ᵥ x‖ ≤ (c ^ k)⁻¹ * (c ^ k * ‖x‖) :=
        mul_le_mul_of_nonneg_left (hAkx x) (by positivity)
      simp only [hf] at h0 ⊢
      rw [h0]
      calc (c ^ k)⁻¹ * ‖(A ^ k) *ᵥ x‖ ≤ (c ^ k)⁻¹ * (c ^ k * ‖x‖) := this
        _ = ‖x‖ := by field_simp
    calc ∑ j ∈ Finset.range k, f (A *ᵥ x) j = ∑ j ∈ Finset.range k, c * f x (j + 1) :=
          Finset.sum_congr rfl fun j _ => hshift j
      _ = c * ∑ j ∈ Finset.range k, f x (j + 1) := by rw [Finset.mul_sum]
      _ = c * ((∑ j ∈ Finset.range k, f x j) + f x k - f x 0) := by rw [hsum]
      _ ≤ c * ∑ j ∈ Finset.range k, f x j := by nlinarith
  exact ⟨{ toFun := fun x => ∑ j ∈ Finset.range k, f x j
           map_zero' := by simp [hf]
           add_le' := hadd
           neg' := fun x => by simp [hf, mulVec_neg]
           smul' := hsmul }, hnorm_le, ⟨_, hle_norm⟩, hkey⟩

end Operator

end Matrix
