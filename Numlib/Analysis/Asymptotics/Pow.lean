import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# Powers at zero: big-O comparisons and the vanishing of low-order terms

Mathlib's `Asymptotics.isLittleO_pow_pow` says `x ^ n = o(x ^ m)` at `0` for `m < n`. This module
adds its non-strict companion `Asymptotics.isBigO_pow_pow` and the two consequences that the
order conditions of numerical methods for ODEs use, each a statement that a quantity of a given
order in the step `h` which is also of a higher order must vanish:

* `eq_zero_of_isBigO_pow_succ` — a coefficient `c` with `c h ^ m = O(h ^ (m + 1))` as `h → 0⁺` is
  zero, since otherwise `h ^ m = o(h ^ m)`;
* `Polynomial.eq_zero_of_isBigO_pow_succ` — a complex polynomial of degree at most `n` whose values
  along real `h → 0⁺` are `O(h ^ (n + 1))` is zero, by induction on `n`: the constant term is the
  value at `0`, hence zero, and `p / X` is `O(h ^ n)`.

The truncation error of a method of order `q` tested on a polynomial solution is a polynomial (or a
monomial) in `h`; these lemmas turn "it is `O(h ^ q)`" into equations on its coefficients, the
algebraic order conditions.
-/

open Filter Topology Asymptotics

namespace Asymptotics

variable {𝕜 : Type*} [NormedDivisionRing 𝕜]

/-- `x ^ n = O(x ^ m)` as `x → 0` for `m ≤ n`: the non-strict companion of Mathlib's
`isLittleO_pow_pow`. -/
theorem isBigO_pow_pow {m n : ℕ} (h : m ≤ n) :
    (fun x : 𝕜 => x ^ n) =O[𝓝 0] fun x => x ^ m := by
  rcases h.lt_or_eq with hlt | rfl
  · exact (isLittleO_pow_pow hlt).isBigO
  · exact isBigO_refl _ _

end Asymptotics

/-- A coefficient `c` with `c h ^ m = O(h ^ (m + 1))` as `h → 0⁺` vanishes: otherwise
`h ^ m = c⁻¹ (c h ^ m)` would be `O(h ^ (m + 1)) = o(h ^ m)`. -/
theorem eq_zero_of_isBigO_pow_succ {c : ℝ} {m : ℕ}
    (h : (fun h : ℝ => c * h ^ m) =O[𝓝[>] 0] fun h => h ^ (m + 1)) : c = 0 := by
  by_contra hc
  have h₁ : (fun h : ℝ => h ^ m) =O[𝓝[>] 0] fun h => h ^ (m + 1) := by
    simpa [inv_mul_cancel_left₀ hc] using h.const_mul_left c⁻¹
  refine isLittleO_irrefl ?_
    (h₁.trans_isLittleO ((isLittleO_pow_pow m.lt_succ_self).mono nhdsWithin_le_nhds))
  have hne : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ^ m ≠ 0 :=
    eventually_mem_nhdsWithin.mono fun x hx => pow_ne_zero m (ne_of_gt hx)
  exact hne.frequently

/-- **A complex polynomial of degree at most `n` that is `O(h ^ (n + 1))` along real `h → 0⁺`
vanishes.** By induction on `n`: a constant is the case `m = 0` of `eq_zero_of_isBigO_pow_succ`
applied to its norm; in general the constant term is the limit at `0`, hence zero, and `p / X` is
`O(h ^ n)`. -/
theorem Polynomial.eq_zero_of_isBigO_pow_succ :
    ∀ (n : ℕ) (p : Polynomial ℂ), p.natDegree ≤ n →
      (fun h : ℝ => p.eval (h : ℂ)) =O[𝓝[>] 0] (fun h => h ^ (n + 1)) → p = 0 := by
  intro n
  induction n with
  | zero =>
    intro p hp h
    rw [Polynomial.eq_C_of_natDegree_le_zero hp] at h ⊢
    have := _root_.eq_zero_of_isBigO_pow_succ (c := ‖p.coeff 0‖) (m := 0)
      (by simpa using h.norm_left)
    rw [norm_eq_zero.1 this, map_zero]
  | succ n ih =>
    intro p hp h
    -- the constant term vanishes
    have h0 : p.coeff 0 = 0 := by
      have hlim : Tendsto (fun h : ℝ => p.eval (h : ℂ)) (𝓝[>] 0) (𝓝 (p.eval 0)) := by
        have : Tendsto (fun h : ℝ => p.eval (h : ℂ)) (𝓝 0) (𝓝 (p.eval ((0 : ℝ) : ℂ))) :=
          (p.continuous.comp Complex.continuous_ofReal).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      have hzero : Tendsto (fun h : ℝ => p.eval (h : ℂ)) (𝓝[>] 0) (𝓝 0) :=
        h.trans_tendsto <| ((continuous_pow (n + 1 + 1)).tendsto' 0 0 (by simp)).mono_left
          nhdsWithin_le_nhds
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact tendsto_nhds_unique hlim hzero
    -- so `p = divX p * X` and `divX p` is `O(h^{n+1})`
    have hpX : p = p.divX * Polynomial.X := by
      conv_lhs => rw [← p.divX_mul_X_add]
      rw [h0, map_zero, add_zero]
    have hdiv : (fun h : ℝ => p.divX.eval (h : ℂ)) =O[𝓝[>] 0] (fun h => h ^ (n + 1)) := by
      obtain ⟨C, hC⟩ := h.bound
      refine IsBigO.of_bound C ?_
      filter_upwards [hC, eventually_mem_nhdsWithin] with h hh (hpos : 0 < h)
      rw [hpX, Polynomial.eval_mul, Polynomial.eval_X, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hpos.le, Real.norm_of_nonneg (pow_pos hpos _).le, pow_succ,
        ← mul_assoc] at hh
      rw [Real.norm_of_nonneg (pow_pos hpos _).le]
      exact le_of_mul_le_mul_right hh hpos
    have := ih p.divX (by
      have := p.natDegree_divX_eq_natDegree_tsub_one
      omega) hdiv
    rw [hpX, this, zero_mul]
