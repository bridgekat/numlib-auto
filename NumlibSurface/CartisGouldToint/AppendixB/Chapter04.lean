import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.InnerProductSpace.NormPowIteratedFDeriv

/-!
# Cartis–Gould–Toint, Appendix B: Appendix to Chapter 4

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], Appendix B, "Appendix to
Chapter 4": Lemma B.4.1 on the derivatives of the regularization term `‖s‖^{p+β}`,
`β ∈ (0, 1]`, on `ℝⁿ = EuclideanSpace ℝ (Fin n)`. The tensor norm (A.7) is the operator norm of
multilinear maps, `∇^j_s(‖s‖^{p+β})` is `iteratedFDeriv ℝ j (fun s ↦ ‖s‖ ^ (p + β)) s`, and
`(k + β)! = ∏_{ℓ=1}^k (ℓ + β)` is `holderFactorial k β`. The content is in the backbone module
`Numlib.Analysis.InnerProductSpace.NormPowIteratedFDeriv` (on any real inner product space).

## Main results

* `lemma_B_4_1_i` — (B.4.1), with the diagonal form `lemma_B_4_1_i_apply_le`.
* `lemma_B_4_1_ii` — (B.4.2).
* `lemma_B_4_1_iii` — (B.4.3) for `β = 1`; `lemma_B_4_1_iii_radial` and
  `lemma_B_4_1_iii_bound` — what remains true for `β ∈ (0, 1)`; `lemma_B_4_1_iii_false` — the
  printed (B.4.3) is false for `β < 1`.
* `lemma_B_4_1_iv` — the convexity claims.

## Deviations from the book

* **(B.4.3) is false for `β ∈ (0, 1)`**: for `n = 2`, `p = 1`, `β = 1/2` and `s = e₁` the norm of
  `∇²_s ‖s‖^{3/2}` is at least `3/2`, while the book's value is `β (p+β)! ‖s‖^{β-1} = 3/4`
  (`lemma_B_4_1_iii_false`): the derivative is larger in directions orthogonal to `s`. The book's
  value is the radial value and a lower bound (`lemma_B_4_1_iii_radial`), and the norm is
  `O(‖s‖^{β-1})` (`lemma_B_4_1_iii_bound`). For `β = 1`, the only case used in the book, (B.4.3)
  holds (`lemma_B_4_1_iii`). The counterexample needs `n ≥ 2`: for `n = 1` there is no direction
  orthogonal to `s` and the radial value is the norm (this case is not formalized separately).
* (B.4.1) and (B.4.2) hold for every `s`, including `s = 0`, as the book states. The convexity
  claims are proved for `s ≠ 0` (for `s = 0` only for `j ≤ p`, where the derivative vanishes) and
  for derivative orders `j ≤ p + 1`, a range the book leaves implicit.
* The book's proof of (B.4.1) maximizes over the radial direction without justification; the
  backbone uses an averaging identity over the unit ball instead.
-/

open Set
open scoped Nat

namespace CartisGouldToint.AppendixB

variable {n p : ℕ} {β : ℝ}

private theorem natCast_lt_add_of_le {j : ℕ} (hβ : β ∈ Ioc (0 : ℝ) 1) (hj : j ≤ p) :
    (j : ℝ) < p + β := by
  have : (j : ℝ) ≤ p := by exact_mod_cast hj
  linarith [hβ.1]

/-- **Lemma B.4.1, (B.4.1)** of [cartis2022evaluation]. For `β ∈ (0, 1]`, `j ∈ [0 : p]` and every
`s ∈ ℝⁿ`, `‖∇^j_s(‖s‖^{p+β})‖ = (p+β)!/(p-j+β)! ‖s‖^{p-j+β}`. -/
theorem lemma_B_4_1_i (hβ : β ∈ Ioc (0 : ℝ) 1) {j : ℕ} (hj : j ≤ p)
    (s : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j (fun s : EuclideanSpace ℝ (Fin n) ↦ ‖s‖ ^ ((p : ℝ) + β)) s‖ =
      holderFactorial p β / holderFactorial (p - j) β * ‖s‖ ^ (((p - j : ℕ) : ℝ) + β) := by
  have hjl := natCast_lt_add_of_le hβ hj
  have hexp : ((p - j : ℕ) : ℝ) + β = (p : ℝ) + β - j := by
    push_cast [Nat.cast_sub hj]; ring
  rw [holderFactorial_div_holderFactorial_sub hj (by linarith [hβ.1]), hexp]
  rcases eq_or_ne s 0 with rfl | hs
  · rw [iteratedFDeriv_normRpow_zero hjl, norm_zero, norm_zero, Real.zero_rpow (by linarith),
      mul_zero]
  · exact norm_iteratedFDeriv_normRpow hjl.le hs

/-- **Lemma B.4.1, (B.4.1)**, diagonal form ([cartis2022evaluation]): for `β ∈ (0, 1]`,
`j ∈ [0 : p]` and `s, v ∈ ℝⁿ`,
`|∇^j_s(‖s‖^{p+β})[v]^j| ≤ (p+β)!/(p-j+β)! ‖s‖^{p-j+β} ‖v‖^j`. -/
theorem lemma_B_4_1_i_apply_le (hβ : β ∈ Ioc (0 : ℝ) 1) {j : ℕ} (hj : j ≤ p)
    (s v : EuclideanSpace ℝ (Fin n)) :
    |iteratedFDeriv ℝ j (fun s : EuclideanSpace ℝ (Fin n) ↦ ‖s‖ ^ ((p : ℝ) + β)) s
        (fun _ ↦ v)| ≤
      holderFactorial p β / holderFactorial (p - j) β * ‖s‖ ^ (((p - j : ℕ) : ℝ) + β) *
        ‖v‖ ^ j := by
  rw [← Real.norm_eq_abs, ← lemma_B_4_1_i hβ hj s]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans_eq ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Lemma B.4.1, (B.4.2)** of [cartis2022evaluation]. For `β ∈ (0, 1]`, `j ∈ [0 : p]` and every
`s ∈ ℝⁿ`, `∇^j_s(‖s‖^{p+β})[s]^j = (p+β)!/(p-j+β)! ‖s‖^{p+β}`. -/
theorem lemma_B_4_1_ii (hβ : β ∈ Ioc (0 : ℝ) 1) {j : ℕ} (hj : j ≤ p)
    (s : EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ j (fun s : EuclideanSpace ℝ (Fin n) ↦ ‖s‖ ^ ((p : ℝ) + β)) s (fun _ ↦ s) =
      holderFactorial p β / holderFactorial (p - j) β * ‖s‖ ^ ((p : ℝ) + β) := by
  rw [holderFactorial_div_holderFactorial_sub hj (by linarith [hβ.1])]
  rcases eq_or_ne s 0 with rfl | hs
  · rw [iteratedFDeriv_normRpow_zero (natCast_lt_add_of_le hβ hj), norm_zero,
      Real.zero_rpow (by linarith [hβ.1]), mul_zero]
    rfl
  · exact iteratedFDeriv_normRpow_apply_self _ j hs

@[deprecated _root_.prod_fin_succ_eq_mul_holderFactorial (since := "2026-10-26")]
alias prod_fin_succ_eq_mul_holderFactorial := _root_.prod_fin_succ_eq_mul_holderFactorial

/-- **Lemma B.4.1, (B.4.3)** of [cartis2022evaluation], for `β = 1`: for `s ≠ 0`,
`‖∇^{p+1}_s(‖s‖^{p+β})‖ = β (p+β)! ‖s‖^{β-1}` with `β = 1`, that is,
`‖∇^{p+1}_s ‖s‖^{p+1}‖ = (p+1)!`. For `β ∈ (0, 1)` the equality is false
(`lemma_B_4_1_iii_false`). -/
theorem lemma_B_4_1_iii {s : EuclideanSpace ℝ (Fin n)} (hs : s ≠ 0) :
    ‖iteratedFDeriv ℝ (p + 1) (fun s : EuclideanSpace ℝ (Fin n) ↦ ‖s‖ ^ ((p : ℝ) + 1)) s‖ =
        1 * holderFactorial p 1 * ‖s‖ ^ ((1 : ℝ) - 1) ∧
      ‖iteratedFDeriv ℝ (p + 1) (fun s : EuclideanSpace ℝ (Fin n) ↦ ‖s‖ ^ ((p : ℝ) + 1)) s‖ =
        ((p + 1)! : ℝ) := by
  have h := norm_iteratedFDeriv_normRpow (lam := (p : ℝ) + 1) (j := p + 1) (by push_cast; rfl) hs
  rw [← Fin.prod_univ_eq_prod_range (fun i ↦ (p : ℝ) + 1 - i),
    _root_.prod_fin_succ_eq_mul_holderFactorial] at h
  have he : (p : ℝ) + 1 - ((p + 1 : ℕ) : ℝ) = 1 - 1 := by push_cast; ring
  rw [he] at h
  refine ⟨h, ?_⟩
  rw [h, sub_self, Real.rpow_zero, mul_one, one_mul, holderFactorial_one_right]

/-- **Lemma B.4.1, (B.4.3)**, what holds for every `β ∈ (0, 1]` ([cartis2022evaluation]): for
`s ≠ 0`, the book's value `β (p+β)! ‖s‖^{β-1}` is the radial value
`∇^{p+1}_s(‖s‖^{p+β})[s/‖s‖]^{p+1}`, hence a lower bound for the norm
`‖∇^{p+1}_s(‖s‖^{p+β})‖`. -/
theorem lemma_B_4_1_iii_radial (β : ℝ) {s : EuclideanSpace ℝ (Fin n)} (hs : s ≠ 0) :
    iteratedFDeriv ℝ (p + 1) (fun s : EuclideanSpace ℝ (Fin n) ↦ ‖s‖ ^ ((p : ℝ) + β)) s
        (fun _ ↦ ‖s‖⁻¹ • s) = β * holderFactorial p β * ‖s‖ ^ (β - 1) ∧
      β * holderFactorial p β * ‖s‖ ^ (β - 1) ≤
        ‖iteratedFDeriv ℝ (p + 1) (fun s : EuclideanSpace ℝ (Fin n) ↦ ‖s‖ ^ ((p : ℝ) + β)) s‖ := by
  have h := iteratedFDeriv_normRpow_apply_unit ((p : ℝ) + β) (p + 1) hs
  have he : (p : ℝ) + β - ((p + 1 : ℕ) : ℝ) = β - 1 := by push_cast; ring
  rw [_root_.prod_fin_succ_eq_mul_holderFactorial, he] at h
  refine ⟨h, ?_⟩
  rw [← h]
  refine (le_abs_self _).trans ?_
  rw [← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans_eq ?_
  have hnx : 0 < ‖s‖ := norm_pos_iff.2 hs
  simp [norm_smul, inv_mul_cancel₀ hnx.ne']

/-- **Lemma B.4.1, (B.4.3)**, the bound that holds for every `β` ([cartis2022evaluation]): there
is a constant `C ≥ 0` (depending on `n`, `p`, `β`) with
`‖∇^{p+1}_s(‖s‖^{p+β})‖ ≤ C ‖s‖^{β-1}` for all `s ≠ 0`. -/
theorem lemma_B_4_1_iii_bound (n p : ℕ) (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : EuclideanSpace ℝ (Fin n), s ≠ 0 →
      ‖iteratedFDeriv ℝ (p + 1) (fun s : EuclideanSpace ℝ (Fin n) ↦ ‖s‖ ^ ((p : ℝ) + β)) s‖ ≤
        C * ‖s‖ ^ (β - 1) := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_norm_iteratedFDeriv_normRpow_le (E := EuclideanSpace ℝ (Fin n)) ((p : ℝ) + β) (p + 1)
  have he : (p : ℝ) + β - ((p + 1 : ℕ) : ℝ) = β - 1 := by push_cast; ring
  exact ⟨C, hC0, fun s hs ↦ he ▸ hC s hs⟩

/-- **(B.4.3) of [cartis2022evaluation] is false for `β < 1`.** It is not true that for all `n`,
`p`, `β ∈ (0, 1]` and `s ≠ 0` in `ℝⁿ`, `‖∇^{p+1}_s(‖s‖^{p+β})‖ = β (p+β)! ‖s‖^{β-1}`: it fails
for `n = 2`, `p = 1`, `β = 1/2`, `s = e₁`. -/
theorem lemma_B_4_1_iii_false :
    ¬ ∀ (n p : ℕ) (β : ℝ), β ∈ Ioc (0 : ℝ) 1 → ∀ s : EuclideanSpace ℝ (Fin n), s ≠ 0 →
      ‖iteratedFDeriv ℝ (p + 1) (fun s : EuclideanSpace ℝ (Fin n) ↦ ‖s‖ ^ ((p : ℝ) + β)) s‖ =
        β * holderFactorial p β * ‖s‖ ^ (β - 1) := by
  intro h
  have hs : (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
    intro h0
    have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0) h0
    simp at this
  have h1 := h 2 1 (1 / 2) ⟨by norm_num, by norm_num⟩ _ hs
  have h3 : ((1 : ℕ) : ℝ) + 1 / 2 = 3 / 2 := by norm_num
  rw [h3] at h1
  exact not_norm_iteratedFDeriv_normRpow_eq_radial.ne' h1

/-- **Lemma B.4.1, convexity** ([cartis2022evaluation]). For `β ∈ (0, 1]`, `j ≤ p + 1` and
`s ≠ 0` (or `j ≤ p`), `d ↦ ∇^j_s(‖s‖^{p+β})[d]^j` is convex on the orthogonal complement of `s`,
and for even `j`, `t ↦ ∇^j_s(‖s‖^{p+β})[t s]^j` is convex on `ℝ`. -/
theorem lemma_B_4_1_iv (hβ : β ∈ Ioc (0 : ℝ) 1) {j : ℕ} (hj : j ≤ p + 1)
    {s : EuclideanSpace ℝ (Fin n)} (hs : s ≠ 0 ∨ j ≤ p) :
    ConvexOn ℝ ((ℝ ∙ s)ᗮ : Set (EuclideanSpace ℝ (Fin n)))
        (fun d ↦ iteratedFDeriv ℝ j
          (fun s : EuclideanSpace ℝ (Fin n) ↦ ‖s‖ ^ ((p : ℝ) + β)) s (fun _ ↦ d)) ∧
      (Even j → ConvexOn ℝ univ (fun t : ℝ ↦ iteratedFDeriv ℝ j
          (fun s : EuclideanSpace ℝ (Fin n) ↦ ‖s‖ ^ ((p : ℝ) + β)) s (fun _ ↦ t • s))) := by
  have hj' : (j : ℝ) ≤ p + 1 := by exact_mod_cast hj
  rcases eq_or_ne s 0 with rfl | hs0
  · have hjp := hs.resolve_left (not_not.2 rfl)
    rw [iteratedFDeriv_normRpow_zero (natCast_lt_add_of_le hβ hjp)]
    exact ⟨convexOn_const 0 (Submodule.convex _), fun _ ↦ convexOn_const 0 convex_univ⟩
  · obtain ⟨h1, h2⟩ := convexOn_iteratedFDeriv_normRpow (lam := (p : ℝ) + β) (j := j)
      (by linarith [hβ.1]) hs0
    exact ⟨h1, fun he ↦ h2 he (by linarith [hβ.1])⟩

end CartisGouldToint.AppendixB
