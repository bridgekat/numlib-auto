/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Lp.PiLp` (the factor inclusions) and
`Mathlib.Analysis.Normed.Module.Dual` (the dual norm).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# The dual of a finite `ℓ^p` product

The continuous linear inclusions of the factors of a finite `ℓ^p` product `PiLp p X` and the
description of its dual: a functional is the sum of its restrictions to the factors, and its
norm is the `ℓ^q` norm of the tuple of the norms of those restrictions, `q` the conjugate
exponent.

## Main definitions and statements

* `PiLp.singleL p i : X i →L[ℝ] PiLp p X`, the inclusion of the `i`-th factor, with
  `PiLp.singleL_apply` (it is `PiLp.single p i`), `PiLp.norm_singleL_apply` (isometric),
  `PiLp.norm_singleL_le` and `PiLp.sum_singleL_apply` (every element is the sum of its
  coordinates).
* `PiLp.strongDual_apply_eq_sum`: `Φ x = ∑ i, (Φ ∘ singleL p i) (x i)` for a functional `Φ` on
  the product, and `PiLp.norm_strongDual_comp_singleL_le`: `‖Φ ∘ singleL p i‖ ≤ ‖Φ‖`.
* `PiLp.norm_strongDual_eq`: for `1 ≤ p < ∞` and `q` the conjugate exponent,
  `‖Φ‖ = ‖(‖Φ ∘ singleL p i‖)_i‖_{ℓ^q}` — the dual of `PiLp p X` is the `ℓ^q` product of the
  duals, isometrically. The upper bound is Hölder's inequality for finite sums and the lower
  bound tests `Φ` against almost extremal vectors of the factors.
* `PiLp.norm_eq_norm_toLp_norm`: the norm of an element of `PiLp q X` is the norm of the real
  tuple of the norms of its coordinates.

## Design

The scalar field is `ℝ` throughout: the consumers are the duals of the real Sobolev spaces
(`W^{-1,p'}(I)` and `W^{-1,p'}(Ω)`, [brezis2011functional] Propositions 8.14 and 9.20, Remark 21
of chapter 8), where the functional on `W^{1,p}` is extended to a finite `ℓ^p` product of copies
of `L^p` and represented factor by factor. The extremal argument of `norm_strongDual_eq` uses
that a real scalar of modulus one makes `Φ x` nonnegative; over `RCLike` the same proof goes
through with `(Φ x)⁻¹ • |Φ x|`.
-/

open scoped ENNReal

noncomputable section

namespace PiLp

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*} [∀ i, NormedAddCommGroup (X i)]
  [∀ i, NormedSpace ℝ (X i)] {p : ℝ≥0∞}

variable (p) in
/-- The inclusion of the `i`-th factor into the `ℓ^p` product, as a continuous linear map. -/
def singleL (i : ι) : X i →L[ℝ] PiLp p X :=
  (continuousLinearEquiv p ℝ X).symm.toContinuousLinearMap.comp (ContinuousLinearMap.single ℝ X i)

/-- `singleL p i b` is `PiLp.single p i b`. -/
theorem singleL_apply (i : ι) (b : X i) : singleL p i b = single p i b := rfl

variable [Fintype ι] [Fact (1 ≤ p)]

/-- The inclusion of a factor is isometric. -/
theorem norm_singleL_apply (i : ι) (b : X i) : ‖singleL p i b‖ = ‖b‖ := by
  rw [singleL_apply, norm_single]

/-- The inclusion of a factor has norm at most `1`. -/
theorem norm_singleL_le (i : ι) : ‖singleL p (X := X) i‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun b ↦ by
    rw [norm_singleL_apply, one_mul]

omit [Fact (1 ≤ p)] in
/-- Every element of the product is the sum of its coordinates. -/
theorem sum_singleL_apply (x : PiLp p X) : ∑ i, singleL p i (x i) = x := by
  refine (continuousLinearEquiv p ℝ X).injective ?_
  rw [map_sum]
  simp only [singleL, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.single_apply]
  exact Finset.univ_sum_single _

omit [Fact (1 ≤ p)] in
/-- A functional on the product is the sum of its restrictions to the factors. -/
theorem strongDual_apply_eq_sum (Φ : StrongDual ℝ (PiLp p X)) (x : PiLp p X) :
    Φ x = ∑ i, Φ.comp (singleL p i) (x i) := by
  conv_lhs => rw [← sum_singleL_apply x]
  rw [map_sum]
  rfl

/-- The restriction of a functional to a factor has norm at most that of the functional. -/
theorem norm_strongDual_comp_singleL_le (Φ : StrongDual ℝ (PiLp p X)) (i : ι) :
    ‖Φ.comp (singleL p i)‖ ≤ ‖Φ‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_left (norm_singleL_le (p := p) i) (norm_nonneg Φ))

/-- **The dual of a finite `ℓ^p` product, `1 ≤ p < ∞`**: the norm of a functional `Φ` on
`PiLp p X` is the `ℓ^q` norm of the tuple of the norms of its restrictions `Φ ∘ single i` to the
factors, `q` the conjugate exponent — `(∑ ‖Φ ∘ single i‖^q)^{1/q}` for `1 < p < ∞`,
`max ‖Φ ∘ single i‖` for `p = 1`. The upper bound is Hölder's inequality for finite sums; the
lower bound tests `Φ` against `(‖Φ ∘ single i‖^{q - 1} y i)_i` with `y i` almost extremal for
`Φ ∘ single i`. -/
theorem norm_strongDual_eq {q : ℝ≥0∞} [ENNReal.HolderConjugate p q] (hp : p ≠ ⊤)
    (Φ : StrongDual ℝ (PiLp p X)) :
    ‖Φ‖ = ‖(WithLp.toLp q fun i ↦ ‖Φ.comp (singleL p i)‖ : PiLp q fun _ : ι ↦ ℝ)‖ := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ∀ i, StrongDual ℝ (X i), ∀ i, ψ i = Φ.comp (singleL p i) :=
    ⟨_, fun _ ↦ rfl⟩
  have hψle : ∀ i, ‖ψ i‖ ≤ ‖Φ‖ := fun i ↦ by rw [hψ]; exact norm_strongDual_comp_singleL_le Φ i
  have hΦx : ∀ x : PiLp p X, Φ x = ∑ i, ψ i (x i) := fun x ↦ by
    simp only [hψ]; exact strongDual_apply_eq_sum Φ x
  have hnorm : ∀ i, ‖(‖ψ i‖)‖ = ‖ψ i‖ := fun i ↦ Real.norm_of_nonneg (norm_nonneg _)
  simp only [← hψ]
  rcases eq_or_ne q ⊤ with rfl | hq
  · -- `p = 1`: the sup norm of the tuple
    have hp1 : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ⊤ p).1 rfl
    subst hp1
    rw [norm_eq_ciSup]
    simp only [hnorm]
    rcases isEmpty_or_nonempty ι with hι | hι
    · rw [Real.iSup_of_isEmpty]
      refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ le_rfl fun x ↦ ?_) (norm_nonneg _)
      rw [hΦx, Finset.univ_eq_empty, Finset.sum_empty, norm_zero, zero_mul]
    refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (Real.iSup_nonneg fun i ↦
      norm_nonneg _) fun x ↦ ?_) (ciSup_le hψle)
    rw [hΦx, norm_eq_sum (by simp)]
    simp only [ENNReal.toReal_one, Real.rpow_one, div_one]
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    refine ((ψ i).le_opNorm (x i)).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact le_ciSup (Finite.bddAbove_range fun i ↦ ‖ψ i‖) i
  · -- `1 < p < ∞`
    have hpq := ENNReal.HolderConjugate.toReal_of_ne_top hp hq (p := p) (q := q)
    have hqp := hpq.symm
    obtain ⟨P, hP⟩ : ∃ P : ℝ, P = p.toReal := ⟨_, rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = q.toReal := ⟨_, rfl⟩
    rw [← hP, ← hQ] at hpq hqp
    have hP1 : 1 < P := hpq.lt
    have hQ1 : 1 < Q := hqp.lt
    have hP0 : 0 < P := zero_lt_one.trans hP1
    have hQ0 : 0 < Q := zero_lt_one.trans hQ1
    rw [norm_eq_sum (by rw [← hQ]; exact hQ0), ← hQ]
    simp only [hnorm]
    obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ i, ‖ψ i‖ ^ Q := ⟨_, rfl⟩
    have hS0 : 0 ≤ S := hS ▸ Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _
    rw [← hS]
    refine le_antisymm ?_ ?_
    · -- Hölder's inequality
      refine ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg hS0 _) fun x ↦ ?_
      rw [hΦx, norm_eq_sum (by rw [← hP]; exact hP0), ← hP, hS]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ ↦ (ψ i).le_opNorm (x i)).trans ?_
      have := Real.inner_le_Lp_mul_Lq Finset.univ (fun i ↦ ‖ψ i‖) (fun i ↦ ‖x i‖) hqp
      simpa only [abs_norm] using this
    · -- the extremal argument
      rcases hS0.eq_or_lt with hS0' | hSpos
      · rw [← hS0', Real.zero_rpow (by positivity)]
        exact norm_nonneg _
      obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ i, ‖ψ i‖ ^ (Q - 1) := ⟨_, rfl⟩
      have hT0 : 0 ≤ T := hT ▸ Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _
      have hSP : 0 < S ^ (1 / P) := Real.rpow_pos_of_pos hSpos _
      -- the key estimate: `S - δ T ≤ ‖Φ‖ S^{1/P}` for every `δ > 0`
      have key : ∀ δ : ℝ, 0 < δ → S - δ * T ≤ ‖Φ‖ * S ^ (1 / P) := by
        intro δ hδ
        -- almost extremal vectors for the `ψ i`
        have hy : ∀ i, ∃ y : X i, ‖y‖ ≤ 1 ∧ ‖ψ i‖ - δ ≤ ψ i y := by
          intro i
          rcases eq_or_ne (ψ i) 0 with h0 | h0
          · exact ⟨0, by simp, by rw [h0]; simp; linarith⟩
          obtain ⟨x, hx1, hx2⟩ := (ψ i).exists_lt_apply_of_lt_opNorm (r := ‖ψ i‖ - δ)
            (by linarith)
          obtain ⟨c, hc1, hc2⟩ : ∃ c : ℝ, |c| = 1 ∧ c * ψ i x = ‖ψ i x‖ := by
            rcases le_or_gt 0 (ψ i x) with h | h
            · exact ⟨1, abs_one, by rw [one_mul, Real.norm_of_nonneg h]⟩
            · exact ⟨-1, by rw [abs_neg, abs_one], by rw [neg_one_mul, Real.norm_of_nonpos h.le]⟩
          refine ⟨c • x, ?_, ?_⟩
          · rw [norm_smul, Real.norm_eq_abs, hc1, one_mul]; exact hx1.le
          · rw [map_smul, smul_eq_mul, hc2]; exact hx2.le
        choose y hy1 hy2 using hy
        obtain ⟨x, hx⟩ : ∃ x : PiLp p X, x = WithLp.toLp p fun i ↦ ‖ψ i‖ ^ (Q - 1) • y i :=
          ⟨_, rfl⟩
        have hxi : ∀ i, x i = ‖ψ i‖ ^ (Q - 1) • y i := fun i ↦ by rw [hx]
        -- `Φ x ≥ S - δ T`
        have hlow : S - δ * T ≤ Φ x := by
          rw [hΦx, hS, hT, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rw [hxi, map_smul, smul_eq_mul]
          have e : ‖ψ i‖ ^ Q = ‖ψ i‖ ^ (Q - 1) * ‖ψ i‖ := by
            rw [← Real.rpow_add_one' (norm_nonneg _) (by linarith), sub_add_cancel]
          rw [e]
          nlinarith [hy2 i, Real.rpow_nonneg (norm_nonneg (ψ i)) (Q - 1)]
        -- `‖x‖ ≤ S^{1/P}`
        have hup : ‖x‖ ≤ S ^ (1 / P) := by
          rw [norm_eq_sum (by rw [← hP]; exact hP0), ← hP, hS]
          refine Real.rpow_le_rpow (Finset.sum_nonneg fun i _ ↦ by positivity)
            (Finset.sum_le_sum fun i _ ↦ ?_) (by positivity)
          rw [hxi, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
            Real.mul_rpow (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _),
            ← Real.rpow_mul (norm_nonneg _), hqp.sub_one_mul_conj]
          exact mul_le_of_le_one_right (Real.rpow_nonneg (norm_nonneg _) _)
            (Real.rpow_le_one (norm_nonneg _) (hy1 i) hP0.le)
        calc S - δ * T ≤ Φ x := hlow
          _ ≤ ‖Φ x‖ := le_abs_self _
          _ ≤ ‖Φ‖ * ‖x‖ := Φ.le_opNorm x
          _ ≤ ‖Φ‖ * S ^ (1 / P) := mul_le_mul_of_nonneg_left hup (norm_nonneg _)
      -- let `δ → 0`
      have hSle : S ≤ ‖Φ‖ * S ^ (1 / P) := by
        rcases hT0.eq_or_lt with hT0' | hTpos
        · have := key 1 one_pos
          rwa [← hT0', mul_zero, sub_zero] at this
        refine le_of_forall_pos_le_add fun ε hε ↦ ?_
        have := key (ε / T) (div_pos hε hTpos)
        rwa [div_mul_cancel₀ _ hTpos.ne', sub_le_iff_le_add] at this
      -- `S^{1/Q} = S / S^{1/P}`
      have hexp : S ^ (1 / Q) = S / S ^ (1 / P) := by
        rw [one_div, one_div, ← hpq.one_sub_inv, Real.rpow_sub hSpos, Real.rpow_one]
      rw [hexp, div_le_iff₀ hSP]
      exact hSle

omit [DecidableEq ι] [∀ i, NormedSpace ℝ (X i)] in
/-- The norm of an element of a finite `ℓ^p` product is the norm of the real tuple of the norms
of its coordinates. -/
theorem norm_eq_norm_toLp_norm (x : PiLp p X) :
    ‖x‖ = ‖(WithLp.toLp p fun i ↦ ‖x i‖ : PiLp p fun _ : ι ↦ ℝ)‖ := by
  rcases eq_or_ne p ⊤ with rfl | hp
  · simp only [PiLp.norm_eq_ciSup, norm_norm]
  · have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp
    simp only [PiLp.norm_eq_sum hp0, norm_norm]

end PiLp

end
