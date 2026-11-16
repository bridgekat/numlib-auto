/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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
# The dual of a finite $\ell^p$ product

Let $X_i$, $i \in \iota$, be finitely many real normed spaces, and let $1 \le p \le \infty$. This
module defines the continuous linear inclusions $\iota_i : X_i \to$ `PiLp p X` of the factors into
the $\ell^p$ product and describes the dual of the product. A continuous linear functional $\Phi$ on
the product is the sum of its restrictions $\Phi \circ \iota_i$ to the factors. For
$1 \le p < \infty$ its norm is
$$\|\Phi\| = \big\| (\|\Phi \circ \iota_i\|)_{i \in \iota} \big\|_q,$$
the $\ell^q$ norm of the norms of the restrictions, where $q$ is the conjugate exponent. So the dual
of the $\ell^p$ product is isometrically the $\ell^q$ product of the duals.

## Main definitions

* `PiLp.singleL`: the inclusion $\iota_i$ of the $i$-th factor, as a continuous linear map.

## Main results

* `PiLp.singleL_apply`, `PiLp.norm_singleL_apply`, `PiLp.norm_singleL_le`: $\iota_i$ is
  `PiLp.single p i`, it is isometric, and its norm is at most $1$.
* `PiLp.sum_singleL_apply`: every element is the sum of its coordinates, $x = \sum_i \iota_i(x_i)$.
* `PiLp.strongDual_apply_eq_sum`, `PiLp.norm_strongDual_comp_singleL_le`:
  $\Phi(x) = \sum_i (\Phi \circ \iota_i)(x_i)$, and $\|\Phi \circ \iota_i\| \le \|\Phi\|$.
* `PiLp.norm_strongDual_eq`: for $1 \le p < \infty$,
  $\|\Phi\| = \| (\|\Phi \circ \iota_i\|)_i \|_q$.
* `PiLp.norm_eq_norm_toLp_norm`: the norm of an element of the product is the $\ell^p$ norm of the
  real vector of the norms of its coordinates.

## Proof outline

The upper bound for $\|\Phi\|$ is Hölder's inequality for finite sums. The lower bound tests $\Phi$
against vectors whose coordinates are almost extremal for the restrictions $\Phi \circ \iota_i$.

## Implementation notes

* The scalar field is $\mathbb{R}$ throughout. The results serve the duals of the real Sobolev
  spaces, $W^{-1,p'}(I)$ and $W^{-1,p'}(\Omega)$ ([brezis2011functional], Propositions 8.14 and
  9.20, and Remark 21 of Chapter 8): there a functional on $W^{1,p}$ is extended to a finite
  $\ell^p$ product of copies of $L^p$ and represented factor by factor.
* The extremal argument of `PiLp.norm_strongDual_eq` uses that a real scalar of modulus one makes
  $\Phi(x)$ nonnegative. Over `RCLike` the same proof goes through with the scalar
  $|\Phi(x)| / \Phi(x)$.
-/

open scoped ENNReal

noncomputable section

namespace PiLp

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*} [∀ i, NormedAddCommGroup (X i)]
  [∀ i, NormedSpace ℝ (X i)] {p : ℝ≥0∞}

variable (p) in
/-- The inclusion $\iota_i : X_i \to$ `PiLp p X` of the $i$-th factor into the $\ell^p$ product, as
a continuous linear map: $\iota_i(b)$ has the coordinate $b$ at $i$ and $0$ at every other
index. -/
def singleL (i : ι) : X i →L[ℝ] PiLp p X :=
  (continuousLinearEquiv p ℝ X).symm.toContinuousLinearMap.comp (ContinuousLinearMap.single ℝ X i)

/-- The inclusion $\iota_i$ of the $i$-th factor maps $b \in X_i$ to `PiLp.single p i b`. -/
theorem singleL_apply (i : ι) (b : X i) : singleL p i b = single p i b := rfl

variable [Fintype ι] [Fact (1 ≤ p)]

/-- Let the index set be finite and $1 \le p \le \infty$. The inclusion of a factor is isometric:
$$\|\iota_i(b)\| = \|b\|.$$
-/
theorem norm_singleL_apply (i : ι) (b : X i) : ‖singleL p i b‖ = ‖b‖ := by
  rw [singleL_apply, norm_single]

/-- Let the index set be finite and $1 \le p \le \infty$. The inclusion $\iota_i$ of a factor has
operator norm $\|\iota_i\| \le 1$. -/
theorem norm_singleL_le (i : ι) : ‖singleL p (X := X) i‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun b ↦ by
    rw [norm_singleL_apply, one_mul]

omit [Fact (1 ≤ p)] in
/-- Every element $x$ of a finite $\ell^p$ product is the sum of its coordinates:
$$x = \sum_i \iota_i(x_i).$$
-/
theorem sum_singleL_apply (x : PiLp p X) : ∑ i, singleL p i (x i) = x := by
  refine (continuousLinearEquiv p ℝ X).injective ?_
  rw [map_sum]
  simp only [singleL, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.single_apply]
  exact Finset.univ_sum_single _

omit [Fact (1 ≤ p)] in
/-- A continuous linear functional $\Phi$ on a finite $\ell^p$ product is the sum of its
restrictions to the factors: for every $x$,
$$\Phi(x) = \sum_i (\Phi \circ \iota_i)(x_i).$$
-/
theorem strongDual_apply_eq_sum (Φ : StrongDual ℝ (PiLp p X)) (x : PiLp p X) :
    Φ x = ∑ i, Φ.comp (singleL p i) (x i) := by
  conv_lhs => rw [← sum_singleL_apply x]
  rw [map_sum]
  rfl

/-- Let the index set be finite and $1 \le p \le \infty$. The restriction of a continuous linear
functional $\Phi$ on the $\ell^p$ product to a factor has no larger norm:
$$\|\Phi \circ \iota_i\| \le \|\Phi\|.$$
-/
theorem norm_strongDual_comp_singleL_le (Φ : StrongDual ℝ (PiLp p X)) (i : ι) :
    ‖Φ.comp (singleL p i)‖ ≤ ‖Φ‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_left (norm_singleL_le (p := p) i) (norm_nonneg Φ))

/-- **The dual of a finite $\ell^p$ product.** Let $X_i$, $i \in \iota$, be finitely many real
normed spaces, let $1 \le p < \infty$, and let $q$ be the conjugate exponent, $1/p + 1/q = 1$.
For every continuous linear functional $\Phi$ on `PiLp p X`,
$$\|\Phi\| = \big\| (\|\Phi \circ \iota_i\|)_{i \in \iota} \big\|_q.$$
That is, $\|\Phi\| = (\sum_i \|\Phi \circ \iota_i\|^q)^{1/q}$ for $1 < p < \infty$, and
$\|\Phi\| = \max_i \|\Phi \circ \iota_i\|$ for $p = 1$.

The upper bound is Hölder's inequality for finite sums. The lower bound tests $\Phi$ against
$(\|\Phi \circ \iota_i\|^{q-1} y_i)_i$, with $y_i$ almost extremal for $\Phi \circ \iota_i$. -/
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
/-- Let $1 \le p \le \infty$. The norm of an element $x$ of a finite $\ell^p$ product is the
$\ell^p$ norm of the real vector $(\|x_i\|)_i$ of the norms of its coordinates:
$$\|x\| = \big\| (\|x_i\|)_i \big\|_p.$$
-/
theorem norm_eq_norm_toLp_norm (x : PiLp p X) :
    ‖x‖ = ‖(WithLp.toLp p fun i ↦ ‖x i‖ : PiLp p fun _ : ι ↦ ℝ)‖ := by
  rcases eq_or_ne p ⊤ with rfl | hp
  · simp only [PiLp.norm_eq_ciSup, norm_norm]
  · have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp
    simp only [PiLp.norm_eq_sum hp0, norm_norm]

end PiLp

end
