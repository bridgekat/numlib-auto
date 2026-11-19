/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.InnerProductSpace.NormPowIteratedFDeriv

/-!
# Cartis, Gould and Toint, Appendix B: Appendix to Chapter 4

This module formalizes the part of Appendix B of [cartis2022evaluation] that belongs to Chapter 4:
Lemma B.4.1 on the derivatives of the regularization term $s \mapsto \|s\|^{p+\beta}$ on
$\mathbb{R}^n$, for $\beta \in (0, 1]$. For $j \le p$ the norm of the $j$-th derivative is
$\frac{(p+\beta)!}{(p-j+\beta)!} \|s\|^{p-j+\beta}$, where
$(k + \beta)! = \prod_{\ell=1}^k (\ell + \beta)$. The $(p+1)$-st derivative has the norm $(p+1)!$
for $\beta = 1$; for $\beta < 1$ the book's formula for it gives only its value in the radial
direction. The content is in the backbone module
`Numlib.Analysis.InnerProductSpace.NormPowIteratedFDeriv`, which works on any real inner product
space.

## Main results

* Lemma B.4.1, (B.4.1), `CartisGouldToint.AppendixB.lemma_B_4_1_i`: the norm of the $j$-th
  derivative for $j \le p$.
* Lemma B.4.1, (B.4.1), `CartisGouldToint.AppendixB.lemma_B_4_1_i_apply_le`: the corresponding bound
  on the $j$-th derivative applied to $[v]^j$.
* Lemma B.4.1, (B.4.2), `CartisGouldToint.AppendixB.lemma_B_4_1_ii`: the $j$-th derivative applied
  to $[s]^j$.
* Lemma B.4.1, (B.4.3), `CartisGouldToint.AppendixB.lemma_B_4_1_iii`: the norm of the $(p+1)$-st
  derivative for $\beta = 1$.
* Lemma B.4.1, (B.4.3), `CartisGouldToint.AppendixB.lemma_B_4_1_iii_radial`: the book's value is the
  radial value of the $(p+1)$-st derivative and a lower bound for its norm.
* Lemma B.4.1, (B.4.3), `CartisGouldToint.AppendixB.lemma_B_4_1_iii_bound`: the norm of the
  $(p+1)$-st derivative is $O(\|s\|^{\beta-1})$.
* Lemma B.4.1, (B.4.3), `CartisGouldToint.AppendixB.lemma_B_4_1_iii_false`: the printed (B.4.3) is
  false for $\beta < 1$.
* Lemma B.4.1, convexity, `CartisGouldToint.AppendixB.lemma_B_4_1_iv`: the convexity claims.

## Conventions

* $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`, and the tensor norm (A.7) is the operator norm of
  multilinear maps.
* $\nabla^j_s(\|s\|^{p+\beta})$ is `iteratedFDeriv ℝ j (fun s ↦ ‖s‖ ^ (p + β)) s`.
* $(k + \beta)!$ is `holderFactorial k β`.

## Implementation notes

* (B.4.1) and (B.4.2) hold for every $s$, including $s = 0$, as the book states.

## Deviations from the source

* **Correction.** Equation (B.4.3) is a radial lower bound in general and an equality at exponent
  one. A counterexample refutes the printed norm equality. See
  `CartisGouldToint.AppendixB.lemma_B_4_1_iii`, `CartisGouldToint.AppendixB.lemma_B_4_1_iii_radial`,
  `CartisGouldToint.AppendixB.lemma_B_4_1_iii_bound`,
  `CartisGouldToint.AppendixB.lemma_B_4_1_iii_false`.
* **Explicit differentiability range.** Lemma B.4.1 makes the derivative orders and the range at
  zero explicit in its convexity claims. See `CartisGouldToint.AppendixB.lemma_B_4_1_iv`.
* **Lemma B.4.1, (B.4.3)** (correction). The book's equality is false for $\beta \in (0, 1)$: for
  $n = 2$, $p = 1$ and $\beta = 1/2$ the norm at $s = e_1$ is at least $3/2$, while the book's value
  is $3/4$. The book's value is the radial value and a lower bound, and it is correct for
  $\beta = 1$, the only case that the book uses. See
  `CartisGouldToint.AppendixB.lemma_B_4_1_iii_false`.
* **Lemma B.4.1, convexity** (reading). The convexity claims are proved for $s \neq 0$, or for
  $s = 0$ when $j \le p$, and for derivative orders $j \le p + 1$, a range that the book leaves
  implicit. See `CartisGouldToint.AppendixB.lemma_B_4_1_iv`.
-/

open Set
open scoped Nat

namespace CartisGouldToint.AppendixB

variable {n p : ℕ} {β : ℝ}

private theorem natCast_lt_add_of_le {j : ℕ} (hβ : β ∈ Ioc (0 : ℝ) 1) (hj : j ≤ p) :
    (j : ℝ) < p + β := by
  have : (j : ℝ) ≤ p := by exact_mod_cast hj
  linarith [hβ.1]

/-- **Lemma B.4.1, (B.4.1)** of [cartis2022evaluation]. Let $\beta \in (0, 1]$, let $j \le p$, and
let $s \in \mathbb{R}^n$. Then
$$\bigl\|\nabla^j_s(\|s\|^{p+\beta})\bigr\| = \frac{(p+\beta)!}{(p-j+\beta)!}
  \|s\|^{p-j+\beta}.$$

The equality holds also at $s = 0$, as the book states. The book's proof maximizes over the
radial direction without justification; the backbone proof uses an averaging identity over the
unit ball instead. -/
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

/-- **Lemma B.4.1, (B.4.1)** of [cartis2022evaluation], applied to a vector. Let $\beta \in (0, 1]$,
let $j \le p$, and let $s, v \in \mathbb{R}^n$. Then
$$\bigl|\nabla^j_s(\|s\|^{p+\beta})[v]^j\bigr| \le \frac{(p+\beta)!}{(p-j+\beta)!}
  \|s\|^{p-j+\beta} \|v\|^j.$$
-/
theorem lemma_B_4_1_i_apply_le (hβ : β ∈ Ioc (0 : ℝ) 1) {j : ℕ} (hj : j ≤ p)
    (s v : EuclideanSpace ℝ (Fin n)) :
    |iteratedFDeriv ℝ j (fun s : EuclideanSpace ℝ (Fin n) ↦ ‖s‖ ^ ((p : ℝ) + β)) s
        (fun _ ↦ v)| ≤
      holderFactorial p β / holderFactorial (p - j) β * ‖s‖ ^ (((p - j : ℕ) : ℝ) + β) *
        ‖v‖ ^ j := by
  rw [← Real.norm_eq_abs, ← lemma_B_4_1_i hβ hj s]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans_eq ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Lemma B.4.1, (B.4.2)** of [cartis2022evaluation]. Let $\beta \in (0, 1]$, let $j \le p$, and
let $s \in \mathbb{R}^n$. Then
$$\nabla^j_s(\|s\|^{p+\beta})[s]^j = \frac{(p+\beta)!}{(p-j+\beta)!} \|s\|^{p+\beta}.$$
-/
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

/-- **Lemma B.4.1, (B.4.3)** of [cartis2022evaluation], the case $\beta = 1$. Let
$s \in \mathbb{R}^n$ with $s \neq 0$. Then the norm of $\nabla^{p+1}_s(\|s\|^{p+1})$ equals the
book's value $\beta (p+\beta)! \|s\|^{\beta-1}$ at $\beta = 1$, that is,
$$\bigl\|\nabla^{p+1}_s(\|s\|^{p+1})\bigr\| = (p+1)!.$$

For $\beta \in (0, 1)$ the equality (B.4.3) is false; see
`CartisGouldToint.AppendixB.lemma_B_4_1_iii_false`.

**Correction.** The coefficient in the source is the radial evaluation and hence a lower bound for
the derivative norm. Equality is retained at exponent one, and a dimension-dependent upper bound
supplies the same radial power in general. A counterexample refutes the unqualified equality.
-/
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

/-- **Lemma B.4.1, (B.4.3)** of [cartis2022evaluation], the radial value. Let $\beta \in \mathbb{R}$
and let $s \in \mathbb{R}^n$ with $s \neq 0$. Then the book's value is the value of the
$(p+1)$-st derivative in the radial direction,
$$\nabla^{p+1}_s(\|s\|^{p+\beta})\Bigl[\frac{s}{\|s\|}\Bigr]^{p+1} = \beta (p+\beta)!
  \|s\|^{\beta-1},$$
and therefore $\beta (p+\beta)! \|s\|^{\beta-1} \le
\bigl\|\nabla^{p+1}_s(\|s\|^{p+\beta})\bigr\|$.

This holds for every real $\beta$, without the hypothesis $\beta \in (0, 1]$.

**Correction.** The coefficient in the source is the radial evaluation and hence a lower bound for
the derivative norm. Equality is retained at exponent one, and a dimension-dependent upper bound
supplies the same radial power in general. A counterexample refutes the unqualified equality.
-/
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

/-- **Lemma B.4.1, (B.4.3)** of [cartis2022evaluation], the bound that remains true. For all
$n, p \in \mathbb{N}$ and $\beta \in \mathbb{R}$ there is a constant $C \ge 0$ with
$$\bigl\|\nabla^{p+1}_s(\|s\|^{p+\beta})\bigr\| \le C \|s\|^{\beta-1} \quad \text{for all } s
  \in \mathbb{R}^n \setminus \{0\}.$$

The constant depends on $n$, $p$ and $\beta$.

**Correction.** The coefficient in the source is the radial evaluation and hence a lower bound for
the derivative norm. Equality is retained at exponent one, and a dimension-dependent upper bound
supplies the same radial power in general. A counterexample refutes the unqualified equality.
-/
theorem lemma_B_4_1_iii_bound (n p : ℕ) (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : EuclideanSpace ℝ (Fin n), s ≠ 0 →
      ‖iteratedFDeriv ℝ (p + 1) (fun s : EuclideanSpace ℝ (Fin n) ↦ ‖s‖ ^ ((p : ℝ) + β)) s‖ ≤
        C * ‖s‖ ^ (β - 1) := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_norm_iteratedFDeriv_normRpow_le (E := EuclideanSpace ℝ (Fin n)) ((p : ℝ) + β) (p + 1)
  have he : (p : ℝ) + β - ((p + 1 : ℕ) : ℝ) = β - 1 := by push_cast; ring
  exact ⟨C, hC0, fun s hs ↦ he ▸ hC s hs⟩

/-- **Lemma B.4.1, (B.4.3)** of [cartis2022evaluation] is false for $\beta < 1$. It is not true that
for all $n, p \in \mathbb{N}$, all $\beta \in (0, 1]$ and all nonzero $s \in \mathbb{R}^n$,
$$\bigl\|\nabla^{p+1}_s(\|s\|^{p+\beta})\bigr\| = \beta (p+\beta)! \|s\|^{\beta-1}.$$

The equality fails for $n = 2$, $p = 1$, $\beta = 1/2$ and $s = e_1$: the norm is at least
$3/2$, while the right-hand side is $3/4$, because the derivative is larger in the directions
orthogonal to $s$. The counterexample needs $n \ge 2$; for $n = 1$ there is no direction
orthogonal to $s$, and the radial value is the norm. The case $n = 1$ is not formalized
separately.

**Correction.** The coefficient in the source is the radial evaluation and hence a lower bound for
the derivative norm. Equality is retained at exponent one, and a dimension-dependent upper bound
supplies the same radial power in general. A counterexample refutes the unqualified equality.
-/
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

/-- **Lemma B.4.1, convexity** of [cartis2022evaluation]. Let $\beta \in (0, 1]$, let $j \le p + 1$,
and let $s \in \mathbb{R}^n$ with $s \neq 0$ or $j \le p$. Then the map
$d \mapsto \nabla^j_s(\|s\|^{p+\beta})[d]^j$ is convex on the orthogonal complement of $s$. If
moreover $j$ is even, then the map $t \mapsto \nabla^j_s(\|s\|^{p+\beta})[ts]^j$ is convex on
$\mathbb{R}$.

**Reading.** The book leaves the range of $j$ and the case $s = 0$ implicit. The claims are
proved for $j \le p + 1$ and $s \neq 0$, and for $s = 0$ only when $j \le p$, where the
derivative vanishes.

**Reading.** The convexity claims concern orders through p plus one, and include zero only through
order p.
-/
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
