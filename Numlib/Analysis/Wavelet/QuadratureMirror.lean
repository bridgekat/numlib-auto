/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.OrthonormalSeries
import Numlib.Analysis.MeanInequalities

/-!
# Quadrature mirror filters and the two-channel decomposition

A **quadrature mirror filter** is a real sequence $p = (p_k)_{k \in \mathbb{Z}}$ with
$$\sum_{k \in \mathbb{Z}} p_k\, p_{k-2l} = \delta_{0l} \quad \text{for every } l \in \mathbb{Z},$$
that is, a sequence whose even translates are orthonormal in $\ell^2(\mathbb{Z})$. Its **high-pass
filter** is $q_k = (-1)^k p_{1-k}$. The main fact of this module is that this one condition already
makes the combined family of the even translates of $p$ and of $q$ an orthonormal basis: no further
condition is needed, and in particular no Fourier analysis. The condition is the one of Exercise
4.5.2 of [han2009theoretical], and $q$ is the coefficient sequence of the wavelet in (4.5.4) there.

Transported along an orthonormal family $(e_k)_{k \in \mathbb{Z}}$ in a real Hilbert space, the fact
says: if $f_l = \sum_k p_{k-2l} e_k$ and $g_l = \sum_k q_{k-2l} e_k$, then the $f_l$ and the $g_l$
together form an orthonormal family with the same closed span as the $e_k$. Applied to the level-$1$
scaling system of a multiresolution analysis, with $p$ the dilation coefficients, this is the whole
algebraic content of Mallat's theorem; see `Numlib.Analysis.Wavelet.Multiresolution`.

## Main definitions

* `IsQMFCoeff`: the condition $\sum_k p_k p_{k-2l} = \delta_{0l}$ for every $l$.
* `qmfHigh`: the high-pass filter $q_k = (-1)^k p_{1-k}$.

## Main results

* `IsQMFCoeff.hasSum_low_low`, `IsQMFCoeff.hasSum_high_high`, `IsQMFCoeff.hasSum_low_high`: the
  three orthonormality relations of the two-channel family,
  $\sum_k p_{k-2l} p_{k-2m} = \delta_{lm}$, $\sum_k q_{k-2l} q_{k-2m} = \delta_{lm}$ and
  $\sum_k p_{k-2l} q_{k-2m} = 0$.
* `IsQMFCoeff.hasSum_sumElim_sq`: the **completeness relation**
  $\sum_l (p_{k-2l}^2 + q_{k-2l}^2) = 1$ for every $k$.
* `IsQMFCoeff.orthonormal_sumElim`, `IsQMFCoeff.topologicalClosure_span_sumElim`: the two-channel
  family $(f_l) \cup (g_l)$ in a Hilbert space is orthonormal and has the same closed span as the
  family $(e_k)$ it is built from.

## Proof outline

The orthogonality of the two channels is an involution argument: the substitution
$k \mapsto 1 + 2l + 2m - k$ sends the summand of $\sum_k p_{k-2l} q_{k-2m}$ to its negative. The
completeness relation is the splitting of $\sum_k p_k^2 = 1$ into the two parities: $k - 2l$ runs
over the integers congruent to $k$ mod $2$, and $1 - k + 2l$ over the others.

## Implementation notes

* All series are `HasSum` statements over $\mathbb{Z}$, so they converge unconditionally.
* `IsQMFCoeff.orthonormal_sumElim` holds in any real inner product space; only
  `IsQMFCoeff.topologicalClosure_span_sumElim` needs completeness.
-/

noncomputable section

variable {p : ℤ → ℝ}

/-! ### The filters -/

/-- A real sequence $p : \mathbb{Z} \to \mathbb{R}$ is a **quadrature mirror filter** if
$$\sum_{k \in \mathbb{Z}} p_k\, p_{k-2l} = \delta_{0l} \quad \text{for every } l \in
  \mathbb{Z},$$
with unconditional convergence. Equivalently, the even translates of $p$ are orthonormal in
$\ell^2(\mathbb{Z})$. This is the condition of Exercise 4.5.2 of [han2009theoretical]. -/
def IsQMFCoeff (p : ℤ → ℝ) : Prop :=
  ∀ l : ℤ, HasSum (fun k : ℤ => p k * p (k - 2 * l)) (if l = 0 then 1 else 0)

/-- The **high-pass filter** attached to a sequence $p : \mathbb{Z} \to \mathbb{R}$ is
$q_k = (-1)^k p_{1-k}$. It is the coefficient sequence of the wavelet in (4.5.4) of
[han2009theoretical]. -/
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

/-- The high-pass filter has the squares of the reflected sequence: $q_k^2 = p_{1-k}^2$ for every
$k \in \mathbb{Z}$. -/
theorem qmfHigh_sq (p : ℤ → ℝ) (k : ℤ) : qmfHigh p k ^ 2 = p (1 - k) ^ 2 := by
  rw [qmfHigh, mul_pow, pow_two ((-1 : ℝ) ^ k), neg_one_zpow_mul_self, one_mul]

/-- The even translates of the high-pass filter, with the sign taken out:
$q_{k-2l} = (-1)^k p_{1-k+2l}$ for all $k, l \in \mathbb{Z}$. -/
theorem qmfHigh_sub_two_mul (p : ℤ → ℝ) (k l : ℤ) :
    qmfHigh p (k - 2 * l) = (-1 : ℝ) ^ k * p (1 - k + 2 * l) := by
  rw [qmfHigh, neg_one_zpow_sub_two_mul, show (1 : ℤ) - (k - 2 * l) = 1 - k + 2 * l by ring]

/-! ### Summability -/

namespace IsQMFCoeff

/-- The squares of the coefficients of a quadrature mirror filter $p$ sum to one:
$\sum_{k \in \mathbb{Z}} p_k^2 = 1$. This is the defining condition at $l = 0$. -/
theorem hasSum_sq (hp : IsQMFCoeff p) : HasSum (fun k : ℤ => p k ^ 2) 1 := by
  have h := hp 0
  simp only [mul_zero, sub_zero] at h
  exact h.congr_fun fun k => pow_two (p k)

/-- For a quadrature mirror filter $p$, the series $\sum_{k \in \mathbb{Z}} p_k^2$ converges. -/
theorem summable_sq (hp : IsQMFCoeff p) : Summable fun k : ℤ => p k ^ 2 :=
  hp.hasSum_sq.summable

/-- For a quadrature mirror filter $p$ and $l \in \mathbb{Z}$, the series
$\sum_{k \in \mathbb{Z}} p_{k-2l}^2$ converges. -/
theorem summable_low_sq (hp : IsQMFCoeff p) (l : ℤ) :
    Summable fun k : ℤ => p (k - 2 * l) ^ 2 := by
  have hinj : Function.Injective (fun k : ℤ => k - 2 * l) := fun a b hab => by
    have h : a - 2 * l = b - 2 * l := hab
    omega
  exact hp.summable_sq.comp_injective hinj

/-- For a quadrature mirror filter $p$ with high-pass filter $q$ and $l \in \mathbb{Z}$, the series
$\sum_{k \in \mathbb{Z}} q_{k-2l}^2$ converges. -/
theorem summable_high_sq (hp : IsQMFCoeff p) (l : ℤ) :
    Summable fun k : ℤ => qmfHigh p (k - 2 * l) ^ 2 := by
  have hinj : Function.Injective (fun k : ℤ => 1 - k + 2 * l) := fun a b hab => by
    have h : 1 - a + 2 * l = 1 - b + 2 * l := hab
    omega
  refine (hp.summable_sq.comp_injective hinj).congr fun k => ?_
  simp only [Function.comp_apply]
  rw [qmfHigh_sq, show (1 : ℤ) - (k - 2 * l) = 1 - k + 2 * l by ring]

/-! ### The orthonormality relations -/

/-- The even translates of a quadrature mirror filter $p$ are orthonormal: for
$l, m \in \mathbb{Z}$,
$$\sum_{k \in \mathbb{Z}} p_{k-2l}\, p_{k-2m} = \delta_{lm}.$$

This is the defining condition, rewritten with both indices shifted. -/
theorem hasSum_low_low (hp : IsQMFCoeff p) (l m : ℤ) :
    HasSum (fun k : ℤ => p (k - 2 * l) * p (k - 2 * m)) (if l = m then 1 else 0) := by
  have h := hp (l - m)
  rw [show (if l - m = 0 then (1 : ℝ) else 0) = (if l = m then 1 else 0) by
    by_cases hlm : l = m <;> simp [hlm, sub_eq_zero]] at h
  rw [← Equiv.hasSum_iff (Equiv.subRight (2 * m))] at h
  refine h.congr_fun fun k => ?_
  simp only [Function.comp_apply, Equiv.subRight_apply]
  rw [show k - 2 * m - 2 * (l - m) = k - 2 * l by ring, mul_comm]

/-- Let $p$ be a quadrature mirror filter with high-pass filter $q$. The even translates of $q$ are
orthonormal: for $l, m \in \mathbb{Z}$,
$$\sum_{k \in \mathbb{Z}} q_{k-2l}\, q_{k-2m} = \delta_{lm}.$$

The substitution $k \mapsto 1 + 2m - k$ turns the sum into the defining condition at $m - l$. -/
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

/-- Let $p$ be a quadrature mirror filter with high-pass filter $q$. The even translates of $p$ are
orthogonal to the even translates of $q$: for $l, m \in \mathbb{Z}$,
$$\sum_{k \in \mathbb{Z}} p_{k-2l}\, q_{k-2m} = 0.$$

The involution $k \mapsto 1 + 2l + 2m - k$ sends the summand to its negative, so the sum is its
own negative. -/
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
  obtain ⟨a, ha⟩ := Real.summable_mul_of_summable_sq (hp.summable_low_sq l) (hp.summable_high_sq m)
  have hτ : HasSum (fun k : ℤ => -(p (k - 2 * l) * qmfHigh p (k - 2 * m))) a :=
    ((Equiv.hasSum_iff (Equiv.subLeft (1 + 2 * m + 2 * l))).mpr ha).congr_fun fun k => by
      simpa only [Function.comp_apply, Equiv.subLeft_apply] using (hneg k).symm
  have hna : HasSum (fun k : ℤ => p (k - 2 * l) * qmfHigh p (k - 2 * m)) (-a) := by
    simpa using hτ.neg
  have hself : a = -a := ha.unique hna
  rwa [show a = 0 by linarith] at ha

/-! ### The completeness relation -/

/-- For $k \in \mathbb{Z}$, the bijection $\mathbb{Z} \oplus \mathbb{Z} \to \mathbb{Z}$ that sends
$l$ in the first copy to $k - 2l$ and $l$ in the second copy to $1 - k + 2l$; the first branch
hits the integers congruent to $k$ mod $2$, the second the others. -/
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

/-- The **completeness relation** of a quadrature mirror filter. Let $p$ be a quadrature mirror
filter with high-pass filter $q$. For every $k \in \mathbb{Z}$,
$$\sum_{l \in \mathbb{Z}} \bigl(p_{k-2l}^2 + q_{k-2l}^2\bigr) = 1.$$

The sum is over $\mathbb{Z} \oplus \mathbb{Z}$ through `Sum.elim`: the first copy carries the
terms $p_{k-2l}^2$ and the second the terms $q_{k-2l}^2$. The relation is the splitting of
$\sum_k p_k^2 = 1$ into the two residue classes mod $2$, and it is what makes the two-channel
family complete. -/
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
/-- The **two-channel family is orthonormal**. Let $E$ be a real inner product space, $p$ a
quadrature mirror filter with high-pass filter $q$, and $(e_k)_{k \in \mathbb{Z}}$ an
orthonormal family in $E$. Let $(f_l)_{l \in \mathbb{Z}}$ and $(g_l)_{l \in \mathbb{Z}}$ be
vectors with
$$f_l = \sum_{k \in \mathbb{Z}} p_{k-2l}\, e_k, \qquad g_l = \sum_{k \in \mathbb{Z}} q_{k-2l}\,
  e_k,$$
with unconditional convergence. Then the family $(f_l) \cup (g_l)$ is orthonormal.

The family is indexed by $\mathbb{Z} \oplus \mathbb{Z}$ through `Sum.elim`. The space $E$ need
not be complete. -/
theorem orthonormal_sumElim : Orthonormal ℝ (Sum.elim f g) := by
  rw [orthonormal_iff_ite]
  rintro (l | l) (m | m)
  · simpa using (he.hasSum_mul_of_hasSum (hf l) (hf m)).unique (hp.hasSum_low_low l m)
  · simpa using (he.hasSum_mul_of_hasSum (hf l) (hg m)).unique (hp.hasSum_low_high l m)
  · have h := (he.hasSum_mul_of_hasSum (hg l) (hf m)).unique
      ((hp.hasSum_low_high m l).congr_fun fun k => mul_comm _ _)
    simpa using h
  · simpa using (he.hasSum_mul_of_hasSum (hg l) (hg m)).unique (hp.hasSum_high_high l m)

/-- The **two-channel family spans what the original family spans**. Let $E$ be a real Hilbert
space, $p$ a quadrature mirror filter with high-pass filter $q$, and $(e_k)_{k \in \mathbb{Z}}$
an orthonormal family in $E$. Let $f_l = \sum_k p_{k-2l} e_k$ and $g_l = \sum_k q_{k-2l} e_k$
for $l \in \mathbb{Z}$, with unconditional convergence. Then the closed linear span of the $f_l$
and the $g_l$ together equals the closed linear span of the $e_k$. With
`IsQMFCoeff.orthonormal_sumElim` this says that the low-pass and high-pass channels together are
an orthonormal basis of the closed span of $(e_k)$.

The family is indexed by $\mathbb{Z} \oplus \mathbb{Z}$ through `Sum.elim`. The proof uses the
completeness relation `IsQMFCoeff.hasSum_sumElim_sq`. -/
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
