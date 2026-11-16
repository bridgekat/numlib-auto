/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.PosDef
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.RingTheory.Polynomial.ChebyshevMinimax

/-!
# Decay of the entries of the inverse of a banded positive definite matrix

Let $G$ be a real symmetric positive definite matrix with lower and upper bandwidth $\beta$, and let
all eigenvalues of $G$ lie in $[a, b]$ with $0 < a$. Put $\kappa = b / a$ and
$q = (\sqrt{\kappa} - 1)/(\sqrt{\kappa} + 1)$. This file proves that the entries of $G^{-1}$ decay
exponentially away from the diagonal:
$$|(G^{-1})_{ij}| \le \frac{2}{a} \, q^{\lceil |i - j| / \beta \rceil}.$$
This is Theorem 2.4 of Demko, Moss and Smith (1984), here with the constant $2$ and the integer
exponent $\lceil |i - j| / \beta \rceil$. For a tridiagonal matrix ($\beta = 1$) and the extreme
eigenvalues it is Lemma B.10.1 of [cartis2022evaluation].

## Main results

* `Matrix.exists_degree_lt_abs_one_sub_mul_eval_le`: for every $d$ there is a polynomial $p$ of
  degree less than $d$ with $|1 - t\,p(t)| \le 2 q^d$ on $[a, b]$.
* `Matrix.abs_inv_apply_le_of_hasBandwidth_of_mem_Icc`: the decay bound for any interval $[a, b]$
  that contains the spectrum.
* `Matrix.abs_inv_apply_le_of_hasBandwidth`: the decay bound with $a = \lambda_{\min}(G)$ and
  $b = \lambda_{\max}(G)$.
* `Matrix.abs_inv_apply_le_of_isTridiagonal`: Lemma B.10.1 of [cartis2022evaluation], the bound for
  a tridiagonal matrix.

## Proof outline

The proof is by polynomial approximation. A polynomial $p(G)$ of degree $d - 1$ has bandwidth
$\beta (d - 1)$, so $(G^{-1})_{ij} = (G^{-1} - p(G))_{ij}$ as soon as $|i - j| > \beta (d - 1)$. If
$G$ is diagonalized by an orthogonal matrix, every entry of $G^{-1} - p(G)$ is bounded by the
largest value of $|1/\lambda - p(\lambda)| = |1 - \lambda p(\lambda)| / \lambda$ on the spectrum. If
$1 - X p$ is the shifted Chebyshev polynomial of degree $d$ normalized at the origin
(`Polynomial.Chebyshev.shifted`), this value is at most $2 q^d / a$.

## Implementation notes

* The exponent is the natural-number ceiling `⌈|i - j| / β⌉₊`. For $\beta = 0$ the quotient is $0$
  by the Lean convention $x / 0 = 0$, so the exponent is $0$ and the bound is $2/a$.
-/

open Finset Polynomial Polynomial.Chebyshev

namespace Matrix

/-! ### The approximating polynomial -/

/-- For $0 < a \le b$ and $\kappa = b/a$, the ratio $(\sqrt{\kappa} - 1)/(\sqrt{\kappa} + 1)$ is
nonnegative. -/
private theorem decay_ratio_nonneg {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ (√(b / a) - 1) / (√(b / a) + 1) := by
  have : 1 ≤ √(b / a) := Real.one_le_sqrt.2 ((one_le_div ha).2 hab)
  positivity

/-- **The residual polynomial.** Let $0 < a \le b$, $\kappa = b/a$,
$q = (\sqrt{\kappa} - 1)/(\sqrt{\kappa} + 1)$, and $d \in \mathbb{N}$. There is a real
polynomial $r$ of degree at most $d$ with $r(0) = 1$ and
$$|r(t)| \le 2 q^d \quad \text{for all } t \in [a, b].$$

The polynomial is the shifted Chebyshev polynomial if $a < b$, and $(1 - X/a)^d$ if $a = b$. -/
theorem exists_eval_zero_eq_one_abs_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (d : ℕ) :
    ∃ r : ℝ[X], r.natDegree ≤ d ∧ r.eval 0 = 1 ∧
      ∀ t ∈ Set.Icc a b, |r.eval t| ≤ 2 * ((√(b / a) - 1) / (√(b / a) + 1)) ^ d := by
  rcases hab.lt_or_eq with hab | rfl
  · have h0 : (0 : ℝ) ∉ Set.Icc a b := fun h => absurd h.1 (not_le.2 ha)
    refine ⟨shifted d a b 0, natDegree_le_iff_degree_le.2 (shifted_degree_le d a b 0),
      shifted_eval_self d hab h0, fun t ht => ?_⟩
    have hκ : 1 < b / a := (one_lt_div ha).2 hab
    have harg : (b + a - 2 * 0) / (b - a) = (b / a + 1) / (b / a - 1) := by
      have h2 : b - a ≠ 0 := sub_ne_zero.2 hab.ne'
      field_simp
      ring
    have hT : 0 < (T ℝ d).eval ((b / a + 1) / (b / a - 1)) :=
      lt_of_lt_of_le one_pos (one_le_eval_T (by rw [le_div_iff₀ (by linarith)]; linarith) d)
    calc |(shifted d a b 0).eval t| ≤ 1 / |(T ℝ d).eval ((b + a - 2 * 0) / (b - a))| :=
          abs_eval_shifted_le d hab ht
      _ = 1 / (T ℝ d).eval ((b / a + 1) / (b / a - 1)) := by rw [harg, abs_of_pos hT]
      _ ≤ _ := one_div_eval_T_le_two_mul_pow hκ d
  · refine ⟨(1 - C (1 / a) * X) ^ d, ?_, by simp, fun t ht => ?_⟩
    · refine (natDegree_pow_le).trans ?_
      have : (1 - C (1 / a) * X : ℝ[X]).natDegree ≤ 1 := by compute_degree
      nlinarith
    · have ht : t = a := le_antisymm ht.2 ht.1
      subst ht
      have hq : (√(t / t) - 1) / (√(t / t) + 1) = 0 := by simp [div_self ha.ne']
      rw [hq]
      simp only [eval_pow, eval_sub, eval_one, eval_mul, eval_C, eval_X, one_div,
        inv_mul_cancel₀ ha.ne', sub_self, abs_pow, abs_zero]
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · norm_num
      · simp [zero_pow hd.ne']

/-- **The approximate inverse.** Let $0 < a \le b$, $\kappa = b/a$,
$q = (\sqrt{\kappa} - 1)/(\sqrt{\kappa} + 1)$, and $d \in \mathbb{N}$. There is a real
polynomial $p$ of degree less than $d$ with
$$|1 - t\,p(t)| \le 2 q^d \quad \text{for all } t \in [a, b].$$

For $d = 0$ the polynomial is $p = 0$, whose degree is $-\infty$ in the Lean convention. -/
theorem exists_degree_lt_abs_one_sub_mul_eval_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (d : ℕ) :
    ∃ p : ℝ[X], p.degree < d ∧
      ∀ t ∈ Set.Icc a b, |1 - t * p.eval t| ≤ 2 * ((√(b / a) - 1) / (√(b / a) + 1)) ^ d := by
  obtain ⟨r, hrd, hr0, hrb⟩ := exists_eval_zero_eq_one_abs_le ha hab d
  have hdvd : X ∣ 1 - r := by
    rw [X_dvd_iff, coeff_zero_eq_eval_zero]
    simp [hr0]
  obtain ⟨p, hp⟩ := hdvd
  refine ⟨p, ?_, fun t ht => ?_⟩
  · by_cases hp0 : p = 0
    · rw [hp0, degree_zero]
      exact WithBot.bot_lt_coe _
    · have h1 : (1 - r).natDegree ≤ d :=
        (natDegree_sub_le _ _).trans (max_le (by simp) hrd)
      rw [hp, natDegree_X_mul hp0] at h1
      exact (degree_le_natDegree).trans_lt (by exact_mod_cast Nat.lt_of_succ_le h1)
  · have := congrArg (eval t) hp
    simp only [eval_sub, eval_one, eval_mul, eval_X] at this
    rw [← this, sub_sub_cancel]
    exact hrb t ht

/-! ### Banded polynomials -/

section Band

variable {m β : ℕ} {G : Matrix (Fin m) (Fin m) ℝ}

/-- Let $G$ be a real square matrix of order $m$ with lower and upper bandwidth $\beta$, and let $p$
be a real polynomial. Then $p(G)_{ij} = 0$ for all $i, j$ with $|i - j| > \beta \deg p$. -/
theorem aeval_apply_eq_zero_of_hasBandwidth (hl : G.HasLowerBandwidth β)
    (hu : G.HasUpperBandwidth β) {p : ℝ[X]} {i j : Fin m}
    (h : β * p.natDegree < ((i : ℤ) - j).natAbs) : aeval G p i j = 0 := by
  have hpow : ∀ n, (G ^ n).HasLowerBandwidth (β * n) ∧ (G ^ n).HasUpperBandwidth (β * n) := by
    intro n
    induction n with
    | zero =>
      simp only [pow_zero, mul_zero]
      exact ⟨fun i j hij => one_apply_ne (ne_of_gt ((card_filter_le_lt_pos_iff i j).1 hij)),
        fun i j hij => one_apply_ne (ne_of_lt ((card_filter_le_lt_pos_iff j i).1 hij))⟩
    | succ n ih =>
      rw [pow_succ, mul_add, mul_one]
      exact ⟨ih.1.mul hl, ih.2.mul hu⟩
  rw [aeval_eq_sum_range, Matrix.sum_apply]
  refine sum_eq_zero fun n hn => ?_
  have hn : n ≤ p.natDegree := Nat.lt_succ_iff.1 (mem_range.1 hn)
  have hb : β * n < ((i : ℤ) - j).natAbs := lt_of_le_of_lt (Nat.mul_le_mul_left β hn) h
  rw [Matrix.smul_apply, smul_eq_mul]
  rcases le_total (j : ℕ) i with hji | hij
  · rw [(hasLowerBandwidth_iff_fin.1 (hpow n).1) i j (by omega), mul_zero]
  · rw [(hasUpperBandwidth_iff_fin.1 (hpow n).2) i j (by omega), mul_zero]

end Band

/-! ### Spectral bounds -/

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n]

open Unitary in
/-- Let $U$ be a real orthogonal matrix, $d$ a real vector, and $M$ a real number with $|d_k| \le M$
for all $k$. Then every entry of $U \operatorname{diag}(d) U^T$ satisfies
$$|(U \operatorname{diag}(d) U^T)_{ij}| \le M.$$

The rows of $U$ are unit vectors, so $|\sum_k u_{ik} d_k u_{jk}| \le M \sum_k (u_{ik}^2 +
u_{jk}^2)/2 = M$. The matrix $U \operatorname{diag}(d) U^T$ is `Unitary.conjStarAlgAut ℝ _ U
(Matrix.diagonal d)`. -/
theorem abs_conjStarAlgAut_diagonal_apply_le (U : unitary (Matrix n n ℝ)) (d : n → ℝ) {M : ℝ}
    (hd : ∀ k, |d k| ≤ M) (i j : n) : |conjStarAlgAut ℝ _ U (diagonal d) i j| ≤ M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hd i)
  have hrow : ∀ i, ∑ k, (U : Matrix n n ℝ) i k * (U : Matrix n n ℝ) i k = 1 := fun i => by
    have := congrFun (congrFun (Unitary.coe_mul_star_self U) i) i
    simpa [Matrix.mul_apply, star_apply] using this
  rw [conjStarAlgAut_apply, Matrix.mul_apply]
  simp only [mul_diagonal, star_apply, star_trivial]
  calc |∑ k, (U : Matrix n n ℝ) i k * d k * (U : Matrix n n ℝ) j k|
      ≤ ∑ k, |(U : Matrix n n ℝ) i k * d k * (U : Matrix n n ℝ) j k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, M * (((U : Matrix n n ℝ) i k * (U : Matrix n n ℝ) i k +
          (U : Matrix n n ℝ) j k * (U : Matrix n n ℝ) j k) / 2) := by
        refine sum_le_sum fun k _ => ?_
        rw [abs_mul, abs_mul]
        have h1 := hd k
        have h2 : |(U : Matrix n n ℝ) i k| * |(U : Matrix n n ℝ) j k| ≤
            ((U : Matrix n n ℝ) i k * (U : Matrix n n ℝ) i k +
              (U : Matrix n n ℝ) j k * (U : Matrix n n ℝ) j k) / 2 := by
          nlinarith [sq_nonneg (|(U : Matrix n n ℝ) i k| - |(U : Matrix n n ℝ) j k|),
            sq_abs ((U : Matrix n n ℝ) i k), sq_abs ((U : Matrix n n ℝ) j k)]
        calc |(U : Matrix n n ℝ) i k| * |d k| * |(U : Matrix n n ℝ) j k|
            = |d k| * (|(U : Matrix n n ℝ) i k| * |(U : Matrix n n ℝ) j k|) := by ring
          _ ≤ M * (|(U : Matrix n n ℝ) i k| * |(U : Matrix n n ℝ) j k|) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left h2 hM
    _ = M := by
        rw [← mul_sum, ← sum_div, sum_add_distrib, hrow, hrow]
        ring

variable {G : Matrix n n ℝ} (hG : G.IsHermitian)

open Unitary in
/-- Let $G$ be a real symmetric matrix with eigenvalues $\lambda_k$ and orthogonal eigenvector
matrix $U$ (`Matrix.IsHermitian.eigenvectorUnitary`). Then for every real polynomial $p$,
$$p(G) = U \operatorname{diag}(p(\lambda_k)) U^T.$$
-/
theorem IsHermitian.aeval_eq_conj (p : ℝ[X]) :
    aeval G p = conjStarAlgAut ℝ _ hG.eigenvectorUnitary
      (diagonal fun k => p.eval (hG.eigenvalues k)) := by
  set Φ := conjStarAlgAut ℝ (Matrix n n ℝ) hG.eigenvectorUnitary
  have key : ∀ x, aeval (Φ x) p = Φ (aeval x p) := fun x =>
    aeval_algHom_apply (AlgHom.ofClass Φ) x p
  conv_lhs => rw [hG.spectral_theorem]
  rw [key]
  congr 1
  rw [← diagonalAlgHom_apply ℝ, aeval_algHom_apply, aeval_pi_apply]
  simp [coe_aeval_eq_eval]

open Unitary in
/-- Let $G$ be a real symmetric matrix with eigenvalues $\lambda_k \ne 0$ and orthogonal eigenvector
matrix $U$ (`Matrix.IsHermitian.eigenvectorUnitary`). Then
$$G^{-1} = U \operatorname{diag}(\lambda_k^{-1}) U^T.$$
-/
theorem IsHermitian.inv_eq_conj (h0 : ∀ k, hG.eigenvalues k ≠ 0) :
    G⁻¹ = conjStarAlgAut ℝ _ hG.eigenvectorUnitary (diagonal fun k => (hG.eigenvalues k)⁻¹) := by
  refine inv_eq_right_inv ?_
  rw [congrArg (· * _) hG.spectral_theorem, ← map_mul, diagonal_mul_diagonal]
  convert map_one (conjStarAlgAut ℝ (Matrix n n ℝ) hG.eigenvectorUnitary)
  rw [← diagonal_one]
  congr 1
  funext k
  simp [mul_inv_cancel₀ (h0 k)]

end Spectral

/-! ### The decay bound -/

variable {m β : ℕ} {G : Matrix (Fin m) (Fin m) ℝ}

open Unitary in
/-- **Decay of the inverse of a banded positive definite matrix**, for any spectral enclosure. Let
$G$ be a real symmetric positive definite matrix of order $m$ with lower and upper bandwidth
$\beta$. Let $0 < a$, and assume that every eigenvalue of $G$ lies in $[a, b]$. Put
$\kappa = b/a$ and $q = (\sqrt{\kappa} - 1)/(\sqrt{\kappa} + 1)$. Then for all $i, j$,
$$|(G^{-1})_{ij}| \le \frac{2}{a} \, q^{\lceil |i - j| / \beta \rceil}.$$

The exponent is the natural-number ceiling, and for $\beta = 0$ it is $0$ because $x / 0 = 0$ in
Lean. -/
theorem abs_inv_apply_le_of_hasBandwidth_of_mem_Icc (hG : G.PosDef) (hl : G.HasLowerBandwidth β)
    (hu : G.HasUpperBandwidth β) {a b : ℝ} (ha : 0 < a)
    (hspec : ∀ k, hG.1.eigenvalues k ∈ Set.Icc a b) (i j : Fin m) :
    |G⁻¹ i j| ≤ 2 / a * ((√(b / a) - 1) / (√(b / a) + 1)) ^
      ⌈(((i : ℤ) - j).natAbs : ℝ) / β⌉₊ := by
  have hab : a ≤ b := (hspec i).1.trans (hspec i).2
  set D := ((i : ℤ) - j).natAbs with hD
  set d := ⌈(D : ℝ) / β⌉₊ with hd
  obtain ⟨p, hpd, hpb⟩ := exists_degree_lt_abs_one_sub_mul_eval_le ha hab d
  -- the entry `(i, j)` of `p(G)` vanishes
  have hzero : aeval G p i j = 0 := by
    by_cases hp0 : p = 0
    · simp [hp0]
    refine aeval_apply_eq_zero_of_hasBandwidth hl hu ?_
    have hnat : p.natDegree < d := by
      rwa [degree_eq_natDegree hp0, Nat.cast_lt] at hpd
    have hceil : (d : ℝ) < D / β + 1 := Nat.ceil_lt_add_one (by positivity)
    -- `d ≥ 1` forces `D / β > 0`, hence `β ≠ 0`
    have hβpos : (0 : ℝ) < β := by
      have hdpos : 0 < (D : ℝ) / β := Nat.ceil_pos.1 (lt_of_le_of_lt (Nat.zero_le _) hnat)
      rcases Nat.eq_zero_or_pos β with h0 | h0
      · simp [h0] at hdpos
      · exact_mod_cast h0
    have : ((β * p.natDegree : ℕ) : ℝ) < D := by
      have h1 : ((p.natDegree : ℕ) : ℝ) + 1 ≤ d := by exact_mod_cast hnat
      push_cast
      have h2 : (p.natDegree : ℝ) < D / β := by linarith
      rw [lt_div_iff₀ hβpos] at h2
      linarith
    have h' : β * p.natDegree < D := by exact_mod_cast this
    exact h'
  -- `G⁻¹ - p(G)` in the eigenbasis
  have h0 : ∀ k, hG.1.eigenvalues k ≠ 0 := fun k => (hG.eigenvalues_pos k).ne'
  have heq : G⁻¹ i j = conjStarAlgAut ℝ _ hG.1.eigenvectorUnitary
      (diagonal fun k => (hG.1.eigenvalues k)⁻¹ - p.eval (hG.1.eigenvalues k)) i j := by
    calc G⁻¹ i j = G⁻¹ i j - aeval G p i j := by rw [hzero, sub_zero]
      _ = (G⁻¹ - aeval G p) i j := (Matrix.sub_apply _ _ _ _).symm
      _ = _ := by rw [hG.1.inv_eq_conj h0, hG.1.aeval_eq_conj p, ← map_sub, diagonal_sub]
  rw [heq]
  refine abs_conjStarAlgAut_diagonal_apply_le _ _ (fun k => ?_) i j
  have hk := hspec k
  have hlam : 0 < hG.1.eigenvalues k := hG.eigenvalues_pos k
  have hq := decay_ratio_nonneg ha hab
  rw [show (hG.1.eigenvalues k)⁻¹ - p.eval (hG.1.eigenvalues k) =
      (1 - hG.1.eigenvalues k * p.eval (hG.1.eigenvalues k)) / hG.1.eigenvalues k by
    field_simp, abs_div, abs_of_pos hlam, div_le_iff₀ hlam]
  calc |1 - hG.1.eigenvalues k * p.eval (hG.1.eigenvalues k)|
      ≤ 2 * ((√(b / a) - 1) / (√(b / a) + 1)) ^ d := hpb _ hk
    _ = 2 / a * ((√(b / a) - 1) / (√(b / a) + 1)) ^ d * a := by field_simp
    _ ≤ 2 / a * ((√(b / a) - 1) / (√(b / a) + 1)) ^ d * hG.1.eigenvalues k :=
        mul_le_mul_of_nonneg_left hk.1 (by positivity)

/-- **Decay of the inverse of a banded positive definite matrix.** Let $G$ be a real symmetric
positive definite matrix of order $m$ with lower and upper bandwidth $\beta$. Let
$a = \lambda_{\min}(G)$, $\kappa = \lambda_{\max}(G) / \lambda_{\min}(G)$ and
$q = (\sqrt{\kappa} - 1)/(\sqrt{\kappa} + 1)$. Then for all $i, j$,
$$|(G^{-1})_{ij}| \le \frac{2}{a} \, q^{\lceil |i - j| / \beta \rceil}.$$
Since $0 \le q \le 1$, this gives $|(G^{-1})_{ij}| \le (2/a) \, q^{|i - j| / \beta}$ for
$\beta \ge 1$.

This is Theorem 2.4 of Demko, Moss and Smith (1984), with the constant $2$ and the integer
exponent $\lceil |i - j| / \beta \rceil$. The exponent is the natural-number ceiling, and for
$\beta = 0$ it is $0$ because $x / 0 = 0$ in Lean. The extreme eigenvalues $\lambda_{\min}(G)$
and $\lambda_{\max}(G)$ are the infimum and the supremum of `Matrix.IsHermitian.eigenvalues`.
The proof specializes `Matrix.abs_inv_apply_le_of_hasBandwidth_of_mem_Icc`. -/
theorem abs_inv_apply_le_of_hasBandwidth (hG : G.PosDef) (hl : G.HasLowerBandwidth β)
    (hu : G.HasUpperBandwidth β) (i j : Fin m) :
    |G⁻¹ i j| ≤ 2 / (⨅ k, hG.1.eigenvalues k) *
      ((√((⨆ k, hG.1.eigenvalues k) / ⨅ k, hG.1.eigenvalues k) - 1) /
        (√((⨆ k, hG.1.eigenvalues k) / ⨅ k, hG.1.eigenvalues k) + 1)) ^
      ⌈(((i : ℤ) - j).natAbs : ℝ) / β⌉₊ := by
  have : Nonempty (Fin m) := ⟨i⟩
  obtain ⟨k₀, hk₀⟩ := exists_eq_ciInf_of_finite (f := hG.1.eigenvalues)
  refine abs_inv_apply_le_of_hasBandwidth_of_mem_Icc hG hl hu ?_ (fun k => ⟨?_, ?_⟩) i j
  · rw [← hk₀]
    exact hG.eigenvalues_pos k₀
  · exact ciInf_le (Set.finite_range _).bddBelow k
  · exact le_ciSup (Set.finite_range _).bddAbove k

/-- Let $T$ be a real symmetric positive definite tridiagonal matrix of order $m$. Let
$a = \lambda_{\min}(T)$ and $\kappa = \lambda_{\max}(T) / \lambda_{\min}(T)$. Then for all
$i, j$,
$$|(T^{-1})_{ij}| \le \frac{2}{a} \left( \frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1}
  \right)^{|i - j|}.$$
This is Lemma B.10.1 of [cartis2022evaluation].

The extreme eigenvalues are the infimum and the supremum of `Matrix.IsHermitian.eigenvalues`.
The proof is `Matrix.abs_inv_apply_le_of_hasBandwidth` with $\beta = 1$. -/
theorem abs_inv_apply_le_of_isTridiagonal {T : Matrix (Fin m) (Fin m) ℝ} (hT : T.PosDef)
    (htri : T.IsTridiagonal) (i j : Fin m) :
    |T⁻¹ i j| ≤ 2 / (⨅ k, hT.1.eigenvalues k) *
      ((√((⨆ k, hT.1.eigenvalues k) / ⨅ k, hT.1.eigenvalues k) - 1) /
        (√((⨆ k, hT.1.eigenvalues k) / ⨅ k, hT.1.eigenvalues k) + 1)) ^
      ((i : ℤ) - j).natAbs := by
  obtain ⟨hl, hu⟩ := isTridiagonal_iff_hasBandwidth_one.1 htri
  have h := abs_inv_apply_le_of_hasBandwidth hT hl hu i j
  simpa only [Nat.cast_one, div_one, Nat.ceil_natCast] using h

end Matrix
