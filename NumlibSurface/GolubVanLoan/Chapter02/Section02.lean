/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Analysis.Normed.Lp.PiLp
import Numlib.Analysis.Normed.Module.NormEquivalence

/-!
# Golub and Van Loan, Section 2.2: Vector norms

This module formalizes §2.2 of [golub2013matrix]: the definition of a vector norm (§2.2.1), the
$p$-norms $\|x\|_p = (|x_1|^p + \dots + |x_n|^p)^{1/p}$ of (2.2.1), Hölder's inequality (2.2.2) and
the Cauchy–Schwarz inequality (2.2.3), the equivalence of all norms on $\mathbb{R}^n$ (2.2.4) with
the explicit constants (2.2.5)–(2.2.7) for the 1-, 2- and $\infty$-norms, the orthogonal invariance
of the 2-norm (§2.2.2), and convergence of vectors (§2.2.4).

The proofs use the backbone modules `Numlib.Analysis.Normed.Lp.PiLp` (Hölder's inequality and the
comparison constants), `Numlib.Analysis.Normed.Module.NormEquivalence` (equivalence of norms and
convergence) and `Numlib.Analysis.Matrix.ToEuclideanLin` (orthogonal invariance).

## Main definitions

* §2.2.1, `GolubVanLoan.Chapter02.IsVectorNorm`: the axioms of a vector norm.

## Main results

* §2.2.1, `GolubVanLoan.Chapter02.IsVectorNorm.exists_seminorm`: a vector norm is a seminorm that
  vanishes only at $0$.
* §2.2.1, `GolubVanLoan.Chapter02.isVectorNorm_norm`: the norm of a real normed space is a vector
  norm.
* §2.2.1, `GolubVanLoan.Chapter02.isVectorNorm_norm_toLp`: the $p$-norms, $p \ge 1$, are vector
  norms on $\mathbb{R}^n$.
* Equation (2.2.1), `GolubVanLoan.Chapter02.equation_2_2_1`: the formulas for $\|x\|_p$, $\|x\|_1$,
  $\|x\|_2$ and $\|x\|_\infty$.
* Equation (2.2.2), `GolubVanLoan.Chapter02.equation_2_2_2`: Hölder's inequality
  $|x^T y| \le \|x\|_p \|y\|_q$.
* Equation (2.2.3), `GolubVanLoan.Chapter02.equation_2_2_3`: the Cauchy–Schwarz inequality
  $|x^T y| \le \|x\|_2 \|y\|_2$.
* Equation (2.2.4), `GolubVanLoan.Chapter02.equation_2_2_4`: all vector norms on $\mathbb{R}^n$ are
  equivalent.
* Equation (2.2.5), `GolubVanLoan.Chapter02.equation_2_2_5`:
  $\|x\|_2 \le \|x\|_1 \le \sqrt{n} \|x\|_2$.
* Equation (2.2.6), `GolubVanLoan.Chapter02.equation_2_2_6`: $\|x\|_\infty \le \|x\|_2 \le \sqrt{n}
  \|x\|_\infty$.
* Equation (2.2.7), `GolubVanLoan.Chapter02.equation_2_2_7`:
  $\|x\|_\infty \le \|x\|_1 \le n \|x\|_\infty$.
* §2.2.2, `GolubVanLoan.Chapter02.norm_mulVec_of_mem_orthogonalGroup`: $\|Qx\|_2 = \|x\|_2$ for
  orthogonal $Q$.
* §2.2.4, `GolubVanLoan.Chapter02.tendsto_iff_of_isVectorNorm`: convergence in one vector norm is
  convergence.

## Conventions

* The source's abstract vector norm is the predicate `GolubVanLoan.Chapter02.IsVectorNorm f` on a
  function `f : E → ℝ`. The source states the axioms on $\mathbb{R}^n$, and §2.3.1 uses the same
  axioms on $\mathbb{R}^{m \times n}$, so the predicate is stated once, for every real vector space.
* The $p$-norm $\|x\|_p$ of `x : Fin n → ℝ` is `‖WithLp.toLp p x‖`, the norm of `PiLp p`, for
  `p : ℝ≥0∞`.

## Implementation notes

* The predicate `GolubVanLoan.Chapter02.IsVectorNorm` is connected to the vocabulary of Mathlib, a
  definite `Seminorm ℝ E`, by `GolubVanLoan.Chapter02.IsVectorNorm.exists_seminorm`.

## Deviations from the source

* **§2.2.1, vector norm** (generalization). The axioms apply to every real vector space.
  See `GolubVanLoan.Chapter02.IsVectorNorm`.
* **Equation (2.2.1) and following special cases** (reading). The infinity norm of the empty
  vector is zero. See `GolubVanLoan.Chapter02.equation_2_2_1`.
* **§2.2.4, convergence** (generalization). The equivalence holds on every finite-dimensional
  real normed space. See `GolubVanLoan.Chapter02.tendsto_iff_of_isVectorNorm`.

## Not formalized

* **Absolute and relative error, §2.2.3.** The subsection names quantities and states a heuristic,
  "about $p$ correct significant digits", with $\approx$.
-/

open Filter Matrix Topology WithLp
open scoped ENNReal

namespace GolubVanLoan.Chapter02

variable {n : ℕ}

/-! ### §2.2.1 Definitions -/

/-- **§2.2.1** of [golub2013matrix], vector norm. A function $f : E \to \mathbb{R}$ on a real vector
space $E$ (the source's $\mathbb{R}^n$) is a **vector norm** if, for all $x, y \in E$ and
$\alpha \in \mathbb{R}$,
$$f(x) \ge 0, \qquad f(x) = 0 \iff x = 0, \qquad f(x + y) \le f(x) + f(y), \qquad f(\alpha x) =
  |\alpha| f(x).$$

**Generalization.** The book states the axioms on $\mathbb R^n$. The same axioms define a
norm on any real vector space, including the matrix spaces used in §2.3.1. -/
structure IsVectorNorm {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → ℝ) : Prop where
  /-- A vector norm is nonnegative: $f(x) \ge 0$. -/
  nonneg : ∀ x, 0 ≤ f x
  /-- A vector norm vanishes exactly at $0$: $f(x) = 0$ if and only if $x = 0$. -/
  eq_zero_iff : ∀ x, f x = 0 ↔ x = 0
  /-- The triangle inequality $f(x + y) \le f(x) + f(y)$. -/
  add_le : ∀ x y, f (x + y) ≤ f x + f y
  /-- Absolute homogeneity: $f(\alpha x) = |\alpha| f(x)$. -/
  smul : ∀ (α : ℝ) x, f (α • x) = |α| * f x

/-- **§2.2.1** of [golub2013matrix], connection to Mathlib. A function $f : E \to \mathbb{R}$ on a
real vector space $E$ is a vector norm if and only if $f$ is a seminorm, as a `Seminorm ℝ E`,
that vanishes only at $0$. -/
theorem IsVectorNorm.exists_seminorm {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → ℝ} :
    IsVectorNorm f ↔ ∃ p : Seminorm ℝ E, ⇑p = f ∧ ∀ x, p x = 0 → x = 0 := by
  constructor
  · intro hf
    refine ⟨Seminorm.of f hf.add_le fun a x => by rw [hf.smul, Real.norm_eq_abs], rfl,
      fun x hx => (hf.eq_zero_iff x).1 hx⟩
  · rintro ⟨p, rfl, hp⟩
    exact ⟨apply_nonneg p, fun x => ⟨hp x, fun h => h ▸ map_zero p⟩, map_add_le_add p,
      fun α x => by rw [map_smul_eq_mul, Real.norm_eq_abs]⟩

/-- **§2.2.1** of [golub2013matrix]. The norm $x \mapsto \|x\|$ of a real normed space is a vector
norm. -/
theorem isVectorNorm_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    IsVectorNorm fun x : E => ‖x‖ :=
  ⟨fun _ => norm_nonneg _, fun _ => norm_eq_zero, norm_add_le,
    fun α x => by rw [norm_smul, Real.norm_eq_abs]⟩

/-- **§2.2.1** of [golub2013matrix], the "useful class" of $p$-norms. For every $p \in [1, \infty]$,
the $p$-norm $x \mapsto \|x\|_p$ is a vector norm on $\mathbb{R}^n$. -/
theorem isVectorNorm_norm_toLp (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    IsVectorNorm fun x : Fin n → ℝ => ‖WithLp.toLp p x‖ := by
  have h := isVectorNorm_norm (E := PiLp p fun _ : Fin n => ℝ)
  exact ⟨fun x => h.nonneg _, fun x => by rw [h.eq_zero_iff, WithLp.toLp_eq_zero],
    fun x y => by rw [WithLp.toLp_add]; exact h.add_le _ _,
    fun α x => by rw [WithLp.toLp_smul]; exact h.smul _ _⟩

/-- **Equation (2.2.1)** of [golub2013matrix], the $p$-norms. Let $x \in \mathbb{R}^n$ and
$1 \le p < \infty$. Then
$$\|x\|_p = (|x_1|^p + \dots + |x_n|^p)^{1/p}.$$
The three most important norms are
$$\|x\|_1 = |x_1| + \dots + |x_n|, \qquad \|x\|_2 = (x^T x)^{1/2}, \qquad \|x\|_\infty = \max_{1
  \le i \le n} |x_i|.$$

**Reading.** The book writes a maximum over $1,\dots,n$. The declaration uses a supremum
that gives zero in dimension zero. -/
theorem equation_2_2_1 (x : Fin n → ℝ) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) :
    ‖WithLp.toLp p x‖ = (∑ i, |x i| ^ p.toReal) ^ (1 / p.toReal) ∧
      ‖WithLp.toLp 1 x‖ = ∑ i, |x i| ∧
      ‖WithLp.toLp 2 x‖ = √(x ⬝ᵥ x) ∧
      ‖WithLp.toLp ∞ x‖ = ⨆ i, |x i| := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (by positivity) hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [PiLp.norm_eq_sum hp0]
  · simp [PiLp.norm_eq_of_L1]
  · rw [EuclideanSpace.norm_eq]
    simp [dotProduct, ← sq]
  · simp [PiLp.norm_eq_ciSup]

/-! ### §2.2.2 Some vector norm properties -/

/-- **Equation (2.2.2)** of [golub2013matrix] (Hölder's inequality). Let $p, q \in [1, \infty]$ with
$1/p + 1/q = 1$, including the pair $p = 1$, $q = \infty$. Then for all $x, y \in \mathbb{R}^n$,
$$|x^T y| \le \|x\|_p \|y\|_q.$$

The condition $1/p + 1/q = 1$ is `ENNReal.HolderConjugate p q`. -/
theorem equation_2_2_2 {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (x y : Fin n → ℝ) : |x ⬝ᵥ y| ≤ ‖WithLp.toLp p x‖ * ‖WithLp.toLp q y‖ :=
  PiLp.norm_dotProduct_le x y

/-- **Equation (2.2.3)** of [golub2013matrix] (Cauchy–Schwarz inequality), the case $p = q = 2$ of
Hölder's inequality. For all $x, y \in \mathbb{R}^n$,
$$|x^T y| \le \|x\|_2 \|y\|_2.$$
-/
theorem equation_2_2_3 (x y : Fin n → ℝ) :
    |x ⬝ᵥ y| ≤ ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖ :=
  equation_2_2_2 x y

/-- **Equation (2.2.4)** of [golub2013matrix]: all norms on $\mathbb{R}^n$ are equivalent. For
vector norms $\|\cdot\|_\alpha$ and $\|\cdot\|_\beta$ on $\mathbb{R}^n$ there are constants
$c_1, c_2 > 0$ such that for all $x \in \mathbb{R}^n$
$$c_1 \|x\|_\alpha \le \|x\|_\beta \le c_2 \|x\|_\alpha.$$

The two norms are functions with the property `GolubVanLoan.Chapter02.IsVectorNorm`. -/
theorem equation_2_2_4 {fα fβ : (Fin n → ℝ) → ℝ} (hα : IsVectorNorm fα) (hβ : IsVectorNorm fβ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ x, c₁ * fα x ≤ fβ x ∧ fβ x ≤ c₂ * fα x := by
  obtain ⟨pα, rfl, hpα⟩ := IsVectorNorm.exists_seminorm.1 hα
  obtain ⟨pβ, rfl, hpβ⟩ := IsVectorNorm.exists_seminorm.1 hβ
  obtain ⟨a, A, ha, hA, hαb⟩ := pα.exists_bounds hpα
  obtain ⟨b, B, hb, hB, hβb⟩ := pβ.exists_bounds hpβ
  refine ⟨b / A, B / a, div_pos hb hA, div_pos hB ha, fun x => ⟨?_, ?_⟩⟩
  · calc b / A * pα x ≤ b / A * (A * ‖x‖) :=
          mul_le_mul_of_nonneg_left (hαb x).2 (div_pos hb hA).le
      _ = b * ‖x‖ := by field_simp
      _ ≤ pβ x := (hβb x).1
  · calc pβ x ≤ B * ‖x‖ := (hβb x).2
      _ = B / a * (a * ‖x‖) := by field_simp
      _ ≤ B / a * pα x := mul_le_mul_of_nonneg_left (hαb x).1 (div_pos hB ha).le

/-- **Equation (2.2.5)** of [golub2013matrix]. For all $x \in \mathbb{R}^n$,
$$\|x\|_2 \le \|x\|_1 \le \sqrt{n} \, \|x\|_2.$$
-/
theorem equation_2_2_5 (x : Fin n → ℝ) :
    ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 1 x‖ ∧ ‖WithLp.toLp 1 x‖ ≤ √(n : ℝ) * ‖WithLp.toLp 2 x‖ :=
  ⟨PiLp.norm_toLp_two_le_norm_toLp_one x, by
    simpa using PiLp.norm_toLp_one_le_sqrt_card_mul_norm_toLp_two x⟩

/-- **Equation (2.2.6)** of [golub2013matrix]. For all $x \in \mathbb{R}^n$,
$$\|x\|_\infty \le \|x\|_2 \le \sqrt{n} \, \|x\|_\infty.$$
-/
theorem equation_2_2_6 (x : Fin n → ℝ) :
    ‖WithLp.toLp ∞ x‖ ≤ ‖WithLp.toLp 2 x‖ ∧ ‖WithLp.toLp 2 x‖ ≤ √(n : ℝ) * ‖WithLp.toLp ∞ x‖ :=
  ⟨PiLp.norm_toLp_top_le_norm_toLp_two x, by
    simpa using PiLp.norm_toLp_two_le_sqrt_card_mul_norm_toLp_top x⟩

/-- **Equation (2.2.7)** of [golub2013matrix]. For all $x \in \mathbb{R}^n$,
$$\|x\|_\infty \le \|x\|_1 \le n \, \|x\|_\infty.$$
-/
theorem equation_2_2_7 (x : Fin n → ℝ) :
    ‖WithLp.toLp ∞ x‖ ≤ ‖WithLp.toLp 1 x‖ ∧ ‖WithLp.toLp 1 x‖ ≤ n * ‖WithLp.toLp ∞ x‖ :=
  ⟨PiLp.norm_toLp_top_le_norm_toLp_one x, by
    simpa using PiLp.norm_toLp_one_le_card_mul_norm_toLp_top x⟩

/-- **§2.2.2** of [golub2013matrix], orthogonal invariance. The 2-norm is preserved under orthogonal
transformation: for an orthogonal $Q \in \mathbb{R}^{n \times n}$ and $x \in \mathbb{R}^n$,
$$\|Qx\|_2 = \|x\|_2.$$

The source's reason is $\|Qx\|_2^2 = x^T Q^T Q x = x^T x$. -/
theorem norm_mulVec_of_mem_orthogonalGroup {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (x : Fin n → ℝ) :
    ‖WithLp.toLp 2 (Q *ᵥ x)‖ = ‖WithLp.toLp 2 x‖ :=
  norm_toLp_mulVec_of_mem_unitaryGroup hQ x

/-! ### §2.2.4 Convergence -/

/-- **§2.2.4** of [golub2013matrix], convergence. Let $E$ be a finite-dimensional real normed space,
let $f$ be a vector norm on $E$, and let $x^{(k)}$ be a sequence in $E$ and $x \in E$. Then
$f(x^{(k)} - x) \to 0$ if and only if $x^{(k)} \to x$. So "convergence in any particular norm
implies convergence in all norms".

**Generalization.** The source states this on $\mathbb{R}^n$. The theorem uses an arbitrary
finite-dimensional real normed space, with its given topology as the reference. -/
theorem tendsto_iff_of_isVectorNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} (hf : IsVectorNorm f) (x : ℕ → E) (x₀ : E) :
    Tendsto (fun k => f (x k - x₀)) atTop (𝓝 0) ↔ Tendsto x atTop (𝓝 x₀) := by
  obtain ⟨p, rfl, hp⟩ := IsVectorNorm.exists_seminorm.1 hf
  rw [Seminorm.tendsto_apply_iff_tendsto_norm p hp fun k => x k - x₀]
  exact tendsto_iff_norm_sub_tendsto_zero.symm

end GolubVanLoan.Chapter02
