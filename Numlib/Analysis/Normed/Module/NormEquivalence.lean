/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Module.FiniteDimension`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Equivalence of norms on a finite-dimensional real normed space

Let $E$ be a finite-dimensional real normed space with norm $\|\cdot\|$, and let $p$ be a second
norm on $E$. This file proves that the two norms are equivalent: there are constants $c, C > 0$ with
$$c \|x\| \le p(x) \le C \|x\| \quad \text{for all } x \in E.$$ The second norm is given as a
seminorm $p$ that is definite, that is, $p(x) = 0$ implies $x = 0$. The upper bound holds for every
seminorm. As a consequence, convergence to $0$ and the limit of $k$-th roots $\|f_k\|^{1/k}$ of a
sequence do not depend on the norm.

Mathlib proves that all norms on a finite-dimensional space over a complete nontrivially normed
field induce the same topology, but it does not state the two-sided inequality, because a type has
only one norm instance. The inequality is what a theorem about an arbitrary norm needs. An example
is Gelfand's formula $\|A^k\|^{1/k} \to \rho(A)$: the limit is the same for every matrix norm, but
the proof is convenient only for one norm.

## Main results

* `Seminorm.exists_le_mul_norm`: every seminorm $p$ on $E$ satisfies $p(x) \le C \|x\|$ for some
  $C > 0$.
* `Seminorm.continuous_of_finiteDimensional`: every seminorm on $E$ is continuous.
* `Seminorm.exists_mul_norm_le`: a definite seminorm $p$ on $E$ satisfies $c \|x\| \le p(x)$ for
  some $c > 0$.
* `Seminorm.exists_bounds`: the two bounds together, which is the equivalence of the two norms.
* `Seminorm.tendsto_apply_iff_tendsto_norm`: $p(f_k) \to 0$ if and only if $\|f_k\| \to 0$.
* `Seminorm.tendsto_rpow_one_div`: if $\|f_k\|^{1/k} \to L$, then $p(f_k)^{1/k} \to L$.
* `Seminorm.exists_bounds_rclike` and `Seminorm.continuous_rclike`: the same facts for seminorms on
  $\mathbb{K}^n$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$.

## Proof outline

The upper bound is the elementary half: expand $x$ in a basis and use subadditivity. The lower bound
is where finite dimension enters: $p$ is Lipschitz by the upper bound, hence continuous, and the
unit sphere is compact, so $p$ attains a positive minimum on it.

## Implementation notes

* The second norm is unbundled, as a `Seminorm ℝ E` together with the hypothesis
  `∀ x, p x = 0 → x = 0`, because a type has only one `Norm` instance. The note in
  `Mathlib.Analysis.Normed.Module.FiniteDimension` gives this reason for the absence of the
  inequality from Mathlib.
* A norm on a complex vector space is also a `Seminorm ℝ` on the underlying real space, and finite
  complex dimension is finite real dimension, so the real statement covers the complex case.
-/

open Filter Metric Topology

namespace Seminorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Let $E$ be a finite-dimensional real normed space. Every seminorm $p$ on $E$ is bounded by a
multiple of the norm: there is $C > 0$ with $p(x) \le C \|x\|$ for all $x \in E$.

The proof expands a vector in a basis. The coordinate functionals are continuous because $E$ is
finite-dimensional, and subadditivity gives the bound. -/
theorem exists_le_mul_norm (p : Seminorm ℝ E) : ∃ C : ℝ, 0 < C ∧ ∀ x, p x ≤ C * ‖x‖ := by
  classical
  set b := Module.finBasis ℝ E with hb
  have hcoord : ∀ i, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : E, |b.repr x i| ≤ K * ‖x‖ := by
    intro i
    refine ⟨‖LinearMap.toContinuousLinearMap (b.coord i)‖, norm_nonneg _, fun x => ?_⟩
    simpa [Real.norm_eq_abs] using (LinearMap.toContinuousLinearMap (b.coord i)).le_opNorm x
  choose K hK hKle using hcoord
  refine ⟨(∑ i, K i * p (b i)) + 1, ?_, fun x => ?_⟩
  · have hnn : (0 : ℝ) ≤ ∑ i, K i * p (b i) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hK i) (apply_nonneg p _)
    linarith
  · have hx : p x ≤ ∑ i, p (b.repr x i • b i) := by
      conv_lhs => rw [← b.sum_repr x]
      exact Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _
    have hstep : ∀ i, p (b.repr x i • b i) ≤ (K i * ‖x‖) * p (b i) := by
      intro i
      rw [map_smul_eq_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hKle i x) (apply_nonneg p _)
    have hsum : ∑ i, p (b.repr x i • b i) ≤ (∑ i, K i * p (b i)) * ‖x‖ := by
      refine (Finset.sum_le_sum fun i _ => hstep i).trans_eq ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hnorm := norm_nonneg x
    nlinarith [hx.trans hsum]

/-- Let $E$ be a finite-dimensional real normed space. Every seminorm $p$ on $E$ is continuous.

The bound of `Seminorm.exists_le_mul_norm` makes $p$ Lipschitz. -/
theorem continuous_of_finiteDimensional (p : Seminorm ℝ E) : Continuous p := by
  obtain ⟨C, hC, hle⟩ := p.exists_le_mul_norm
  refine LipschitzWith.continuous (K := Real.toNNReal C)
    (LipschitzWith.of_dist_le_mul fun x y => ?_)
  have hxy : p x ≤ p (x - y) + p y := by
    simpa using map_add_le_add p (x - y) y
  have hyx : p y ≤ p (y - x) + p x := by
    simpa using map_add_le_add p (y - x) x
  have h₁ := hle (x - y)
  have h₂ := hle (y - x)
  rw [norm_sub_rev] at h₂
  rw [Real.coe_toNNReal C hC.le, Real.dist_eq, dist_eq_norm]
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- Let $E$ be a finite-dimensional real normed space, and let $p$ be a definite seminorm on $E$,
that is, $p(x) = 0$ implies $x = 0$. Then $p$ dominates a multiple of the norm: there is $c > 0$
with $c \|x\| \le p(x)$ for all $x \in E$.

This is the half that needs compactness. The seminorm $p$ is continuous and positive on the unit
sphere, which is compact, so $p$ has a positive minimum there, and homogeneity extends the bound
to all of $E$. -/
theorem exists_mul_norm_le (p : Seminorm ℝ E) (hp : ∀ x : E, p x = 0 → x = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ p x := by
  rcases subsingleton_or_nontrivial E with _ | _
  · refine ⟨1, one_pos, fun x => ?_⟩
    rw [Subsingleton.elim x 0]
    simp
  · have hcpt : IsCompact (sphere (0 : E) 1) := isCompact_sphere 0 1
    have hne : (sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.2 zero_le_one
    obtain ⟨x₀, hx₀, hmin⟩ :=
      hcpt.exists_isMinOn hne p.continuous_of_finiteDimensional.continuousOn
    have hx₀norm : ‖x₀‖ = 1 := mem_sphere_zero_iff_norm.1 hx₀
    have hx₀ne : x₀ ≠ 0 := fun h => by simp [h] at hx₀norm
    have hpos : 0 < p x₀ := lt_of_le_of_ne (apply_nonneg p _) fun h => hx₀ne (hp x₀ h.symm)
    refine ⟨p x₀, hpos, fun x => ?_⟩
    rcases eq_or_ne x 0 with rfl | hxne
    · simp
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hxne
      have hmem : ‖x‖⁻¹ • x ∈ sphere (0 : E) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm]
        field_simp
      have hle : p x₀ ≤ p (‖x‖⁻¹ • x) := hmin hmem
      rw [map_smul_eq_mul, norm_inv, norm_norm] at hle
      rw [mul_comm]
      calc ‖x‖ * p x₀ ≤ ‖x‖ * (‖x‖⁻¹ * p x) := mul_le_mul_of_nonneg_left hle hxpos.le
        _ = p x := by field_simp

/-- **Equivalence of norms in finite dimension.** Let $E$ be a finite-dimensional real normed space,
and let $p$ be a definite seminorm on $E$, that is, $p(x) = 0$ implies $x = 0$. Then there are
constants $c, C > 0$ with $$c \|x\| \le p(x) \le C \|x\| \quad \text{for all } x \in E.$$

The two bounds are `Seminorm.exists_mul_norm_le` and `Seminorm.exists_le_mul_norm`. -/
theorem exists_bounds (p : Seminorm ℝ E) (hp : ∀ x : E, p x = 0 → x = 0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, c * ‖x‖ ≤ p x ∧ p x ≤ C * ‖x‖ := by
  obtain ⟨c, hc, hcle⟩ := p.exists_mul_norm_le hp
  obtain ⟨C, hC, hCle⟩ := p.exists_le_mul_norm
  exact ⟨c, C, hc, hC, fun x => ⟨hcle x, hCle x⟩⟩

/-- Let $E$ be a finite-dimensional real normed space, let $p$ be a definite seminorm on $E$, and
let $(f_k)_{k \in \iota}$ be a family in $E$ with a filter $l$ on $\iota$. Then $p(f_k) \to 0$
along $l$ if and only if $\|f_k\| \to 0$ along $l$.

The two-sided bound $c \|v\| \le p(v) \le C \|v\|$ of `Seminorm.exists_bounds` squeezes each
side by the other. -/
theorem tendsto_apply_iff_tendsto_norm (p : Seminorm ℝ E) (hp : ∀ x, p x = 0 → x = 0)
    {ι : Type*} {l : Filter ι} (f : ι → E) :
    Tendsto (fun k => p (f k)) l (𝓝 0) ↔ Tendsto (fun k => ‖f k‖) l (𝓝 0) := by
  obtain ⟨c, C, hc, hC, h⟩ := p.exists_bounds hp
  constructor
  · intro hf
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hf.const_mul c⁻¹) (fun k => norm_nonneg _) fun k => ?_
    rw [le_inv_mul_iff₀ hc]
    exact (h (f k)).1
  · intro hf
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hf.const_mul C) (fun k => apply_nonneg p _) fun k => (h (f k)).2

/-! ### Root asymptotics are the same for every norm -/

/-- Let $c > 0$. Then $c^{1/k} \to 1$ as $k \to \infty$ over the natural numbers.

This is why the constant factor between two equivalent norms does not change a limit of $k$-th
roots. -/
theorem _root_.tendsto_const_rpow_one_div_natCast {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k : ℕ => c ^ (1 / k : ℝ)) atTop (𝓝 1) := by
  have h : Tendsto (fun k : ℕ => Real.log c * (1 / k : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.log c)
  simpa [Function.comp_def, Real.rpow_def_of_pos hc] using
    (Real.continuous_exp.tendsto 0).comp h

/-- Let $E$ be a finite-dimensional real normed space, let $p$ be a definite seminorm on $E$, and
let $(f_k)_{k \in \mathbb{N}}$ be a sequence in $E$. If $\|f_k\|^{1/k} \to L$ as $k \to \infty$,
then $$p(f_k)^{1/k} \to L.$$

By `Seminorm.exists_bounds` the two sequences differ by factors $c^{1/k}$ and $C^{1/k}$, and
both tend to $1$. No submultiplicativity is used. So a limit of Gelfand type
$\|A^k\|^{1/k} \to \rho(A)$, proved for one convenient norm, holds at once for every norm. The
exponent $1/k$ is a real power, and at $k = 0$ it is $0$ because $1/0 = 0$ in Lean. -/
theorem tendsto_rpow_one_div (p : Seminorm ℝ E) (hp : ∀ x : E, p x = 0 → x = 0) {f : ℕ → E}
    {L : ℝ} (hf : Tendsto (fun k : ℕ => ‖f k‖ ^ (1 / k : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun k : ℕ => p (f k) ^ (1 / k : ℝ)) atTop (𝓝 L) := by
  obtain ⟨c, C, hc, hC, hb⟩ := p.exists_bounds hp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun k : ℕ => c ^ (1 / k : ℝ) * ‖f k‖ ^ (1 / k : ℝ))
    (h := fun k : ℕ => C ^ (1 / k : ℝ) * ‖f k‖ ^ (1 / k : ℝ))
    (by simpa using (tendsto_const_rpow_one_div_natCast hc).mul hf)
    (by simpa using (tendsto_const_rpow_one_div_natCast hC).mul hf) (fun k => ?_) fun k => ?_
  · dsimp only
    rw [← Real.mul_rpow hc.le (norm_nonneg _)]
    exact Real.rpow_le_rpow (by positivity) (hb (f k)).1 (by positivity)
  · dsimp only
    rw [← Real.mul_rpow hC.le (norm_nonneg _)]
    exact Real.rpow_le_rpow (apply_nonneg p _) (hb (f k)).2 (by positivity)

end Seminorm

/-! ### Seminorms on `n → 𝕜` over `RCLike 𝕜` -/

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-- Let $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $n$ be a finite type, and let $p$ be a
definite seminorm on $\mathbb{K}^n$ over $\mathbb{K}$, that is, $p(x) = 0$ implies $x = 0$. Then
there are constants $c, C > 0$ with $c \|x\|_\infty \le p(x) \le C \|x\|_\infty$ for all
$x \in \mathbb{K}^n$.

The norm on `n → 𝕜` is the sup norm. The proof applies `Seminorm.exists_bounds` to the
restriction of scalars of $p$ to $\mathbb{R}$. -/
theorem Seminorm.exists_bounds_rclike (p : Seminorm 𝕜 (n → 𝕜)) (hp : ∀ x, p x = 0 → x = 0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, c * ‖x‖ ≤ p x ∧ p x ≤ C * ‖x‖ :=
  (p.restrictScalars ℝ).exists_bounds hp

omit [Fintype n] in
/-- Let $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$ and let $n$ be a finite type. Every seminorm on
$\mathbb{K}^n$ over $\mathbb{K}$ is continuous. -/
theorem Seminorm.continuous_rclike [Finite n] (p : Seminorm 𝕜 (n → 𝕜)) : Continuous p := by
  cases nonempty_fintype n
  exact (p.restrictScalars ℝ).continuous_of_finiteDimensional

end RCLike
