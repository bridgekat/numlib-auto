import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Atkinson–Han §1.2: normed spaces

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §1.2: normed spaces, convergence, equivalence of
norms, Banach spaces, the completion of a normed space, and the two facts from measure theory
(§1.2.3) that the book records for later use.

The definitions of the section — norm, seminorm, ball, open and closed set, convergence,
continuity, series, dense subset, separability, Schauder basis, Cauchy sequence, completeness — are
Mathlib's `Norm`, `Seminorm`, `Metric.ball`, `IsOpen`, `IsClosed`, `Filter.Tendsto`,
`SeqContinuous`, `Dense`, `TopologicalSpace.SeparableSpace`, `SchauderBasis`, `CauchySeq` and
`CompleteSpace`, and each is restated here under the book's number.

## Main definitions

* `definition_1_2_2` — a semi-norm: a norm without the requirement that `|v| = 0` force `v = 0`.
* `definition_1_2_8` — convergence `uₙ → u`, spelled `‖uₙ - u‖ → 0`.
* `definition_1_2_9` — continuity at a point, in the book's sequential form.
* `definition_1_2_17` — convergence of the series `∑ vᵢ`, through its partial sums.
* `definition_1_2_18` — `V₁` is dense in `V₂`.
* `definition_1_2_20`, `definition_1_2_20_schauder` — the two clauses of Definition 1.2.20: a
  countably-infinite basis, which is what the book calls separability, and a Schauder basis.
* `definition_1_2_21` — a Cauchy sequence.

## Main results

* `definition_1_2_1` — Mathlib's norm satisfies exactly the three axioms the book lists.
* `definition_1_2_2_iff`, `definition_1_2_8_iff`, `definition_1_2_9_iff`, `definition_1_2_17_iff`,
  `definition_1_2_18_iff`, `definition_1_2_21_iff` — each restated definition read back as the
  Mathlib notion; later chapters rewrite along these.
* `definition_1_2_6`, `definition_1_2_7` — the open and closed balls, and open and closed sets.
* `definition_1_2_24` — a normed space is complete, that is a Banach space, exactly when every
  Cauchy sequence in it converges.
* `proposition_1_2_10` — the norm is a continuous function, in the sequential form of the book.
* `theorem_1_2_14` — any two norms on a finite-dimensional space are equivalent.
* `proposition_1_2_23` — a Cauchy sequence with a convergent subsequence converges.
* `theorem_1_2_25`, `theorem_1_2_25_uniqueness` — the completion of a normed space, and its
  uniqueness up to a linear isometric isomorphism fixing the embedded copy of `V`.
* `theorem_1_2_26` — the Lebesgue dominated convergence theorem.
* `theorem_1_2_27` — Fubini's theorem.
* `example_1_2_3`, `example_1_2_4`, `example_1_2_5`, `example_1_2_11`, `example_1_2_13`,
  `example_1_2_15`, `example_1_2_16`, `example_1_2_22` — the illustrations of the section.

## Conventions

The convention of §1.1 continues: a definition naming a property of data is a `def … : Prop` in the
book's words with a companion `…_iff`, and a definition naming a structure carried by a type — here
the norm and completeness — is a theorem recording that Mathlib's class satisfies the book's
axioms.

`ℝ^d` with `‖·‖_p` is `PiLp p (fun _ : Fin d => ℝ)`, whose `p = ∞` case carries the maximum norm;
`ℓᵖ` is `lp (fun _ : ℕ => ℝ) p`; `C[a, b]` is `C(Set.Icc a b, ℝ)` and `C_p(2π)` is
`C(AddCircle (2π), ℝ)`, both normed by the supremum because their domains are compact.

Theorem 1.2.14 is stated in the only shape Lean allows. The book quantifies over two norms on one
linear space; a Lean type carries one norm, so the statement is about two normed types `V` and `W`
and a linear equivalence `e : V ≃ₗ[𝕜] W` between them, the two norms being `‖v‖` and `‖e v‖`.

Theorems 1.2.26 and 1.2.27 are stated over an arbitrary measure space rather than over an open set
of `ℝ^d`, which is how Mathlib has them and how the book uses them.

## Not formalized here

Example 1.2.5 (b), the norm `‖f‖_{k,∞} = max_{j ≤ k} ‖f⁽ʲ⁾‖_∞` of `Cᵏ[a, b]`, and with it
Example 1.2.28 (a), need `Cᵏ[a, b]` as a normed space, which Mathlib does not have — it has
`C(X, ℝ)` for compact `X`, hence only the case `k = 0`. Example 1.2.28 (b) is the Sobolev
completion `W^{m,p}(a, b)` and is out of scope for the project. The second half of Example 1.2.22,
that `C(Ω̄)` with `‖·‖_p` is *not* complete, is an explicit counterexample with no consumer in the
book and no Mathlib form; only its first half is stated. Example 1.2.19 is Theorem 1.5.6 restated
for a bounded `Ω`, and is recorded with it in §1.5.
-/

open ENNReal Filter MeasureTheory Topology

open scoped NNReal Real

namespace AtkinsonHan.Chapter01

section Normed

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Definition 1.2.1.** A *norm* on a linear space `V` is a function `‖·‖ : V → ℝ` such that
`‖v‖ ≥ 0` with `‖v‖ = 0` if and only if `v = 0`; `‖α v‖ = |α| ‖v‖` (positive homogeneity); and
`‖u + v‖ ≤ ‖u‖ + ‖v‖` (the triangle inequality). The pair `(V, ‖·‖)` is a *normed space*.

This is Mathlib's `Norm`, bundled as `NormedAddCommGroup V` with `NormedSpace 𝕜 V`, and the
statement below is that the bundle satisfies exactly the book's three axioms. -/
theorem definition_1_2_1 (𝕜 V : Type*) [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V] :
    (∀ v : V, 0 ≤ ‖v‖ ∧ (‖v‖ = 0 ↔ v = 0)) ∧
      (∀ (α : 𝕜) (v : V), ‖α • v‖ = ‖α‖ * ‖v‖) ∧
      (∀ u v : V, ‖u + v‖ ≤ ‖u‖ + ‖v‖) :=
  ⟨fun v => ⟨norm_nonneg v, norm_eq_zero⟩, norm_smul, norm_add_le⟩

/-- **Definition 1.2.2.** A *semi-norm* `|·|` on a linear space has the properties of a norm
(Definition 1.2.1) except that `|v| = 0` need not imply `v = 0`.

This is Mathlib's `Seminorm 𝕜 V`; `definition_1_2_2_iff` is the correspondence. The book uses
semi-norms for the error of polynomial interpolation, which this surface reaches in Chapter 3. -/
def definition_1_2_2 (𝕜 : Type*) {V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    (p : V → ℝ) : Prop :=
  (∀ v : V, 0 ≤ p v) ∧ (∀ (α : 𝕜) (v : V), p (α • v) = ‖α‖ * p v) ∧
    ∀ u v : V, p (u + v) ≤ p u + p v

/-- Definition 1.2.2 is Mathlib's `Seminorm`. -/
theorem definition_1_2_2_iff (p : V → ℝ) :
    definition_1_2_2 𝕜 p ↔ ∃ q : Seminorm 𝕜 V, ⇑q = p := by
  constructor
  · rintro ⟨-, hsmul, hadd⟩
    refine ⟨⟨⟨p, ?_, hadd, fun v => ?_⟩, hsmul⟩, rfl⟩
    · simpa using hsmul 0 0
    · simpa using hsmul (-1) v
  · rintro ⟨q, rfl⟩
    exact ⟨fun v => apply_nonneg q v, fun α v => map_smul_eq_mul q α v,
      fun u v => map_add_le_add q u v⟩

/-- **Example 1.2.3.** The `p`-norms (1.2.2)–(1.2.3) on `ℝ^d`: `‖x‖_p = (∑ |xᵢ|^p)^{1/p}` for
`1 ≤ p < ∞`, and the maximum norm `‖x‖_∞ = maxᵢ |xᵢ|`. In Mathlib these live on `PiLp p`, of which
`EuclideanSpace ℝ (Fin d)` is the case `p = 2`. -/
theorem example_1_2_3 (d : ℕ) :
    (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → ∀ x : PiLp p fun _ : Fin d => ℝ,
        ‖x‖ = (∑ i, |x i| ^ p.toReal) ^ (1 / p.toReal)) ∧
      (∀ x : PiLp ∞ fun _ : Fin d => ℝ, ‖x‖ = ⨆ i, |x i|) := by
  refine ⟨fun p _ hp x => ?_, fun x => ?_⟩
  · rw [PiLp.norm_eq_sum (p.toReal_pos_iff_ne_top.mpr hp)]
    simp [Real.norm_eq_abs]
  · rw [PiLp.norm_eq_ciSup]
    simp [Real.norm_eq_abs]

/-- **Example 1.2.4.** For `p ∈ [1, ∞]` the sequence space `ℓᵖ` is the set of sequences of finite
`‖·‖_{ℓᵖ}` norm, `‖v‖_{ℓᵖ} = (∑_{n ≥ 1} |vₙ|^p)^{1/p}` for `p < ∞` and `‖v‖_{ℓ^∞} = sup_n |vₙ|`.

This is Mathlib's `lp (fun _ : ℕ => ℝ) p`, the subtype of the sequences satisfying `Memℓp`; its
norm instance carries the triangle inequality that the book defers to Exercise 1.5.11. -/
theorem example_1_2_4 :
    (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → ∀ v : lp (fun _ : ℕ => ℝ) p,
        ‖v‖ = (∑' n, |v n| ^ p.toReal) ^ (1 / p.toReal)) ∧
      (∀ v : lp (fun _ : ℕ => ℝ) ∞, ‖v‖ = ⨆ n, |v n|) := by
  refine ⟨fun p _ hp v => ?_, fun v => ?_⟩
  · rw [lp.norm_eq_tsum_rpow (p.toReal_pos_iff_ne_top.mpr hp)]
    simp [Real.norm_eq_abs]
  · rw [lp.norm_eq_ciSup]
    simp [Real.norm_eq_abs]

section Periodic

/-- `2π` is positive, which is what makes `AddCircle (2π)` a compact space and `C_p(2π)` a normed
space. -/
local instance instFactTwoPiPos : Fact (0 < 2 * π) := Fact.mk Real.two_pi_pos

/-- **Example 1.2.5** (a). The standard norm of `C[a, b]` is the maximum norm
`‖f‖_∞ = max_{a ≤ x ≤ b} |f x|`, and the same formula is the standard norm of `C_p(2π)`, the
continuous `2π`-periodic functions. Both are Mathlib's supremum norm on `C(X, ℝ)` for a compact
`X`. -/
theorem example_1_2_5 {a b : ℝ} :
    (∀ f : C(Set.Icc a b, ℝ), ‖f‖ = ⨆ x, |f x|) ∧
      (∀ f : C(AddCircle (2 * π), ℝ), ‖f‖ = ⨆ x, |f x|) :=
  ⟨fun f => by simpa [Real.norm_eq_abs] using f.norm_eq_iSup_norm,
    fun f => by simpa [Real.norm_eq_abs] using f.norm_eq_iSup_norm⟩

end Periodic

/-- **Definition 1.2.6.** For `v₀` in a normed space and `r > 0`, the *open ball*
`B(v₀, r) = {v | ‖v - v₀‖ < r}` and the *closed ball* `B̄(v₀, r) = {v | ‖v - v₀‖ ≤ r}`; at `v₀ = 0`
and `r = 1` these are the unit balls.

These are Mathlib's `Metric.ball` and `Metric.closedBall` for the metric the norm induces. -/
theorem definition_1_2_6 (v₀ : V) (r : ℝ) :
    Metric.ball v₀ r = {v | ‖v - v₀‖ < r} ∧ Metric.closedBall v₀ r = {v | ‖v - v₀‖ ≤ r} :=
  ⟨by ext v; simp [Metric.mem_ball, dist_eq_norm],
    by ext v; simp [Metric.mem_closedBall, dist_eq_norm]⟩

/-- **Definition 1.2.7.** A set `A` in a normed space is *open* if every `v ∈ A` has a ball
`B(v, r) ⊆ A`, and *closed* in `V` if its complement `V \ A` is open.

These are Mathlib's `IsOpen` and `IsClosed` for the metric topology the norm induces. -/
theorem definition_1_2_7 (A : Set V) :
    (IsOpen A ↔ ∀ v ∈ A, ∃ r > 0, Metric.ball v r ⊆ A) ∧ (IsClosed A ↔ IsOpen Aᶜ) :=
  ⟨Metric.isOpen_iff, isOpen_compl_iff.symm⟩

/-- **Definition 1.2.8.** A sequence `{uₙ}` in a normed space *converges* to `u` when
`‖uₙ - u‖ → 0`; `u` is then the limit of the sequence, and a sequence has at most one limit
(`definition_1_2_8_unique`).

This is Mathlib's `Filter.Tendsto u atTop (𝓝 u₀)` by `definition_1_2_8_iff`. -/
def definition_1_2_8 {V : Type*} [NormedAddCommGroup V] (u : ℕ → V) (v : V) : Prop :=
  Tendsto (fun n => ‖u n - v‖) atTop (𝓝 0)

/-- Definition 1.2.8 is Mathlib's `Filter.Tendsto _ atTop (𝓝 _)`. -/
theorem definition_1_2_8_iff (u : ℕ → V) (v : V) :
    definition_1_2_8 u v ↔ Tendsto u atTop (𝓝 v) :=
  tendsto_iff_norm_sub_tendsto_zero.symm

/-- A sequence in a normed space has at most one limit, as the book records after
Definition 1.2.8. -/
theorem definition_1_2_8_unique {u : ℕ → V} {v w : V} (hv : definition_1_2_8 u v)
    (hw : definition_1_2_8 u w) : v = w :=
  tendsto_nhds_unique ((definition_1_2_8_iff u v).mp hv) ((definition_1_2_8_iff u w).mp hw)

/-- **Definition 1.2.9.** A function `f : V → ℝ` is *continuous at* `u ∈ V` if `uₙ → u` implies
`f uₙ → f u`, and *continuous on* `V` if it is continuous at every `u ∈ V`.

The book's sequential form is Mathlib's `SeqContinuous`, which agrees with `Continuous` on a metric
space; `definition_1_2_9_iff` is the correspondence. -/
def definition_1_2_9 {V : Type*} [NormedAddCommGroup V] (f : V → ℝ) (u : V) : Prop :=
  ∀ v : ℕ → V, definition_1_2_8 v u → definition_1_2_8 (fun n => f (v n)) (f u)

/-- Continuity at every point in the sequential sense of Definition 1.2.9 is Mathlib's
`Continuous`. -/
theorem definition_1_2_9_iff (f : V → ℝ) : (∀ u, definition_1_2_9 f u) ↔ Continuous f := by
  rw [continuous_iff_seqContinuous]
  constructor
  · intro h x y hxy
    exact (definition_1_2_8_iff _ _).mp (h y x ((definition_1_2_8_iff _ _).mpr hxy))
  · intro h u v hv
    exact (definition_1_2_8_iff _ _).mpr (h ((definition_1_2_8_iff _ _).mp hv))

/-- **Proposition 1.2.10.** The norm is a continuous function: if `uₙ → u` then `‖uₙ‖ → ‖u‖`. The
book's proof is the backward triangle inequality (1.2.5), `|‖u‖ - ‖v‖| ≤ ‖u - v‖`, which is
Mathlib's `abs_norm_sub_norm_le`. -/
theorem proposition_1_2_10 {u : ℕ → V} {v : V} (h : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖v‖) :=
  h.norm

/-- **Example 1.2.11.** On `V = C[0, 1]` the point evaluation `ℓ_{x₀} v = v x₀` is continuous, in
the sense of Definition 1.2.9, because `|ℓ_{x₀} vₙ - ℓ_{x₀} v| ≤ ‖vₙ - v‖_∞`. The book returns to it
as a linear functional in Chapter 2, where this surface states it again. -/
theorem example_1_2_11 (x₀ : Set.Icc (0 : ℝ) 1) (u : C(Set.Icc (0 : ℝ) 1, ℝ)) :
    definition_1_2_9 (fun v : C(Set.Icc (0 : ℝ) 1, ℝ) => v x₀) u :=
  (definition_1_2_9_iff _).mpr (continuous_eval_const x₀) u

/-- **Example 1.2.13**, the inequality (1.2.6): on `ℝ^d`, `‖x‖_∞ ≤ ‖x‖_p ≤ d^{1/p} ‖x‖_∞` for
`1 ≤ p < ∞`, so all the `p`-norms on `ℝ^d` are equivalent — a special case of
`theorem_1_2_14`. -/
theorem example_1_2_13 {d : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : Fin d → ℝ) :
    ‖(WithLp.toLp ∞ x : PiLp ∞ fun _ : Fin d => ℝ)‖ ≤
        ‖(WithLp.toLp p x : PiLp p fun _ : Fin d => ℝ)‖ ∧
      ‖(WithLp.toLp p x : PiLp p fun _ : Fin d => ℝ)‖ ≤
        (d : ℝ) ^ (1 / p.toReal) * ‖(WithLp.toLp ∞ x : PiLp ∞ fun _ : Fin d => ℝ)‖ := by
  have hK : (((Fintype.card (Fin d) : ℝ≥0) ^ (1 / p).toReal : ℝ≥0) : ℝ)
      = (d : ℝ) ^ (1 / p.toReal) := by
    rw [Fintype.card_fin, NNReal.coe_rpow, NNReal.coe_natCast, ENNReal.toReal_div,
      ENNReal.toReal_one]
  refine ⟨?_, ?_⟩
  · rw [PiLp.norm_eq_ciSup]
    refine Real.iSup_le (fun i => ?_) (norm_nonneg _)
    simpa using PiLp.norm_apply_le (WithLp.toLp p x) i
  · have h := (PiLp.lipschitzWith_toLp p fun _ : Fin d => ℝ).dist_le_mul x 0
    simp only [WithLp.toLp_zero, dist_zero_right] at h
    rw [PiLp.norm_toLp, ← hK]
    exact h

/-- **Example 1.2.15.** On `C[0, 1]` the norms `‖·‖_p`, `1 ≤ p < ∞`, and `‖·‖_∞` are *not*
equivalent: there is no constant `c` with `‖v‖_∞ ≤ c ‖v‖_p` for every `v`. The statement below is
that negation in witness form — for every `c` some `v ∈ C[0, 1]` has `‖v‖_∞ = 1` while
`c ‖v‖_p < 1`.

The book's witnesses are the ramps `uₙ x = max (1 - n x) 0`, of `p`-norm `[n (p + 1)]^{-1/p}`; the
witnesses below are `vₙ x = (1 - x)ⁿ`, whose `p`-norm `(n p + 1)^{-1/p}` is as easy to compute and
avoids a piecewise definition. -/
theorem example_1_2_15 {p : ℝ} (hp : 1 ≤ p) (c : ℝ) :
    ∃ v : ℝ → ℝ, Continuous v ∧ (∀ x ∈ Set.Icc (0 : ℝ) 1, |v x| ≤ 1) ∧ v 0 = 1 ∧
      c * (∫ x in (0 : ℝ)..1, |v x| ^ p) ^ (1 / p) < 1 := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  -- the witness `vₙ x = (1 - x)ⁿ`, for an `n` chosen below
  set n : ℕ := ⌈max c 0 ^ p⌉₊ with hn
  refine ⟨fun x => (1 - x) ^ n, by fun_prop, fun x hx => ?_, by simp, ?_⟩
  · rw [abs_pow]
    refine pow_le_one₀ (abs_nonneg _) ?_
    rw [abs_le]
    constructor <;> [linarith [hx.2]; linarith [hx.1]]
  -- the integral is `1 / (n p + 1)`
  have hr : (0 : ℝ) ≤ (n : ℝ) * p := by positivity
  have hint : (∫ x in (0 : ℝ)..1, |(1 - x) ^ n| ^ p) = 1 / ((n : ℝ) * p + 1) := by
    have hcongr : ∀ x ∈ Set.uIcc (0 : ℝ) 1, |(1 - x) ^ n| ^ p = (1 - x) ^ ((n : ℝ) * p) := by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      have h1x : (0 : ℝ) ≤ 1 - x := by linarith [hx.2]
      rw [abs_of_nonneg (pow_nonneg h1x n), ← Real.rpow_natCast (1 - x) n,
        ← Real.rpow_mul h1x]
    rw [intervalIntegral.integral_congr hcongr,
      intervalIntegral.integral_comp_sub_left (fun x => x ^ ((n : ℝ) * p)) 1]
    norm_num
    rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < (n : ℝ) * p)), Real.one_rpow,
      Real.zero_rpow (by linarith), sub_zero, one_div]
  rw [hint]
  rcases le_or_gt c 0 with hc | hc
  · have : (0 : ℝ) ≤ (1 / ((n : ℝ) * p + 1)) ^ (1 / p) :=
      Real.rpow_nonneg (by positivity) _
    nlinarith
  -- for `c > 0`, `n` was chosen so that `n p + 1 > c ^ p`
  · have hcp : max c 0 ^ p ≤ (n : ℝ) := Nat.le_ceil _
    have hcp' : c ^ p < (n : ℝ) * p + 1 := by
      have hmax : max c 0 = c := max_eq_left hc.le
      rw [hmax] at hcp
      nlinarith [Real.rpow_nonneg hc.le p]
    have hcppos : (0 : ℝ) < c ^ p := Real.rpow_pos_of_pos hc p
    have hlt : (1 / ((n : ℝ) * p + 1)) ^ (1 / p) < (1 / c ^ p) ^ (1 / p) := by
      refine Real.rpow_lt_rpow (by positivity) ?_ (by positivity)
      exact one_div_lt_one_div_of_lt hcppos hcp'
    have heq : (1 / c ^ p) ^ (1 / p) = 1 / c := by
      rw [one_div, one_div, Real.inv_rpow (le_of_lt hcppos), ← Real.rpow_mul hc.le,
        mul_inv_cancel₀ hp0.ne', Real.rpow_one, one_div]
    rw [heq] at hlt
    calc c * (1 / ((n : ℝ) * p + 1)) ^ (1 / p) < c * (1 / c) := by
          exact mul_lt_mul_of_pos_left hlt hc
      _ = 1 := by field_simp

/-- **Example 1.2.16.** On `C[0, 1]` one has `‖v‖_p ≤ ‖v‖_∞` for every `p ∈ [1, ∞)`, so uniform
convergence implies convergence in `‖·‖_p` — but not conversely, which is Example 1.2.15.

The uniform norm appears as an arbitrary bound `M` on `|v|` over `[0, 1]`, which is what the book's
`‖v‖_∞` is; the general form of the inequality, the inclusion `L^q ⊆ Lᵖ` with the constant
`meas(Ω)^{1/p - 1/q}`, is `theorem_1_5_5_c`. -/
theorem example_1_2_16 {p : ℝ} (hp : 1 ≤ p) {v : ℝ → ℝ} (hv : ContinuousOn v (Set.Icc 0 1))
    {M : ℝ} (hM : ∀ x ∈ Set.Icc (0 : ℝ) 1, |v x| ≤ M) :
    (∫ x in (0 : ℝ)..1, |v x| ^ p) ^ (1 / p) ≤ M := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 (by norm_num))
  have hcont : ContinuousOn (fun x => |v x| ^ p) (Set.Icc 0 1) :=
    hv.abs.rpow_const fun _ _ => Or.inr hp0.le
  have hint : IntervalIntegrable (fun x => |v x| ^ p) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hle : (∫ x in (0 : ℝ)..1, |v x| ^ p) ≤ M ^ p := by
    have hmono : (∫ x in (0 : ℝ)..1, |v x| ^ p) ≤ ∫ _ in (0 : ℝ)..1, M ^ p := by
      refine intervalIntegral.integral_mono_on (by norm_num) hint intervalIntegrable_const ?_
      intro x hx
      exact Real.rpow_le_rpow (abs_nonneg _) (hM x hx) hp0.le
    simpa using hmono
  have hnn : 0 ≤ ∫ x in (0 : ℝ)..1, |v x| ^ p :=
    intervalIntegral.integral_nonneg (by norm_num) fun x _ => Real.rpow_nonneg (abs_nonneg _) p
  calc (∫ x in (0 : ℝ)..1, |v x| ^ p) ^ (1 / p)
      ≤ (M ^ p) ^ (1 / p) := Real.rpow_le_rpow hnn hle (by positivity)
    _ = M := by
        rw [← Real.rpow_mul hM0, mul_one_div_cancel hp0.ne', Real.rpow_one]

/-- **Definition 1.2.17.** For a sequence `{vₙ}` in a normed space with partial sums
`sₙ = ∑_{i ≤ n} vᵢ`, the series `∑_{i ≥ 1} vᵢ` *converges to* `s` when `sₙ → s` in `V`.

This is the ordered form of summation, `Tendsto (fun n => ∑ i ∈ Finset.range n, v i) atTop (𝓝 s)`;
Mathlib's `HasSum` is the unordered variant, and the two agree for the unconditionally convergent
series the book meets. -/
def definition_1_2_17 {V : Type*} [NormedAddCommGroup V] (v : ℕ → V) (s : V) : Prop :=
  definition_1_2_8 (fun n => ∑ i ∈ Finset.range n, v i) s

/-- Definition 1.2.17 is the convergence of the partial sums. -/
theorem definition_1_2_17_iff (v : ℕ → V) (s : V) :
    definition_1_2_17 v s ↔ Tendsto (fun n => ∑ i ∈ Finset.range n, v i) atTop (𝓝 s) :=
  definition_1_2_8_iff _ _

/-- **Definition 1.2.18.** For subsets `V₁ ⊆ V₂` of a normed space, `V₁` is *dense in* `V₂` when
every `u ∈ V₂` and every `ε > 0` admit a `v ∈ V₁` with `‖v - u‖ < ε`.

This is `V₂ ⊆ closure V₁` in Mathlib, and Mathlib's `Dense` when `V₂` is everything;
`definition_1_2_18_iff` and `definition_1_2_18_iff_dense` are the two correspondences. -/
def definition_1_2_18 {V : Type*} [NormedAddCommGroup V] (V₁ V₂ : Set V) : Prop :=
  ∀ u ∈ V₂, ∀ ε > 0, ∃ v ∈ V₁, ‖v - u‖ < ε

/-- Definition 1.2.18 says exactly that `V₂` lies in the closure of `V₁`. -/
theorem definition_1_2_18_iff (V₁ V₂ : Set V) :
    definition_1_2_18 V₁ V₂ ↔ V₂ ⊆ closure V₁ := by
  constructor
  · intro h u hu
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨v, hv, hvu⟩ := h u hu ε hε
    exact ⟨v, hv, by rwa [dist_eq_norm, norm_sub_rev]⟩
  · intro h u hu ε hε
    obtain ⟨v, hv, hvu⟩ := Metric.mem_closure_iff.mp (h hu) ε hε
    exact ⟨v, hv, by rwa [dist_eq_norm, norm_sub_rev] at hvu⟩

/-- A subset dense in the whole space in the sense of Definition 1.2.18 is Mathlib's `Dense`. -/
theorem definition_1_2_18_iff_dense (V₁ : Set V) :
    definition_1_2_18 V₁ Set.univ ↔ Dense V₁ := by
  rw [definition_1_2_18_iff, dense_iff_closure_eq, Set.univ_subset_iff, eq_comm]

/-- **Definition 1.2.20** (a). An infinite dimensional normed space `V` has a
*countably-infinite basis* `{vᵢ}` when for every `v ∈ V` there are scalars `{α_{n,i}}` with
`‖v - ∑_{i < n} α_{n,i} vᵢ‖ → 0`; `V` is then also said to be *separable*, and `{vᵢ}` is called a
basis when each of its finite subfamilies is linearly independent.

The approximation property below is what makes `V` separable, Mathlib's
`TopologicalSpace.SeparableSpace`; the independence rider is Definition 1.1.5. -/
def definition_1_2_20 (𝕜 : Type*) {V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    (v : ℕ → V) : Prop :=
  ∀ u : V, ∃ α : ℕ → ℕ → 𝕜, definition_1_2_8 (fun n => ∑ i ∈ Finset.range n, α n i • v i) u

/-- **Definition 1.2.20** (b). A normed space `V` has a *Schauder basis* `{vₙ}` when every `v ∈ V`
is a convergent series `v = ∑_{n ≥ 1} αₙ vₙ` for a unique choice of scalars `{αₙ}`.

This is Mathlib's `SchauderBasis 𝕜 V`, an abbreviation for
`GeneralSchauderBasis ℕ 𝕜 V (SummationFilter.conditional ℕ)`. A Schauder basis is in particular a
countably-infinite basis in the sense of clause (a). -/
def definition_1_2_20_schauder (𝕜 : Type*) {V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] (v : ℕ → V) : Prop :=
  ∀ u : V, ∃! α : ℕ → 𝕜, definition_1_2_17 (fun n => α n • v n) u

/-- Clause (b) of Definition 1.2.20 implies clause (a): a Schauder basis is a countably-infinite
basis, taking `α_{n,i} = αᵢ` independent of `n`. -/
theorem definition_1_2_20_of_schauder {v : ℕ → V} (h : definition_1_2_20_schauder 𝕜 v) :
    definition_1_2_20 𝕜 v := by
  intro u
  obtain ⟨α, hα, -⟩ := h u
  exact ⟨fun _ i => α i, hα⟩

/-- **Definition 1.2.21.** A sequence `{uₙ}` in a normed space is a *Cauchy sequence* when
`‖u_m - uₙ‖ → 0` as `m, n → ∞`.

This is Mathlib's `CauchySeq`; `definition_1_2_21_iff` is the correspondence. -/
def definition_1_2_21 {V : Type*} [NormedAddCommGroup V] (u : ℕ → V) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ‖u m - u n‖ < ε

/-- Definition 1.2.21 is Mathlib's `CauchySeq`. -/
theorem definition_1_2_21_iff (u : ℕ → V) : definition_1_2_21 u ↔ CauchySeq u := by
  rw [Metric.cauchySeq_iff]
  simp [definition_1_2_21, dist_eq_norm]

/-- **Example 1.2.22**, first half. `C(Ω̄)` with the maximum norm is a Banach space, because a
uniform limit of continuous functions is continuous. The second half of the example, that `C(Ω̄)`
with `‖·‖_p` for `1 ≤ p < ∞` is *not* complete, is an explicit counterexample and is not
stated. -/
theorem example_1_2_22 {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} (hD : IsCompact D) :
    CompleteSpace C(D, ℝ) :=
  have : CompactSpace D := isCompact_iff_compactSpace.mp hD
  inferInstance

/-- **Proposition 1.2.23.** A Cauchy sequence with a convergent subsequence converges, to the same
limit. -/
theorem proposition_1_2_23 {u : ℕ → V} (hu : CauchySeq u) {φ : ℕ → ℕ} (hφ : StrictMono φ) {v : V}
    (h : Tendsto (u ∘ φ) atTop (𝓝 v)) : Tendsto u atTop (𝓝 v) :=
  tendsto_nhds_of_cauchySeq_of_subseq hu hφ.tendsto_atTop h

/-- **Definition 1.2.24.** A normed space is *complete* when every Cauchy sequence from the space
converges to an element of the space, and a complete normed space is a *Banach space*.

This is Mathlib's `CompleteSpace` beside `NormedAddCommGroup` and `NormedSpace`. Mathlib bundles no
`BanachSpace`, and that hypothesis triple is what this surface carries throughout. -/
theorem definition_1_2_24 (V : Type*) [NormedAddCommGroup V] :
    CompleteSpace V ↔ ∀ u : ℕ → V, definition_1_2_21 u → ∃ v : V, definition_1_2_8 u v := by
  simp only [definition_1_2_21_iff, definition_1_2_8_iff]
  exact ⟨fun _ _ hu => cauchySeq_tendsto_of_complete hu, Metric.complete_of_cauchySeq_tendsto⟩

/-- **Theorem 1.2.14.** On a finite-dimensional linear space any two norms are equivalent: for a
linear equivalence `e : V ≃ₗ[𝕜] W` between normed spaces with `V` finite-dimensional there are
`c₁, c₂ > 0` with `c₁ ‖v‖ ≤ ‖e v‖ ≤ c₂ ‖v‖`. Both bounds come from the continuity of a linear map
on a finite-dimensional space, applied to `e` and to `e.symm`. -/
theorem theorem_1_2_14 {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    [FiniteDimensional 𝕜 V] (e : V ≃ₗ[𝕜] W) :
    ∃ c₁ > 0, ∃ c₂ > 0, ∀ v : V, c₁ * ‖v‖ ≤ ‖e v‖ ∧ ‖e v‖ ≤ c₂ * ‖v‖ := by
  have _ : FiniteDimensional 𝕜 W := e.finiteDimensional
  set E : V ≃L[𝕜] W := e.toContinuousLinearEquiv
  have hcoe : ∀ v : V, E v = e v := fun _ => rfl
  refine ⟨(‖(E.symm : W →L[𝕜] V)‖ + 1)⁻¹, by positivity, ‖(E : V →L[𝕜] W)‖ + 1, by positivity,
    fun v => ⟨?_, ?_⟩⟩
  · rw [inv_mul_le_iff₀ (by positivity), ← hcoe]
    calc ‖v‖ = ‖E.symm (E v)‖ := by simp
      _ ≤ ‖(E.symm : W →L[𝕜] V)‖ * ‖E v‖ := (E.symm : W →L[𝕜] V).le_opNorm _
      _ ≤ (‖(E.symm : W →L[𝕜] V)‖ + 1) * ‖E v‖ := by nlinarith [norm_nonneg (E v)]
  · rw [← hcoe]
    calc ‖E v‖ ≤ ‖(E : V →L[𝕜] W)‖ * ‖v‖ := (E : V →L[𝕜] W).le_opNorm _
      _ ≤ (‖(E : V →L[𝕜] W)‖ + 1) * ‖v‖ := by nlinarith [norm_nonneg v]

/-- **Theorem 1.2.25** (existence of a completion). Every normed space `V` has a completion: the
Banach space `UniformSpace.Completion V` together with the linear isometry
`UniformSpace.Completion.toComplₗᵢ`, whose range is dense. -/
theorem theorem_1_2_25 :
    CompleteSpace (UniformSpace.Completion V) ∧
      DenseRange (UniformSpace.Completion.toComplₗᵢ : V →ₗᵢ[𝕜] UniformSpace.Completion V) :=
  ⟨inferInstance, UniformSpace.Completion.denseRange_coe⟩

/-- **Theorem 1.2.25** (uniqueness of the completion). Any Banach space `W` carrying a linear
isometry `I : V →ₗᵢ[𝕜] W` with dense range is a copy of `UniformSpace.Completion V`: there is a
surjective linear isometry from the completion onto `W` extending `I`. Two completions of `V` are
therefore isometrically isomorphic by an isomorphism fixing the embedded copy of `V`. -/
theorem theorem_1_2_25_uniqueness {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    [CompleteSpace W] (I : V →ₗᵢ[𝕜] W) (hI : DenseRange I) :
    ∃ e : UniformSpace.Completion V ≃ₗᵢ[𝕜] W, ∀ v : V, e v = I v := by
  set f : UniformSpace.Completion V →L[𝕜] W := I.toContinuousLinearMap.fromCompletion with hf
  have hcoe : ∀ v : V, f v = I v := by simp [hf]
  have hnorm : ∀ x : UniformSpace.Completion V, ‖f x‖ = ‖x‖ := by
    intro x
    refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop))
      fun v => ?_
    rw [hcoe, I.norm_map, UniformSpace.Completion.norm_coe]
  let g : UniformSpace.Completion V →ₗᵢ[𝕜] W := ⟨f.toLinearMap, hnorm⟩
  have hsub : Set.range I ⊆ Set.range g := by
    rintro w ⟨v, rfl⟩
    exact ⟨(v : UniformSpace.Completion V), hcoe v⟩
  have hsurj : Function.Surjective g :=
    Set.range_eq_univ.mp <| by
      rw [← g.isometry.isClosedEmbedding.isClosed_range.closure_eq, (hI.mono hsub).closure_eq]
  exact ⟨LinearIsometryEquiv.ofSurjective g hsurj, hcoe⟩

end Normed

section Measure

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Theorem 1.2.26**, the Lebesgue dominated convergence theorem, in the book's statement: if
`f n → g` almost everywhere and `‖f n‖ ≤ bound` almost everywhere for an integrable `bound`, then
the limit `g` is integrable and `∫ f n → ∫ g`. -/
theorem theorem_1_2_26 {f : ℕ → α → ℝ} {g : α → ℝ} {bound : α → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hbound : Integrable bound μ)
    (hle : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Integrable g μ ∧ Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  have hgmeas : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae atTop hf hlim
  have hgle : ∀ᵐ x ∂μ, ‖g x‖ ≤ bound x := by
    filter_upwards [ae_all_iff.2 hle, hlim] with x hx hxlim
    exact le_of_tendsto' hxlim.norm hx
  exact ⟨hbound.mono' hgmeas hgle,
    tendsto_integral_of_dominated_convergence bound hf hbound hle hlim⟩

/-- **Theorem 1.2.27**, Fubini's theorem: a function integrable on a product is integrable in each
variable for almost every value of the other, and its double integrals in the two orders agree. -/
theorem theorem_1_2_27 {β : Type*} [MeasurableSpace β] {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α → β → ℝ} (hf : Integrable (Function.uncurry f) (μ.prod ν)) :
    (∀ᵐ x ∂μ, Integrable (f x) ν) ∧ (∀ᵐ y ∂ν, Integrable (fun x => f x y) μ) ∧
      ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫ x, f x y ∂μ ∂ν :=
  ⟨hf.prod_right_ae, hf.prod_left_ae, integral_integral_swap hf⟩

end Measure

end AtkinsonHan.Chapter01
