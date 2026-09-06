import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Atkinson–Han §1.5: the `Lᵖ` spaces

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §1.5: Young's, Hölder's and Minkowski's
inequalities, completeness of `Lᵖ(Ω)`, the inclusions between the `Lᵖ` spaces on a set of finite
measure, and the density of `C₀^∞(Ω)`.

Everything here is Mathlib. The section is stated because it is the book's account of the spaces
every later chapter integrates over, and because Theorem 1.5.5 (c) — the inclusion `Lq ⊆ Lᵖ` with
the explicit constant `meas(Ω)^{1/p - 1/q}` — is the one statement whose Mathlib form is not
obviously the book's.

## Main results

* `lemma_1_5_1`, `lemma_1_5_2` — Young's inequality and its `ε`-weighted form.
* `lemma_1_5_3` — Hölder's inequality.
* `lemma_1_5_4` — Minkowski's inequality.
* `theorem_1_5_5_a`, `theorem_1_5_5_b`, `theorem_1_5_5_c` — the three clauses of Theorem 1.5.5.
* `theorem_1_5_6` — smooth compactly supported functions are dense in `Lᵖ`.

## Conventions

The book's `Ω ⊆ ℝ^d` with Lebesgue measure is an arbitrary measure space here, except in Theorem
1.5.6, where the smoothness of the approximants needs a finite-dimensional real domain. The book's
exponent `p ∈ [1, ∞]` is Mathlib's `p : ℝ≥0∞` with `Fact (1 ≤ p)`, and the book's `‖·‖_{Lᵖ}` is
`MeasureTheory.eLpNorm`, which is the `Lp` norm without the `ENNReal.toReal`.

## Not formalized here

* The Clarkson inequalities (1.5.5)–(1.5.6). The book states them without proof for Exercise
  2.7.4 (b), that `Lᵖ` is uniformly convex; they are not in Mathlib and nothing else uses them.
* Theorem 1.5.6 for a *proper* open `Ω ⊆ ℝ^d`, with the approximants supported inside `Ω`. What is
  proved below is the statement for `Ω = ℝ^d`, which is Mathlib's; the version for a proper open
  set needs a compact exhaustion of `Ω` before the mollification, which Mathlib does not have.

## References

* K. E. Atkinson and W. Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*,
  3rd edition, Texts in Applied Mathematics 39, Springer, 2009.
-/

open Filter MeasureTheory Topology
open scoped ENNReal ContDiff

namespace AtkinsonHan.Chapter01

/-! ### Young's inequality -/

/-- **Lemma 1.5.1**, Young's inequality: `a b ≤ aᵖ/p + b^q/q` for `a, b ≥ 0` and conjugate
exponents `p, q > 1`. -/
theorem lemma_1_5_1 {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hpq : p.HolderConjugate q) :
    a * b ≤ a ^ p / p + b ^ q / q :=
  Real.young_inequality_of_nonneg ha hb hpq

/-- **Lemma 1.5.2**, the modified Young inequality: for every `ε > 0`,
`a b ≤ ε aᵖ/p + ε^{1-q} b^q/q`. It is Lemma 1.5.1 applied to `ε^{1/p} a` and `ε^{-1/p} b`. -/
theorem lemma_1_5_2 {a b p q ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hpq : p.HolderConjugate q)
    (hε : 0 < ε) : a * b ≤ ε * a ^ p / p + ε ^ (1 - q) * b ^ q / q := by
  have hp := hpq.pos
  have hq := hpq.symm.pos
  have hεp : (0 : ℝ) < ε ^ (1 / p) := Real.rpow_pos_of_pos hε _
  have hεm : (0 : ℝ) < ε ^ (-(1 / p)) := Real.rpow_pos_of_pos hε _
  -- `q / p = q - 1`, from `p⁻¹ + q⁻¹ = 1`.
  have hqp : q * (1 / p) = q - 1 := by
    have h := hpq.inv_add_inv_eq_one
    field_simp at h ⊢
    linarith
  have key := lemma_1_5_1 (mul_nonneg hεp.le ha) (mul_nonneg hεm.le hb) hpq
  have hmul : ε ^ (1 / p) * a * (ε ^ (-(1 / p)) * b) = a * b := by
    rw [show ε ^ (1 / p) * a * (ε ^ (-(1 / p)) * b)
        = ε ^ (1 / p) * ε ^ (-(1 / p)) * (a * b) by ring, ← Real.rpow_add hε]
    simp
  have hfst : (ε ^ (1 / p) * a) ^ p = ε * a ^ p := by
    rw [Real.mul_rpow hεp.le ha, ← Real.rpow_mul hε.le, one_div, inv_mul_cancel₀ hp.ne',
      Real.rpow_one]
  have hsnd : (ε ^ (-(1 / p)) * b) ^ q = ε ^ (1 - q) * b ^ q := by
    rw [Real.mul_rpow hεm.le hb, ← Real.rpow_mul hε.le]
    congr 2
    rw [neg_mul, ← mul_comm q (1 / p), hqp]
    ring
  rw [hmul, hfst, hsnd] at key
  exact key

section Lp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ### Hölder's and Minkowski's inequalities -/

/-- **Lemma 1.5.3**, Hölder's inequality: for conjugate exponents `p, q ∈ [1, ∞]`, the product of
a function in `Lᵖ` and a function in `L^q` is in `L¹`, with `‖u v‖_{L¹} ≤ ‖u‖_{Lᵖ} ‖v‖_{L^q}`. -/
theorem lemma_1_5_3 {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q] {u v : α → ℝ} (hu : MemLp u p μ)
    (hv : MemLp v q μ) :
    MemLp (u * v) 1 μ ∧ eLpNorm (u * v) 1 μ ≤ eLpNorm u p μ * eLpNorm v q μ :=
  ⟨hv.mul hu, by simpa using eLpNorm_smul_le_mul_eLpNorm hv.1 hu.1⟩

/-- **Lemma 1.5.4**, Minkowski's inequality: `‖u + v‖_{Lᵖ} ≤ ‖u‖_{Lᵖ} + ‖v‖_{Lᵖ}` for
`p ∈ [1, ∞]`. It is the triangle inequality for the `Lᵖ` norm. -/
theorem lemma_1_5_4 {p : ℝ≥0∞} (hp : 1 ≤ p) {u v : α → ℝ} (hu : AEStronglyMeasurable u μ)
    (hv : AEStronglyMeasurable v μ) : eLpNorm (u + v) p μ ≤ eLpNorm u p μ + eLpNorm v p μ :=
  eLpNorm_add_le hu hv hp

/-! ### Theorem 1.5.5 -/

/-- **Theorem 1.5.5 (a).** `Lᵖ(Ω)` is a Banach space: it is complete for the `Lᵖ` norm. -/
theorem theorem_1_5_5_a {p : ℝ≥0∞} [Fact (1 ≤ p)] : CompleteSpace (Lp ℝ p μ) :=
  inferInstance

/-- **Theorem 1.5.5 (b).** A Cauchy sequence in `Lᵖ(Ω)` has a subsequence converging pointwise
almost everywhere. -/
theorem theorem_1_5_5_b {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : ℕ → Lp ℝ p μ} (hf : CauchySeq f) :
    ∃ (g : α → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => f (φ n) x) atTop (𝓝 (g x)) := by
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hf
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hmeas : TendstoInMeasure μ (fun n => ⇑(f n)) atTop ⇑F :=
    tendstoInMeasure_of_tendsto_eLpNorm hp0 (fun n => (Lp.memLp (f n)).1) (Lp.memLp F).1
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' f F).mp hF)
  obtain ⟨φ, hφ, hae⟩ := hmeas.exists_seq_tendsto_ae
  exact ⟨⇑F, φ, hφ, hae⟩

/-- **Theorem 1.5.5 (c).** On a set of finite measure the `Lᵖ` spaces are nested: for
`1 ≤ p ≤ q ≤ ∞`, every `v ∈ L^q(Ω)` lies in `Lᵖ(Ω)` and
`‖v‖_{Lᵖ} ≤ meas(Ω)^{1/p - 1/q} ‖v‖_{L^q}`. -/
theorem theorem_1_5_5_c [IsFiniteMeasure μ] {p q : ℝ≥0∞} (hpq : p ≤ q) {v : α → ℝ}
    (hv : MemLp v q μ) :
    MemLp v p μ ∧ eLpNorm v p μ ≤ μ Set.univ ^ (1 / p.toReal - 1 / q.toReal) * eLpNorm v q μ :=
  ⟨hv.mono_exponent hpq, by
    rw [mul_comm]; exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hv.1⟩

end Lp

/-! ### Theorem 1.5.6 -/

/-- **Theorem 1.5.6.** `C₀^∞(ℝ^d)` is dense in `Lᵖ(ℝ^d)` for `1 ≤ p < ∞`: every `Lᵖ` class has a
smooth compactly supported function arbitrarily close to it. -/
theorem theorem_1_5_6 {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    Dense {f : Lp ℝ p (volume : Measure (EuclideanSpace ℝ (Fin d))) |
      ∃ g : EuclideanSpace ℝ (Fin d) → ℝ,
        f =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} :=
  MeasureTheory.Lp.dense_hasCompactSupport_contDiff hp

end AtkinsonHan.Chapter01
