import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Analysis.Normed.Lp.PiLp
import Numlib.Analysis.Normed.Module.NormEquivalence

/-!
# Golub–Van Loan §2.2: vector norms

Surface file for [golub2013matrix] §2.2: the definition of a vector norm (§2.2.1), the `p`-norms
(2.2.1), Hölder's and the Cauchy–Schwarz inequality (2.2.2)–(2.2.3), the equivalence of norms
(2.2.4) with the explicit constants (2.2.5)–(2.2.7), the orthogonal invariance of the 2-norm
(§2.2.2), and convergence (§2.2.4).

## Conventions

The book's abstract vector norm is the predicate `IsVectorNorm f` on a function `f : E → ℝ`: the
book states the axioms on `ℝⁿ = Fin n → ℝ`, and §2.3.1 reuses the same axioms on `ℝ^{m×n}`
(`IsMatrixNorm`), so the predicate is stated once for any real vector space. It is bridged to
Mathlib's vocabulary, a definite `Seminorm ℝ E` (`IsVectorNorm.exists_seminorm`). The `p`-norm
`‖x‖_p` of `x : Fin n → ℝ` is `‖WithLp.toLp p x‖`, the norm of `PiLp p`, for `p : ℝ≥0∞`.

## Sources

Backbone `Numlib/Analysis/Normed/Lp/PiLp` (Hölder, the comparison constants),
`Numlib/Analysis/Normed/Module/NormEquivalence` (equivalence of norms, convergence),
`Numlib/Analysis/Matrix/ToEuclideanLin` (orthogonal invariance). §2.2.3 (absolute and relative
error, "about `p` correct significant digits") names quantities and states a heuristic with `≈`;
it has no declaration.
-/

open Filter Matrix Topology WithLp
open scoped ENNReal

namespace GolubVanLoan.Chapter02

variable {n : ℕ}

/-! ### §2.2.1 Definitions -/

/-- **§2.2.1, vector norm.** A function `f` on a real vector space (the book's `ℝⁿ`) is a *vector
norm* if `f(x) ≥ 0` with `f(x) = 0` iff `x = 0`, `f(x + y) ≤ f(x) + f(y)`, and
`f(αx) = |α| f(x)`. -/
structure IsVectorNorm {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → ℝ) : Prop where
  /-- A norm is nonnegative. -/
  nonneg : ∀ x, 0 ≤ f x
  /-- A norm vanishes exactly at `0`. -/
  eq_zero_iff : ∀ x, f x = 0 ↔ x = 0
  /-- The triangle inequality. -/
  add_le : ∀ x y, f (x + y) ≤ f x + f y
  /-- Absolute homogeneity. -/
  smul : ∀ (α : ℝ) x, f (α • x) = |α| * f x

/-- **§2.2.1, bridge to Mathlib.** A vector norm is exactly a definite seminorm: `IsVectorNorm f`
iff `f` is (the coercion of) a `Seminorm ℝ E` vanishing only at `0`. -/
theorem IsVectorNorm.exists_seminorm {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → ℝ} :
    IsVectorNorm f ↔ ∃ p : Seminorm ℝ E, ⇑p = f ∧ ∀ x, p x = 0 → x = 0 := by
  constructor
  · intro hf
    refine ⟨Seminorm.of f hf.add_le fun a x => by rw [hf.smul, Real.norm_eq_abs], rfl,
      fun x hx => (hf.eq_zero_iff x).1 hx⟩
  · rintro ⟨p, rfl, hp⟩
    exact ⟨apply_nonneg p, fun x => ⟨hp x, fun h => h ▸ map_zero p⟩, map_add_le_add p,
      fun α x => by rw [map_smul_eq_mul, Real.norm_eq_abs]⟩

/-- **§2.2.1**: the norm of a real normed space is a vector norm. -/
theorem isVectorNorm_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    IsVectorNorm fun x : E => ‖x‖ :=
  ⟨fun _ => norm_nonneg _, fun _ => norm_eq_zero, norm_add_le,
    fun α x => by rw [norm_smul, Real.norm_eq_abs]⟩

/-- **§2.2.1**: the `p`-norms, `p ≥ 1`, are vector norms on `ℝⁿ` (the book's "useful class"). -/
theorem isVectorNorm_norm_toLp (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    IsVectorNorm fun x : Fin n → ℝ => ‖WithLp.toLp p x‖ := by
  have h := isVectorNorm_norm (E := PiLp p fun _ : Fin n => ℝ)
  exact ⟨fun x => h.nonneg _, fun x => by rw [h.eq_zero_iff, WithLp.toLp_eq_zero],
    fun x y => by rw [WithLp.toLp_add]; exact h.add_le _ _,
    fun α x => by rw [WithLp.toLp_smul]; exact h.smul _ _⟩

/-- **(2.2.1)**, the `p`-norms `‖x‖_p = (|x₁|^p + ⋯ + |xₙ|^p)^{1/p}` for `1 ≤ p < ∞`, and the
three most important ones: `‖x‖₁ = |x₁| + ⋯ + |xₙ|`, `‖x‖₂ = (xᵀx)^{1/2}`,
`‖x‖_∞ = max_i |xᵢ|`. -/
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

/-- **(2.2.2), Hölder's inequality**: `|xᵀy| ≤ ‖x‖_p ‖y‖_q` for `1/p + 1/q = 1` (the endpoint pair
`p = 1`, `q = ∞` included). -/
theorem equation_2_2_2 {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (x y : Fin n → ℝ) : |x ⬝ᵥ y| ≤ ‖WithLp.toLp p x‖ * ‖WithLp.toLp q y‖ :=
  PiLp.norm_dotProduct_le x y

/-- **(2.2.3), the Cauchy–Schwarz inequality**: `|xᵀy| ≤ ‖x‖₂ ‖y‖₂`, the case `p = q = 2` of
Hölder's inequality. -/
theorem equation_2_2_3 (x y : Fin n → ℝ) :
    |x ⬝ᵥ y| ≤ ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖ :=
  equation_2_2_2 x y

/-- **(2.2.4), all norms on `ℝⁿ` are equivalent**: for vector norms `‖·‖_α`, `‖·‖_β` there are
positive `c₁`, `c₂` with `c₁ ‖x‖_α ≤ ‖x‖_β ≤ c₂ ‖x‖_α`. -/
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

/-- **(2.2.5)**: `‖x‖₂ ≤ ‖x‖₁ ≤ √n ‖x‖₂`. -/
theorem equation_2_2_5 (x : Fin n → ℝ) :
    ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 1 x‖ ∧ ‖WithLp.toLp 1 x‖ ≤ √(n : ℝ) * ‖WithLp.toLp 2 x‖ :=
  ⟨PiLp.norm_toLp_two_le_norm_toLp_one x, by
    simpa using PiLp.norm_toLp_one_le_sqrt_card_mul_norm_toLp_two x⟩

/-- **(2.2.6)**: `‖x‖_∞ ≤ ‖x‖₂ ≤ √n ‖x‖_∞`. -/
theorem equation_2_2_6 (x : Fin n → ℝ) :
    ‖WithLp.toLp ∞ x‖ ≤ ‖WithLp.toLp 2 x‖ ∧ ‖WithLp.toLp 2 x‖ ≤ √(n : ℝ) * ‖WithLp.toLp ∞ x‖ :=
  ⟨PiLp.norm_toLp_top_le_norm_toLp_two x, by
    simpa using PiLp.norm_toLp_two_le_sqrt_card_mul_norm_toLp_top x⟩

/-- **(2.2.7)**: `‖x‖_∞ ≤ ‖x‖₁ ≤ n ‖x‖_∞`. -/
theorem equation_2_2_7 (x : Fin n → ℝ) :
    ‖WithLp.toLp ∞ x‖ ≤ ‖WithLp.toLp 1 x‖ ∧ ‖WithLp.toLp 1 x‖ ≤ n * ‖WithLp.toLp ∞ x‖ :=
  ⟨PiLp.norm_toLp_top_le_norm_toLp_one x, by
    simpa using PiLp.norm_toLp_one_le_card_mul_norm_toLp_top x⟩

/-- **§2.2.2, orthogonal invariance**: the 2-norm is preserved under orthogonal transformation,
`‖Qx‖₂ = ‖x‖₂` for orthogonal `Q` (`‖Qx‖₂² = xᵀQᵀQx = xᵀx`). -/
theorem norm_mulVec_of_mem_orthogonalGroup {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (x : Fin n → ℝ) :
    ‖WithLp.toLp 2 (Q *ᵥ x)‖ = ‖WithLp.toLp 2 x‖ :=
  norm_toLp_mulVec_of_mem_unitaryGroup hQ x

/-! ### §2.2.4 Convergence -/

/-- **§2.2.4, convergence**: `x⁽ᵏ⁾ → x` iff `‖x⁽ᵏ⁾ - x‖ → 0` in any particular vector norm, so
"convergence in any particular norm implies convergence in all norms". Stated for any
finite-dimensional real normed space (the book's `ℝⁿ`, and `ℝ^{m×n}` in §2.3.2). -/
theorem tendsto_iff_of_isVectorNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} (hf : IsVectorNorm f) (x : ℕ → E) (x₀ : E) :
    Tendsto (fun k => f (x k - x₀)) atTop (𝓝 0) ↔ Tendsto x atTop (𝓝 x₀) := by
  obtain ⟨p, rfl, hp⟩ := IsVectorNorm.exists_seminorm.1 hf
  rw [Seminorm.tendsto_apply_iff_tendsto_norm p hp fun k => x k - x₀]
  exact tendsto_iff_norm_sub_tendsto_zero.symm

end GolubVanLoan.Chapter02
