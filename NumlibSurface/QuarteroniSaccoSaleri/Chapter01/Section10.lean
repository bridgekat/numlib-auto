import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.MeanInequalities
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Analysis.Normed.Lp.PiLp
import Numlib.Analysis.Normed.Module.NormEquivalence

/-!
# Quarteroni–Sacco–Saleri §1.10: scalar product and norms in vector spaces

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §1.10. Definition 1.16 (scalar product) is Mathlib's
`InnerProductSpace 𝕜 V` and Definition 1.17 (norm, seminorm, normed space, unit vector) is
`NormedAddCommGroup`/`NormedSpace`, `Seminorm` and `‖v‖ = 1`; the two carry alignment
statements only (`definition_1_16`, `definition_1_17`). The rest of the section is stated over
`ℝⁿ = Fin n → ℝ` and `ℂⁿ`, with the `p`-norms read on `PiLp p (fun _ ↦ ℝ)` through
`WithLp.toLp`, from Mathlib and the backbone modules `Numlib/Analysis/Normed/Lp/PiLp` (the
comparison of the `p`-norms) and `Numlib/Analysis/Normed/Module/NormEquivalence` (equivalence of
norms in finite dimension).

## Convention

The book's scalar product `(x, y)` is linear in its *first* argument (Definition 1.16), so it is
Mathlib's `inner 𝕜 y x`, which is conjugate-linear in its first argument; every statement below
writes the book's `(x, y)` as `inner 𝕜 y x`. On `ℂⁿ` this is `(x, y) = yᴴ x = ∑ xᵢ conj yᵢ`
(`inner_eq_star_dotProduct`). A "vector norm" is a definite `Seminorm 𝕜 V`
(`p : Seminorm 𝕜 V` with `∀ v, p v = 0 → v = 0`), the representation every statement about "an
arbitrary norm" in §1.10–1.11 uses.

## Contents

* `definition_1_16`, `inner_eq_star_dotProduct`, `equation_1_12`, `property_1_8` — the scalar
  product, the Euclidean one, the adjoint identity `(A x, y) = (x, Aᴴ y)`, unitary invariance.
* `definition_1_17`, `equation_1_13`, `tendsto_norm_lp_atTop` — norms, the `p`-norms, the
  `∞`-norm as the limit `p → ∞`.
* `property_1_9`, `holder_inequality` — Cauchy–Schwarz with its equality case, Hölder.
* `property_1_10`, `property_1_11` — continuity of a norm, the norm `‖A x‖`.
* `definition_1_18`, `table_1_1` — equivalence of norms, the constants `1`, `√n`, `n`.
* `equation_1_15`, `property_1_12` — componentwise convergence, convergence in norm;
  `Seminorm.tendsto_apply_iff_tendsto_norm` is the lemma behind the "topological equivalence" of
  norms.

## Readings

Property 1.9's equality case is read as linear dependence, `x = 0 ∨ ∃ α, y = α x` (the book's
"iff `y = α x`" fails for `x = 0`, `y ≠ 0`). Property 1.10 as printed, with the same norm on
both sides, is the reverse triangle inequality with `C = 1`; Exercise 14's proof shows that the
intended statement bounds `|‖x‖ - ‖x̂‖|` by a multiple of the *component* norm, and that is what
`property_1_10` states, with the continuity of the norm as a consequence.
-/

open Filter Finset Matrix Topology WithLp
open scoped ENNReal

namespace QuarteroniSaccoSaleri.Chapter01

/-! ### Definition 1.16: the scalar product -/

section Inner

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Definition 1.16.** A *scalar product* on `V` is a map `(·, ·) : V × V → K` that is
(1) linear in its first argument, (2) Hermitian, `(y, x) = conj (x, y)`, and (3) positive
definite, `(x, x) > 0` for `x ≠ 0`. Mathlib's `inner 𝕜` is conjugate-linear in its first
argument and linear in its second, so the book's `(x, y)` is `inner 𝕜 y x`; the three axioms
read as follows for it. -/
theorem definition_1_16 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    (x y z : V) (γ δ : 𝕜) :
    inner 𝕜 y (γ • x + δ • z) = γ * inner 𝕜 y x + δ * inner 𝕜 y z ∧
      inner 𝕜 x y = star (inner 𝕜 y x) ∧
      (x ≠ 0 → 0 < RCLike.re (inner 𝕜 x x) ∧ RCLike.im (inner 𝕜 x x) = 0) ∧
      (inner 𝕜 x x = 0 ↔ x = 0) := by
  refine ⟨by rw [inner_add_right, inner_smul_right, inner_smul_right], ?_,
    fun hx => ⟨re_inner_self_pos.2 hx, inner_self_im x⟩, inner_self_eq_zero⟩
  rw [← inner_conj_symm x y, starRingEnd_apply]

/-- **The Euclidean scalar product**, `(x, y) = yᴴ x = ∑ᵢ xᵢ conj yᵢ` on `ℂⁿ` (or `ℝⁿ`): with
the book's argument order it is `inner 𝕜 y x` on `EuclideanSpace 𝕜 (Fin n)`
(`EuclideanSpace.inner_eq_star_dotProduct`). This fixes the argument order used throughout the
surface. -/
theorem inner_eq_star_dotProduct {n : ℕ} (x y : EuclideanSpace 𝕜 (Fin n)) :
    inner 𝕜 y x = ofLp x ⬝ᵥ star (ofLp y) ∧ inner 𝕜 y x = ∑ i, x i * star (y i) :=
  ⟨EuclideanSpace.inner_eq_star_dotProduct y x, rfl⟩

/-- **(1.12).** For a square matrix `A` and `x, y ∈ ℂⁿ`, `(A x, y) = (x, Aᴴ y)` (backbone
`Matrix.toEuclideanLin_conjTranspose`: `Aᴴ` acts as the adjoint); in particular
`(Q x, Q y) = (x, Qᴴ Q y)` for every `Q`. -/
theorem equation_1_12 {n : ℕ} (A Q : Matrix (Fin n) (Fin n) 𝕜) (x y : EuclideanSpace 𝕜 (Fin n)) :
    inner 𝕜 y (toEuclideanLin A x) = inner 𝕜 (toEuclideanLin Aᴴ y) x ∧
      inner 𝕜 (toEuclideanLin Q y) (toEuclideanLin Q x) =
        inner 𝕜 (toEuclideanLin (Qᴴ * Q) y) x := by
  refine ⟨(toEuclideanLin_conjTranspose_inner_left A x y).symm, ?_⟩
  rw [toEuclideanLin_mul_apply, toEuclideanLin_conjTranspose_inner_left]

/-- **Property 1.8.** Unitary matrices preserve the Euclidean scalar product:
`(Q x, Q y) = (x, y)` for every unitary `Q` and all `x`, `y` (backbone
`Matrix.inner_toLp_mulVec_of_mem_unitaryGroup`). -/
theorem property_1_8 {n : ℕ} {Q : Matrix (Fin n) (Fin n) 𝕜} (hQ : Q ∈ unitaryGroup (Fin n) 𝕜)
    (x y : EuclideanSpace 𝕜 (Fin n)) :
    inner 𝕜 (toEuclideanLin Q y) (toEuclideanLin Q x) = inner 𝕜 y x :=
  inner_toLp_mulVec_of_mem_unitaryGroup hQ _ _

end Inner

/-! ### Definition 1.17: norms and the `p`-norms -/

section Norms

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Definition 1.17.** A *norm* on `V` is a map `‖·‖ : V → ℝ` with (1) `‖v‖ ≥ 0` and
`‖v‖ = 0 ↔ v = 0`, (2) `‖α v‖ = |α| ‖v‖`, (3) `‖v + w‖ ≤ ‖v‖ + ‖w‖`; a map with only 1(i), 2
and 3 is a *seminorm*. A seminorm is Mathlib's `Seminorm 𝕜 V` and a norm a *definite* one,
`p` with `∀ v, p v = 0 → v = 0`: the three axioms hold for it. Conversely the norm of a normed
space `E` is the definite seminorm `normSeminorm 𝕜 E`. -/
theorem definition_1_17 {V : Type*} [AddCommGroup V] [Module 𝕜 V] (p : Seminorm 𝕜 V)
    (hp : ∀ v, p v = 0 → v = 0) (α : 𝕜) (v w : V)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (e : E) :
    (0 ≤ p v ∧ (p v = 0 ↔ v = 0)) ∧ p (α • v) = ‖α‖ * p v ∧ p (v + w) ≤ p v + p w ∧
      normSeminorm 𝕜 E e = ‖e‖ ∧ (∀ e : E, normSeminorm 𝕜 E e = 0 → e = 0) :=
  ⟨⟨apply_nonneg p v, ⟨hp v, fun h => by rw [h, map_zero]⟩⟩, map_smul_eq_mul p α v,
    map_add_le_add p v w, rfl, fun e he => norm_eq_zero.1 he⟩

/-- **(1.13), the `p`-norms on `ℝⁿ`.** For `1 ≤ p < ∞`, `‖x‖_p = (∑ᵢ |xᵢ|^p)^{1/p}`; the
`∞`-norm (maximum norm) is `‖x‖_∞ = maxᵢ |xᵢ|`; and for `p = 2` the Euclidean norm
`‖x‖₂ = (x, x)^{1/2} = (∑ᵢ |xᵢ|²)^{1/2}`. The vector `x` is read on `PiLp p (fun _ ↦ ℝ)` through
`WithLp.toLp p`. -/
theorem equation_1_13 {n : ℕ} (p : ℝ≥0∞) (hp₁ : 1 ≤ p) (hp₂ : p ≠ ⊤) (x : Fin n → ℝ) :
    ‖toLp p x‖ = (∑ i, |x i| ^ p.toReal) ^ (1 / p.toReal) ∧
      ‖toLp ⊤ x‖ = ⨆ i, |x i| ∧
      ‖toLp 2 x‖ = √(inner ℝ (toLp 2 x) (toLp 2 x)) ∧ ‖toLp 2 x‖ = √(∑ i, |x i| ^ 2) := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hp₁).ne' hp₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [PiLp.norm_eq_sum hp]
    simp only [Real.norm_eq_abs]
  · rw [PiLp.norm_eq_ciSup]
    simp only [Real.norm_eq_abs]
  · rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  · rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs]

/-- **The limit `p → ∞` of the `p`-norms.** "The limit as `p` goes to infinity of `‖x‖_p`
exists, is finite, and equals the maximum module of the components of `x`": the `∞`-norm is
`lim_{p → ∞} ‖x‖_p` (backbone `PiLp.tendsto_norm_toLp_atTop`). -/
theorem tendsto_norm_lp_atTop {n : ℕ} (x : Fin n → ℝ) :
    Tendsto (fun p : ℝ => ‖toLp (ENNReal.ofReal p) x‖) atTop (𝓝 (⨆ i, |x i|)) := by
  have h := PiLp.tendsto_norm_toLp_atTop x
  rwa [PiLp.norm_eq_ciSup] at h

/-- **Property 1.9 (Cauchy–Schwarz inequality), (1.14).** For `x, y ∈ ℝⁿ`,
`|(x, y)| = |xᵀ y| ≤ ‖x‖₂ ‖y‖₂`, with equality iff `x` and `y` are linearly dependent, that is
`x = 0` or `y = α x` for some `α ∈ ℝ`. Book erratum: the text says equality holds "iff
`y = α x` for some `α`", which fails for `x = 0`, `y ≠ 0`. -/
theorem property_1_9 {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ y x = ∑ i, x i * y i ∧ |inner ℝ y x| ≤ ‖x‖ * ‖y‖ ∧
      (|inner ℝ y x| = ‖x‖ * ‖y‖ ↔ x = 0 ∨ ∃ α : ℝ, y = α • x) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct]
  · rw [real_inner_comm]
    exact abs_real_inner_le_norm x y
  · rw [real_inner_comm, ← Real.norm_eq_abs]
    exact (norm_inner_eq_norm_tfae ℝ x y).out 1 3

/-- **Hölder's inequality.** For `x, y ∈ ℝⁿ` and conjugate exponents `1/p + 1/q = 1`,
`|(x, y)| ≤ ‖x‖_p ‖y‖_q` (Mathlib's `Real.inner_le_Lp_mul_Lq`); and at the endpoint `p = 1`,
`q = ∞`, `|(x, y)| ≤ ‖x‖₁ ‖y‖_∞`. -/
theorem holder_inequality {n : ℕ} (x y : Fin n → ℝ) {p q : ℝ} (hpq : p.HolderConjugate q) :
    |∑ i, x i * y i| ≤ ‖toLp (ENNReal.ofReal p) x‖ * ‖toLp (ENNReal.ofReal q) y‖ ∧
      |∑ i, x i * y i| ≤ ‖toLp 1 x‖ * ‖toLp ⊤ y‖ := by
  have habs : |∑ i, x i * y i| ≤ ∑ i, |x i| * |y i| :=
    (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => abs_mul _ _))
  constructor
  · have h := Real.inner_le_Lp_mul_Lq univ (fun i => |x i|) (fun i => |y i|) hpq
    simp only [abs_abs] at h
    rw [PiLp.norm_eq_sum (by rw [ENNReal.toReal_ofReal hpq.nonneg]; exact hpq.pos),
      PiLp.norm_eq_sum (by rw [ENNReal.toReal_ofReal hpq.symm.nonneg]; exact hpq.symm.pos),
      ENNReal.toReal_ofReal hpq.nonneg, ENNReal.toReal_ofReal hpq.symm.nonneg]
    simp only [Real.norm_eq_abs]
    exact habs.trans h
  · refine habs.trans ?_
    rw [PiLp.norm_eq_sum (by norm_num), ENNReal.toReal_one]
    simp only [div_one, Real.rpow_one, Real.norm_eq_abs]
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (toLp ⊤ y) i

end Norms

/-! ### Properties 1.10 and 1.11 -/

section Continuity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Property 1.10.** Any vector norm `‖·‖` on a finite-dimensional space `V` is a continuous
function of its argument: there is `C > 0` with `|‖x‖ - ‖x̂‖| ≤ C ‖x - x̂‖_∞` for all `x, x̂`,
the right-hand side taken in the component norm of `V` (so `‖x - x̂‖_∞ ≤ ε` gives
`|‖x‖ - ‖x̂‖| ≤ C ε`), and `‖·‖` is continuous. Backbone `Seminorm.exists_le_mul_norm` and
`Seminorm.continuous_of_finiteDimensional`. Book reading: as printed, with the *same* norm on
both sides, the statement is the reverse triangle inequality with `C = 1`
(`abs_sub_map_le_sub`); Exercise 14's proof shows that the intended content is the bound against
the component norm. -/
theorem property_1_10 (p : Seminorm ℝ V) :
    (∃ C : ℝ, 0 < C ∧ ∀ x y : V, |p x - p y| ≤ C * ‖x - y‖) ∧ Continuous p := by
  obtain ⟨C, hC, h⟩ := p.exists_le_mul_norm
  exact ⟨⟨C, hC, fun x y => (abs_sub_map_le_sub p x y).trans (h (x - y))⟩,
    p.continuous_of_finiteDimensional⟩

/-- **Property 1.11.** Let `‖·‖` be a norm of `ℝᵐ` and `A ∈ ℝ^{m×n}` a matrix with `n` linearly
independent columns. Then `‖x‖_{A} := ‖A x‖` is a norm of `ℝⁿ`: it is the seminorm
`p.comp A.mulVecLin`, and it is definite. Rectangular, as in Exercise 15; the book's statement
is the square case `m = n`. -/
theorem property_1_11 {m n : ℕ} (p : Seminorm ℝ (Fin m → ℝ)) (hp : ∀ v, p v = 0 → v = 0)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : LinearIndependent ℝ A.col) :
    (∀ x, p.comp A.mulVecLin x = p (A *ᵥ x)) ∧
      ∀ x, p.comp A.mulVecLin x = 0 → x = 0 := by
  refine ⟨fun x => rfl, fun x hx => ?_⟩
  have h : A *ᵥ x = 0 := hp _ hx
  exact mulVec_injective_iff.2 hA (by rw [h, mulVec_zero])

/-! ### Definition 1.18 and Table 1.1 -/

/-- **Definition 1.18 and the equivalence of all norms in finite dimension.** Two norms `‖·‖_p`,
`‖·‖_q` on `V` are *equivalent* when there are constants `c_pq, C_pq > 0` with
`c_pq ‖x‖_q ≤ ‖x‖_p ≤ C_pq ‖x‖_q` for all `x`. In a finite-dimensional normed space all norms
are equivalent: every norm `p` is equivalent to the norm of `V` (backbone
`Seminorm.exists_bounds`), and hence any two norms `p`, `q` are equivalent to each other. -/
theorem definition_1_18 (p q : Seminorm ℝ V) (hp : ∀ x, p x = 0 → x = 0)
    (hq : ∀ x, q x = 0 → x = 0) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, c * ‖x‖ ≤ p x ∧ p x ≤ C * ‖x‖) ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, c * q x ≤ p x ∧ p x ≤ C * q x := by
  refine ⟨p.exists_bounds hp, ?_⟩
  obtain ⟨c₁, C₁, hc₁, hC₁, h₁⟩ := p.exists_bounds hp
  obtain ⟨c₂, C₂, hc₂, hC₂, h₂⟩ := q.exists_bounds hq
  refine ⟨c₁ / C₂, C₁ / c₂, by positivity, by positivity, fun x => ⟨?_, ?_⟩⟩
  · calc c₁ / C₂ * q x ≤ c₁ / C₂ * (C₂ * ‖x‖) := by gcongr; exact (h₂ x).2
      _ = c₁ * ‖x‖ := by field_simp
      _ ≤ p x := (h₁ x).1
  · calc p x ≤ C₁ * ‖x‖ := (h₁ x).2
      _ = C₁ / c₂ * (c₂ * ‖x‖) := by field_simp
      _ ≤ C₁ / c₂ * q x := by gcongr; exact (h₂ x).1

/-- **Table 1.1.** The equivalence constants `c_pq`, `C_pq` of the norms `‖·‖₁`, `‖·‖₂`,
`‖·‖_∞` on `ℝⁿ`: `‖x‖₂ ≤ ‖x‖₁ ≤ √n ‖x‖₂`, `‖x‖_∞ ≤ ‖x‖₂ ≤ √n ‖x‖_∞` and
`‖x‖_∞ ≤ ‖x‖₁ ≤ n ‖x‖_∞` — the constants `1`, `n^{1/2}`, `n` of the table, the `n^{-1/2}` and
`n^{-1}` entries being the same inequalities read the other way. Backbone
`PiLp.norm_le_norm_of_le` and `PiLp.norm_le_card_rpow_mul_norm`. -/
theorem table_1_1 {n : ℕ} (x : Fin n → ℝ) :
    (‖toLp 2 x‖ ≤ ‖toLp 1 x‖ ∧ ‖toLp 1 x‖ ≤ √n * ‖toLp 2 x‖) ∧
      (‖toLp ⊤ x‖ ≤ ‖toLp 2 x‖ ∧ ‖toLp 2 x‖ ≤ √n * ‖toLp ⊤ x‖) ∧
      (‖toLp ⊤ x‖ ≤ ‖toLp 1 x‖ ∧ ‖toLp 1 x‖ ≤ n * ‖toLp ⊤ x‖) := by
  refine ⟨⟨PiLp.norm_toLp_two_le_norm_toLp_one x, ?_⟩,
    ⟨PiLp.norm_toLp_top_le_norm_toLp_two x, ?_⟩,
    ⟨PiLp.norm_toLp_top_le_norm_toLp_one x, ?_⟩⟩
  · simpa using PiLp.norm_toLp_one_le_sqrt_card_mul_norm_toLp_two x
  · simpa using PiLp.norm_toLp_two_le_sqrt_card_mul_norm_toLp_top x
  · simpa using PiLp.norm_toLp_one_le_card_mul_norm_toLp_top x

/-! ### Convergence of vectors: (1.15) and Property 1.12 -/

/-- **(1.15).** A sequence `x^(k)` in a space `V` of finite dimension `n` converges to `x` when
its components with respect to a basis `b` converge, `lim_k x_i^(k) = x_i` for `i = 1, …, n`;
this is convergence in the topology of `V` (the coordinate map `b.repr` is a homeomorphism in
finite dimension). For `V = ℝⁿ` the components are the entries, so the condition is
`tendsto_pi_nhds`, and the limit, if it exists, is unique (`tendsto_nhds_unique`). -/
theorem equation_1_15 {n : ℕ} (b : Module.Basis (Fin n) ℝ V) (x : ℕ → V) (y : V)
    (u : ℕ → (Fin n → ℝ)) (v w : Fin n → ℝ) :
    (Tendsto x atTop (𝓝 y) ↔
        ∀ i, Tendsto (fun k => b.repr (x k) i) atTop (𝓝 (b.repr y i))) ∧
      (Tendsto u atTop (𝓝 v) ↔ ∀ i, Tendsto (fun k => u k i) atTop (𝓝 (v i))) ∧
      (Tendsto u atTop (𝓝 v) → Tendsto u atTop (𝓝 w) → v = w) := by
  refine ⟨?_, tendsto_pi_nhds, fun hv hw => tendsto_nhds_unique hv hw⟩
  rw [b.equivFun.toContinuousLinearEquiv.toHomeomorph.isInducing.tendsto_nhds_iff,
    tendsto_pi_nhds]
  simp only [Function.comp_def, ContinuousLinearEquiv.coe_toHomeomorph,
    LinearEquiv.coe_toContinuousLinearEquiv', Module.Basis.equivFun_apply]

/-- **Property 1.12**, and the topological equivalence of norms preceding it. For a norm `‖·‖`
on a finite-dimensional space `V`, `lim_k x^(k) = x ⟺ lim_k ‖x - x^(k)‖ = 0`; and for any two
norms `‖|·|‖`, `‖·‖` on `V`, `‖|x^(k)|‖ → 0 ⟺ ‖x^(k)‖ → 0`. -/
theorem property_1_12 (p q : Seminorm ℝ V) (hp : ∀ x, p x = 0 → x = 0)
    (hq : ∀ x, q x = 0 → x = 0) (x : ℕ → V) (y : V) :
    (Tendsto x atTop (𝓝 y) ↔ Tendsto (fun k => p (y - x k)) atTop (𝓝 0)) ∧
      (Tendsto (fun k => p (x k)) atTop (𝓝 0) ↔ Tendsto (fun k => q (x k)) atTop (𝓝 0)) := by
  refine ⟨?_, (Seminorm.tendsto_apply_iff_tendsto_norm p hp x).trans
    (Seminorm.tendsto_apply_iff_tendsto_norm q hq x).symm⟩
  rw [tendsto_iff_norm_sub_tendsto_zero, Seminorm.tendsto_apply_iff_tendsto_norm p hp]
  simp only [norm_sub_rev]

end Continuity

end QuarteroniSaccoSaleri.Chapter01
