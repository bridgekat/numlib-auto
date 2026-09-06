import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Numlib.IntegralEquations.Basic
import NumlibSurface.AtkinsonHan.Chapter02.Section01

/-!
# Atkinson–Han §2.2: continuous linear operators

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §2.2: the equivalence of continuity and
boundedness for a linear operator, the operator norm, and `𝓛(V, W)` as a Banach space.

The book's `𝓛(V, W)` is Mathlib's `V →L[𝕜] W`, so Theorems 2.2.5 and 2.2.10 are instances rather
than theorems; they are stated anyway, in the shape the book gives them, because they are numbered
results and because the surface's job is to give a reader of the book a Lean name for each. The
substance of the section for the rest of the book is Theorem 2.2.4 and the submultiplicativity
(2.2.6), on which every operator-norm estimate in Chapters 2, 5, 8 and 9 rests.

## Main results

* `proposition_2_2_2` — continuity at the origin gives continuity everywhere, in the book's
  sequential form.
* `proposition_2_2_3` — Definition 2.1.6's boundedness of a *linear* operator is the estimate
  (2.2.2) `‖L v‖ ≤ γ ‖v‖`.
* `theorem_2_2_4` — continuous ⇔ bounded, with `equation_2_2_3` for the Lipschitz estimate.
* `theorem_2_2_5` — (2.2.4) and the equivalent descriptions of the operator norm, including
  Exercise 2.2.4's `‖L‖ = inf {γ | ∀ v, ‖L v‖ ≤ γ ‖v‖}`.
* `theorem_2_2_6` — (2.2.5), (2.2.6) and `‖Lⁿ‖ ≤ ‖L‖ⁿ`.
* `example_2_2_8_linfty`, `example_2_2_8_l1`, `example_2_2_8_l2` — the matrix operator norms for
  the vector `∞`-, `1`- and `2`-norms.
* `theorem_2_2_10` — `𝓛(V, W)` is a Banach space when `W` is.
* `equation_2_2_8` — Example 2.2.9, the norm of an integral operator with continuous kernel on
  `C[a, b]`.

Two clauses of Theorem 2.2.5 are also stated on their own, because later sections use them
directly: `opNorm_eq_sSup_ratio` is (2.2.4), and `isBoundedOperator_iff_exists_bound` is
Proposition 2.2.3 under the descriptive name that matches
`isBoundedOperator_iff_image_bounded` of §2.1.

Example 2.2.8 is three declarations because Mathlib keeps the three matrix norms apart with scoped
instances, and because it has no `ℓ¹` operator norm on matrices at all: `example_2_2_8_l1`
therefore states the *characterization* of the induced norm, which is what Exercise 2.2.4 says an
operator norm is, rather than an equation between two norms.

## Not formalized here

Example 2.2.7, that the identity operator has norm `1`, is Mathlib's
`ContinuousLinearMap.norm_id`. The exercises of the section are either restatements of the
theorems above (2.2.3 is Theorem 2.2.5, 2.2.4 is its fourth clause, 2.2.5 is `equation_2_2_8`) or
one-line consequences of linearity and of `LinearMap.ker_eq_bot` (2.2.1, 2.2.2, 2.2.7, 2.2.8);
Exercise 2.2.6, that multiplication by `m ∈ C(Ω̄)` has norm `‖m‖_∞` on `Lᵖ(Ω)`, is not used later.
-/

open Bornology Filter Metric Topology

namespace AtkinsonHan.Chapter02

section Continuity

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- **Proposition 2.2.2.** A linear operator that is continuous at the origin is continuous
everywhere.  The book argues sequentially: `L uₙ → 0` whenever `uₙ → 0` is enough, because
`uₙ → u` gives `uₙ - u → 0`.  The converse is immediate, so the two are stated as an
equivalence. -/
theorem proposition_2_2_2 (L : V →ₗ[𝕜] W) :
    (∀ u : ℕ → V, Tendsto u atTop (𝓝 0) → Tendsto (fun n => L (u n)) atTop (𝓝 0)) ↔
      Continuous L := by
  constructor
  · intro h
    refine continuous_of_continuousAt_zero L ?_
    rw [ContinuousAt, map_zero]
    exact Filter.tendsto_iff_seq_tendsto.2 h
  · intro h u hu
    have := (h.tendsto (0 : V)).comp hu
    rwa [map_zero] at this

/-- **Proposition 2.2.3**, (2.2.2).  For a *linear* operator, the boundedness of Definition 2.1.6
— bounded sets have bounded images — is the estimate `‖L v‖ ≤ γ ‖v‖` with a single constant.
This is the bridge that lets the rest of the book work with `γ` instead of with images of bounded
sets. -/
theorem proposition_2_2_3 (L : V →ₗ[𝕜] W) :
    IsBoundedOperator L ↔ ∃ γ : ℝ, 0 ≤ γ ∧ ∀ v, ‖L v‖ ≤ γ * ‖v‖ := by
  constructor
  · intro hL
    obtain ⟨R, hR⟩ := hL 1 one_pos
    obtain ⟨C, hC⟩ := L.bound_of_ball_bound one_pos R fun z hz =>
      hR z (mem_ball_zero_iff.mp hz).le
    refine ⟨max C 0, le_max_right _ _, fun v => (hC v).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg v)
  · rintro ⟨γ, hγ, h⟩ r _
    exact ⟨γ * r, fun v hv => (h v).trans (mul_le_mul_of_nonneg_left hv hγ)⟩

/-- The descriptive name of Proposition 2.2.3, matching
`isBoundedOperator_iff_image_bounded` of §2.1: for a linear operator, Definition 2.1.6 is the
existence of a bound `γ` in (2.2.2). -/
theorem isBoundedOperator_iff_exists_bound (L : V →ₗ[𝕜] W) :
    IsBoundedOperator L ↔ ∃ γ : ℝ, 0 ≤ γ ∧ ∀ v, ‖L v‖ ≤ γ * ‖v‖ :=
  proposition_2_2_3 L

/-- **Theorem 2.2.4.** A linear operator between normed spaces is continuous if and only if it is
bounded in the sense of Definition 2.1.6.  With Proposition 2.2.3 this is the statement the book
uses everywhere: continuity may always be replaced by an estimate `‖L v‖ ≤ γ ‖v‖`. -/
theorem theorem_2_2_4 (L : V →ₗ[𝕜] W) : Continuous L ↔ IsBoundedOperator L := by
  rw [proposition_2_2_3]
  constructor
  · intro h
    obtain ⟨C, hC0, hC⟩ := ContinuousLinearMap.bound (⟨L, h⟩ : V →L[𝕜] W)
    exact ⟨C, hC0.le, hC⟩
  · rintro ⟨γ, _, h⟩
    exact AddMonoidHomClass.continuous_of_bound L γ h

/-- **(2.2.3).** A continuous linear operator is Lipschitz, with the operator norm as its
constant: `‖L v₁ − L v₂‖ ≤ ‖L‖ ‖v₁ − v₂‖`.  This is what "continuity is uniform for a linear
operator" means in the book. -/
theorem equation_2_2_3 (L : V →L[𝕜] W) (v₁ v₂ : V) : ‖L v₁ - L v₂‖ ≤ ‖L‖ * ‖v₁ - v₂‖ := by
  rw [← map_sub]
  exact L.le_opNorm _

end Continuity

section OperatorNorm

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- (2.2.4) as the book writes it: `‖L‖` is the supremum of the ratios `‖L v‖/‖v‖` over `v ≠ 0`.
The supremum is a real supremum: the family is bounded above by `‖L‖`, and on a trivial space both
sides are `0` because `sSup ∅ = 0`. -/
theorem opNorm_eq_sSup_ratio (L : V →L[𝕜] W) :
    ‖L‖ = sSup ((fun v => ‖L v‖ / ‖v‖) '' {v : V | v ≠ 0}) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · have hL : L = 0 := by
      ext v
      rw [Subsingleton.elim v 0, map_zero]
      simp
    have hempty : {v : V | v ≠ 0} = ∅ := by
      ext v
      simp [Subsingleton.elim v 0]
    rw [hL, hempty, Set.image_empty, Real.sSup_empty, norm_zero]
  · obtain ⟨w, hw⟩ := exists_ne (0 : V)
    have hbdd : BddAbove ((fun v => ‖L v‖ / ‖v‖) '' {v : V | v ≠ 0}) :=
      ⟨‖L‖, by rintro _ ⟨v, -, rfl⟩; exact L.ratio_le_opNorm v⟩
    have hne : ((fun v => ‖L v‖ / ‖v‖) '' {v : V | v ≠ 0}).Nonempty := ⟨_, ⟨w, hw, rfl⟩⟩
    refine le_antisymm ?_ (csSup_le hne (by rintro _ ⟨v, -, rfl⟩; exact L.ratio_le_opNorm v))
    have hS0 : 0 ≤ sSup ((fun v => ‖L v‖ / ‖v‖) '' {v : V | v ≠ 0}) :=
      le_trans (by positivity) (le_csSup hbdd ⟨w, hw, rfl⟩)
    refine L.opNorm_le_bound hS0 ?_
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · rw [← div_le_iff₀ (norm_pos_iff.mpr hv)]
      exact le_csSup hbdd ⟨v, hv, rfl⟩

/-- **Theorem 2.2.5**, with (2.2.4) and Exercise 2.2.4.  `𝓛(V, W)` is a normed linear space —
that is Mathlib's `V →L[𝕜] W` — and its norm has the four descriptions the book gives: as the
supremum of `‖L v‖/‖v‖` over `v ≠ 0`, as the supremum of `‖L v‖` over the closed unit ball, as the
supremum of `‖L v‖` over the unit sphere, and (Exercise 2.2.4) as the *least* `γ ≥ 0` with
`‖L v‖ ≤ γ ‖v‖` for all `v`. -/
theorem theorem_2_2_5 (L : V →L[𝕜] W) :
    ‖L‖ = sSup ((fun v => ‖L v‖ / ‖v‖) '' {v : V | v ≠ 0}) ∧
      ‖L‖ = sSup ((fun v => ‖L v‖) '' closedBall 0 1) ∧
        ‖L‖ = sSup ((fun v => ‖L v‖) '' sphere 0 1) ∧
          IsLeast {γ : ℝ | 0 ≤ γ ∧ ∀ v, ‖L v‖ ≤ γ * ‖v‖} ‖L‖ :=
  ⟨opNorm_eq_sSup_ratio L, (L.sSup_unitClosedBall_eq_norm).symm, (L.sSup_sphere_eq_norm).symm,
    L.isLeast_opNorm⟩

/-- **Theorem 2.2.6**, with (2.2.5) and (2.2.6).  The operator norm satisfies `‖L v‖ ≤ ‖L‖ ‖v‖`
and is submultiplicative, `‖L₂ ∘ L₁‖ ≤ ‖L₂‖ ‖L₁‖`; iterating the second gives `‖Lⁿ‖ ≤ ‖L‖ⁿ`,
which is what every Neumann-series estimate of §2.3 uses. -/
theorem theorem_2_2_6 {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] (L₁ : V →L[𝕜] W)
    (L₂ : W →L[𝕜] X) (L : V →L[𝕜] V) :
    (∀ v, ‖L₁ v‖ ≤ ‖L₁‖ * ‖v‖) ∧ ‖L₂.comp L₁‖ ≤ ‖L₂‖ * ‖L₁‖ ∧ ∀ n : ℕ, ‖L ^ n‖ ≤ ‖L‖ ^ n :=
  ⟨L₁.le_opNorm, L₂.opNorm_comp_le L₁, fun n => by
    cases n with
    | zero =>
      simpa [ContinuousLinearMap.one_def] using
        ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := V)
    | succ n => exact norm_pow_le' L n.succ_pos⟩

/-- **Theorem 2.2.10.**  If `W` is a Banach space then so is `𝓛(V, W)`.  In Mathlib this is the
instance `ContinuousLinearMap.completeSpace`; the statement is recorded so that the book's number
has a name. -/
theorem theorem_2_2_10 [CompleteSpace W] : CompleteSpace (V →L[𝕜] W) := inferInstance

end OperatorNorm

/-! ### Example 2.2.8: the operator norms of a matrix

Each of the three vector norms of the book gives a different norm on matrices, and Mathlib keeps
them apart with scoped instances; each clause below therefore opens its own scope. -/

section MatrixLinfty

open scoped Matrix.Norms.Operator

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- **Example 2.2.8**, the `∞`-norm: for the vector norm `‖x‖_∞ = max_i |x_i|` the induced matrix
norm is the maximum absolute row sum, `‖A‖_∞ = max_i ∑_j |a_ij|`.  The second clause says that
this really is the operator norm of `x ↦ A x` on sup-normed coordinate space. -/
theorem example_2_2_8_linfty (A : Matrix m n 𝕜) :
    ‖A‖ = ((Finset.univ.sup fun i => ∑ j, ‖A i j‖₊ : NNReal) : ℝ) ∧
      ‖A‖ = ‖ContinuousLinearMap.mk (Matrix.mulVecLin A)‖ :=
  ⟨Matrix.linfty_opNorm_def A, Matrix.linfty_opNorm_eq_opNorm A⟩

end MatrixLinfty

section MatrixL1

open scoped Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- **Example 2.2.8**, the `1`-norm: for the vector norm `‖x‖₁ = ∑_i |x_i|` the induced matrix
norm is the maximum absolute column sum, `‖A‖₁ = max_j ∑_i |a_ij|`.

Mathlib has no `ℓ¹` operator norm on matrices, so the statement is the *characterization* of an
induced norm rather than an equation between two norms: `max_j ∑_i |a_ij|` is the least `γ ≥ 0`
with `‖A x‖₁ ≤ γ ‖x‖₁` for every `x`.  That is Exercise 2.2.4's description of the operator norm,
the fourth clause of `theorem_2_2_5`, so it says exactly what the book's `‖A‖₁ = max_j ∑_i |a_ij|`
says.  The minimum is attained at the coordinate vector `e_j` of a maximizing column. -/
theorem example_2_2_8_l1 (A : Matrix m n 𝕜) :
    IsLeast {γ : ℝ | 0 ≤ γ ∧ ∀ x : n → 𝕜, ∑ i, ‖(A *ᵥ x) i‖ ≤ γ * ∑ j, ‖x j‖}
      ((Finset.univ.sup fun j => ∑ i, ‖A i j‖₊ : NNReal) : ℝ) := by
  classical
  have hcol : ∀ j, ∑ i, ‖A i j‖ ≤ ((Finset.univ.sup fun j => ∑ i, ‖A i j‖₊ : NNReal) : ℝ) := by
    intro j
    have h : (∑ i, ‖A i j‖₊) ≤ (Finset.univ.sup fun j => ∑ i, ‖A i j‖₊) :=
      Finset.le_sup (f := fun j => ∑ i, ‖A i j‖₊) (Finset.mem_univ j)
    simpa using NNReal.coe_le_coe.2 h
  refine ⟨⟨NNReal.coe_nonneg _, fun x => ?_⟩, ?_⟩
  · have hstep : ∀ i, ‖(A *ᵥ x) i‖ ≤ ∑ j, ‖A i j‖ * ‖x j‖ := by
      intro i
      rw [Matrix.mulVec_apply_eq_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      exact le_of_eq (norm_mul _ _)
    calc ∑ i, ‖(A *ᵥ x) i‖ ≤ ∑ i, ∑ j, ‖A i j‖ * ‖x j‖ := Finset.sum_le_sum fun i _ => hstep i
      _ = ∑ j, (∑ i, ‖A i j‖) * ‖x j‖ := by rw [Finset.sum_comm]; simp [Finset.sum_mul]
      _ ≤ ∑ j, ((Finset.univ.sup fun j => ∑ i, ‖A i j‖₊ : NNReal) : ℝ) * ‖x j‖ :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hcol j) (norm_nonneg _)
      _ = ((Finset.univ.sup fun j => ∑ i, ‖A i j‖₊ : NNReal) : ℝ) * ∑ j, ‖x j‖ := by
          rw [Finset.mul_sum]
  · rintro γ ⟨hγ0, hγ⟩
    lift γ to NNReal using hγ0 with γ'
    rw [NNReal.coe_le_coe]
    refine Finset.sup_le fun j _ => ?_
    have hx : ∑ k, ‖(Pi.single j 1 : n → 𝕜) k‖ = 1 := by
      rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
      simp
    have hAx : ∀ i, (A *ᵥ (Pi.single j 1 : n → 𝕜)) i = A i j := by
      intro i
      rw [Matrix.mulVec_apply_eq_sum,
        Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
      simp
    have h := hγ (Pi.single j 1)
    simp only [hAx, hx, mul_one] at h
    rw [← NNReal.coe_le_coe]
    push_cast
    exact h

end MatrixL1

section MatrixL2

open scoped Matrix Matrix.Norms.L2Operator

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Example 2.2.8**, the `2`-norm.  For the Euclidean vector norm on `ℂⁿ` the induced matrix
norm is `‖A‖₂ = √(ρ(Aᴴ A))`, the square root of the spectral radius of `Aᴴ A`.  The second clause
is the `C*`-identity `‖Aᴴ A‖ = ‖A‖²` that produces it — `Aᴴ A` is self-adjoint, so its spectral
radius *is* its norm — and the third says that `‖A‖₂` is the operator norm of `x ↦ A x` between
Euclidean spaces.

Stated over `ℂ`, as the book states Example 2.2.8, because the spectral-radius identity for a
self-adjoint element is available for a `C*`-algebra over `ℂ`. -/
theorem example_2_2_8_l2 (A : Matrix m n ℂ) :
    ‖A‖ = Real.sqrt (spectralRadius ℂ (Aᴴ * A)).toReal ∧
      ‖Aᴴ * A‖ = ‖A‖ ^ 2 ∧
        ‖A‖ = ‖(Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A‖ := by
  have hsa : IsSelfAdjoint (Aᴴ * A) := by
    simp [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul]
  have hmul : ‖Aᴴ * A‖ = ‖A‖ ^ 2 := by
    rw [Matrix.l2_opNorm_conjTranspose_mul_self, sq]
  refine ⟨?_, hmul, Matrix.l2_opNorm_def A⟩
  rw [IsSelfAdjoint.spectralRadius_eq_nnnorm hsa, ENNReal.coe_toReal, coe_nnnorm, hmul,
    Real.sqrt_sq (norm_nonneg A)]

end MatrixL2

section IntegralOperator

/-- **Example 2.2.9**, (2.2.8).  The integral operator with continuous kernel `k` on `C[a, b]` is
bounded, with norm `‖K‖ = max_x ∫_a^b |k(x, y)| dy`.  The same formula is (3.7.9) and (3.7.17) in
Chapter 3.  Both the operator and the formula are the backbone's
(`Numlib/IntegralEquations/Basic`). -/
theorem equation_2_2_8 {a b : ℝ} (hab : a ≤ b) (k : C(Set.Icc a b × Set.Icc a b, ℝ)) :
    ‖IntegralOperator.fredholm hab k‖ = ⨆ x, ∫ y in a..b, |k (x, Set.projIcc a b hab y)| :=
  IntegralOperator.norm_fredholm hab k

end IntegralOperator

end AtkinsonHan.Chapter02
