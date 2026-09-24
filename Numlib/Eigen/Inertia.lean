/-
Copyright (c) 2026 Numlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Numlib.Eigen.MinMax
import Numlib.LinearAlgebra.Matrix.LU

/-!
# Sylvester's law of inertia

The inertia of a Hermitian matrix `A : Matrix n n 𝕜` (`[RCLike 𝕜]`) is the triple of the numbers
of negative, zero and positive eigenvalues, counted with multiplicity. The law of inertia says that
a congruence `A ↦ Xᴴ A X` with `X` invertible preserves it ([golub2013matrix] Theorem 8.1.17).

The proof is variational, at the operator level. The number of positive eigenvalues of a symmetric
operator `T` on a finite-dimensional inner product space is the largest dimension of a subspace on
which the quadratic form `re ⟪T x, x⟫` is positive definite
(`LinearMap.IsSymmetric.card_pos_eigenvalues_isGreatest`): the span of the eigenvectors for the
positive eigenvalues attains it, and any competitor meets the span of the others only in `0`. A
subspace on which the form of `S` is positive definite is carried by any injective `ι` with
`re ⟪S y, y⟫ = re ⟪T (ι y), ι y⟫` to one for `T` of the same dimension, so the count can only grow
(`LinearMap.IsSymmetric.card_pos_eigenvalues_le_of_re_inner_eq`); for an invertible congruence it
therefore does not change. The negative count is the positive count of `-T`
(`LinearMap.IsSymmetric.eigenvalues_neg`), and the zero count is what remains.

## Main results

* `LinearMap.IsSymmetric.card_pos_eigenvalues_isGreatest`,
  `LinearMap.IsSymmetric.card_neg_eigenvalues_isGreatest`: the positive and negative counts as
  maximal dimensions of definite subspaces.
* `Matrix.IsHermitian.inertia`, the inertia of a Hermitian matrix, with
  `Matrix.IsHermitian.inertia_eq_eigenvalues₀` (the same counts over the sorted eigenvalues) and
  `Matrix.IsHermitian.inertia_diagonal` (a real diagonal matrix counts the signs of its entries).
* `Matrix.IsHermitian.inertia_conj`: **Sylvester's law of inertia**.
* `Matrix.IsHermitian.card_eigenvalues_lt_eq_card_neg_of_isLDM`: for a real symmetric `A` and an
  `L D Lᵀ` factorization of `A - μ I`, the number of eigenvalues of `A` below `μ` is the number of
  negative pivots ([golub2013matrix] §8.4.2).
* `Matrix.IsHermitian.inertia_pos_eq_sigPos`, `Matrix.IsHermitian.inertia_neg_eq_sigNeg`: at
  `𝕜 = ℝ` the counts are Mathlib's `QuadraticForm.sigPos` and `QuadraticForm.sigNeg` of the
  quadratic form `x ↦ x ⬝ᵥ A x`.

## Implementation notes

Mathlib's `QuadraticForm.sigPos` (`Mathlib/LinearAlgebra/QuadraticForm/Signature`) is the
uniqueness half of Sylvester's law for quadratic forms over a linearly ordered field; it does not
reach complex Hermitian matrices (a sesquilinear form is not a `QuadraticMap`) and says nothing
about eigenvalues. The bridge at `𝕜 = ℝ` lets either theory be used on real symmetric matrices.
-/

open Finset

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {n : ℕ} {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n)
include hT

/-- On the span of the eigenvectors for positive eigenvalues the quadratic form is positive
definite: in the eigenbasis `re ⟪T x, x⟫ = ∑ λ_i |x_i|²`, every term is nonnegative and one is
positive. -/
theorem re_inner_pos_of_mem_eigenvectorSpan_pos {x : E}
    (hx : x ∈ hT.eigenvectorSpan hn {i | 0 < hT.eigenvalues hn i}) (hx0 : x ≠ 0) :
    0 < RCLike.re (inner 𝕜 (T x) x) := by
  set b := hT.eigenvectorBasis hn
  have hrepr : b.repr x ≠ 0 := by
    rwa [Ne, LinearIsometryEquiv.map_eq_zero_iff]
  obtain ⟨j, hj⟩ : ∃ j, b.repr x j ≠ 0 := by
    by_contra! h
    exact hrepr (by ext j; simp [h j])
  have hjs : 0 < hT.eigenvalues hn j := by
    by_contra hneg
    exact hj ((hT.mem_eigenvectorSpan_iff hn).mp hx j (by simpa using hneg))
  rw [hT.re_inner_apply_self_eq_sum hn]
  refine Finset.sum_pos' (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
  · by_cases hi : 0 < hT.eigenvalues hn i
    · positivity
    · rw [(hT.mem_eigenvectorSpan_iff hn).mp hx i (by simpa using hi)]
      simp
  · exact mul_pos hjs (by positivity)

/-- **The positive count is a maximal dimension**: the number of positive eigenvalues of a
symmetric `T` is the largest dimension of a subspace on which `re ⟪T x, x⟫ > 0` for `x ≠ 0`.
Attained by the span of the eigenvectors for the positive eigenvalues
(`LinearMap.IsSymmetric.re_inner_pos_of_mem_eigenvectorSpan_pos`); a competitor meets the span of
the eigenvectors for the nonpositive eigenvalues, on which `re ⟪T x, x⟫ ≤ 0`, only in `0`, so its
dimension is at most `n - (n - #pos)` (`Submodule.exists_mem_inf_ne_zero`). -/
theorem card_pos_eigenvalues_isGreatest :
    IsGreatest {d | ∃ S : Submodule 𝕜 E, Module.finrank 𝕜 S = d ∧
        ∀ x ∈ S, x ≠ 0 → 0 < RCLike.re (inner 𝕜 (T x) x)}
      #{i | 0 < hT.eigenvalues hn i} := by
  refine ⟨⟨hT.eigenvectorSpan hn {i | 0 < hT.eigenvalues hn i},
    hT.finrank_eigenvectorSpan hn _, fun x hx hx0 =>
      hT.re_inner_pos_of_mem_eigenvectorSpan_pos hn hx hx0⟩, ?_⟩
  rintro _ ⟨S, rfl, hS⟩
  set W := hT.eigenvectorSpan hn {i | ¬ 0 < hT.eigenvalues hn i}
  have hW : Module.finrank 𝕜 W = n - #{i | 0 < hT.eigenvalues hn i} := by
    rw [hT.finrank_eigenvectorSpan hn, Finset.filter_not, Finset.card_sdiff_of_subset
      (Finset.filter_subset _ _), Finset.card_univ, Fintype.card_fin]
  have hle : #{i | 0 < hT.eigenvalues hn i} ≤ n :=
    (Finset.card_filter_le _ _).trans (by simp)
  by_contra hlt
  obtain ⟨x, hxSW, hx0⟩ := Submodule.exists_mem_inf_ne_zero (S := S) (W := W) (by omega)
  have hpos := hS x (Submodule.mem_inf.mp hxSW).1 hx0
  have hnonpos := hT.re_inner_apply_self_le_of_mem_eigenvectorSpan hn (c := 0)
    (fun i hi => by simpa using hi) (Submodule.mem_inf.mp hxSW).2
  rw [zero_mul] at hnonpos
  linarith

/-- The positive eigenvalues of `-T` are the negatives of the negative eigenvalues of `T`: the two
counts agree, through `LinearMap.IsSymmetric.eigenvalues_neg` and the reversal of `Fin n`. -/
theorem card_pos_eigenvalues_neg :
    #{i | 0 < hT.neg.eigenvalues hn i} = #{i | hT.eigenvalues hn i < 0} := by
  simp_rw [hT.eigenvalues_neg hn, neg_pos]
  rw [← Finset.map_univ_equiv Fin.revPerm, Finset.filter_map, Finset.card_map]
  congr 1
  ext i
  simp

/-- **The negative count is a maximal dimension**: the number of negative eigenvalues of `T` is
the largest dimension of a subspace on which `re ⟪T x, x⟫ < 0` for `x ≠ 0`.
`LinearMap.IsSymmetric.card_pos_eigenvalues_isGreatest` for `-T`. -/
theorem card_neg_eigenvalues_isGreatest :
    IsGreatest {d | ∃ S : Submodule 𝕜 E, Module.finrank 𝕜 S = d ∧
        ∀ x ∈ S, x ≠ 0 → RCLike.re (inner 𝕜 (T x) x) < 0}
      #{i | hT.eigenvalues hn i < 0} := by
  rw [← hT.card_pos_eigenvalues_neg hn]
  convert hT.neg.card_pos_eigenvalues_isGreatest hn using 7
  simp [inner_neg_left]

/-- **Congruence can only increase the positive count**: if an injective linear `ι : F → E`
pulls the quadratic form of `T` back to that of `S`, `re ⟪S y, y⟫ = re ⟪T (ι y), ι y⟫`, then `S`
has at most as many positive eigenvalues as `T`. A positive definite subspace for `S` is mapped by
`ι` to one for `T` of the same dimension. -/
theorem card_pos_eigenvalues_le_of_re_inner_eq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] {m : ℕ} {S : F →ₗ[𝕜] F}
    (hS : S.IsSymmetric) (hm : Module.finrank 𝕜 F = m) {ι : F →ₗ[𝕜] E}
    (hι : Function.Injective ι)
    (h : ∀ y, RCLike.re (inner 𝕜 (S y) y) = RCLike.re (inner 𝕜 (T (ι y)) (ι y))) :
    #{i | 0 < hS.eigenvalues hm i} ≤ #{i | 0 < hT.eigenvalues hn i} := by
  obtain ⟨⟨V, hV, hVpos⟩, -⟩ := hS.card_pos_eigenvalues_isGreatest hm
  refine (hT.card_pos_eigenvalues_isGreatest hn).2 ⟨V.map ι, ?_, ?_⟩
  · rw [← (Submodule.equivMapOfInjective _ hι V).finrank_eq, hV]
  · rintro _ ⟨y, hy, rfl⟩ hy0
    rw [← h]
    exact hVpos y hy fun h0 => hy0 (by simp [h0])

/-- **Congruence can only increase the negative count**, the dual of
`LinearMap.IsSymmetric.card_pos_eigenvalues_le_of_re_inner_eq`, applied to `-S` and `-T`. -/
theorem card_neg_eigenvalues_le_of_re_inner_eq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] {m : ℕ} {S : F →ₗ[𝕜] F}
    (hS : S.IsSymmetric) (hm : Module.finrank 𝕜 F = m) {ι : F →ₗ[𝕜] E}
    (hι : Function.Injective ι)
    (h : ∀ y, RCLike.re (inner 𝕜 (S y) y) = RCLike.re (inner 𝕜 (T (ι y)) (ι y))) :
    #{i | hS.eigenvalues hm i < 0} ≤ #{i | hT.eigenvalues hn i < 0} := by
  rw [← hS.card_pos_eigenvalues_neg hm, ← hT.card_pos_eigenvalues_neg hn]
  exact hT.neg.card_pos_eigenvalues_le_of_re_inner_eq hn hS.neg hm hι fun y => by
    simp [inner_neg_left, h y]

end LinearMap.IsSymmetric

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **inertia** of a Hermitian matrix ([golub2013matrix] §8.1.5): the numbers of negative, zero
and positive eigenvalues, counted with multiplicity. Any indexing of the eigenvalues gives the same
counts (`Matrix.IsHermitian.inertia_eq_eigenvalues₀`). -/
noncomputable def inertia {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℕ × ℕ × ℕ :=
  (#{i | hA.eigenvalues i < 0}, #{i | hA.eigenvalues i = 0}, #{i | 0 < hA.eigenvalues i})

/-- Counting the values of `f ∘ e` for an equivalence `e` is counting the values of `f`. -/
private theorem card_filter_comp_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (p : β → Prop) [DecidablePred p] : #{a | p (e a)} = #{b | p b} := by
  rw [← Finset.map_univ_equiv e, Finset.filter_map, Finset.card_map]
  rfl

/-- The inertia through the sorted eigenvalues `eigenvalues₀`: the `n`-indexed `eigenvalues` are
`eigenvalues₀` composed with an equivalence, which does not change any count. -/
theorem inertia_eq_eigenvalues₀ {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    hA.inertia = (#{k | hA.eigenvalues₀ k < 0}, #{k | hA.eigenvalues₀ k = 0},
      #{k | 0 < hA.eigenvalues₀ k}) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact card_filter_comp_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      (fun x => hA.eigenvalues₀ x < 0)
  · exact card_filter_comp_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      (fun x => hA.eigenvalues₀ x = 0)
  · exact card_filter_comp_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      (fun x => 0 < hA.eigenvalues₀ x)

/-- The three counts of the inertia add up to the order of the matrix. -/
theorem inertia_sum {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    hA.inertia.1 + hA.inertia.2.1 + hA.inertia.2.2 = Fintype.card n := by
  simp only [inertia]
  have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i => hA.eigenvalues i < 0)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun i => ¬ hA.eigenvalues i < 0) (fun i => hA.eigenvalues i = 0)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have e1 : (Finset.univ.filter fun i => ¬ hA.eigenvalues i < 0 ∧ hA.eigenvalues i = 0) =
      Finset.univ.filter fun i => hA.eigenvalues i = 0 :=
    Finset.filter_congr fun i _ => ⟨fun h => h.2, fun h => ⟨by linarith, h⟩⟩
  have e2 : (Finset.univ.filter fun i => ¬ hA.eigenvalues i < 0 ∧ ¬ hA.eigenvalues i = 0) =
      Finset.univ.filter fun i => 0 < hA.eigenvalues i :=
    Finset.filter_congr fun i _ =>
      ⟨fun h => lt_of_le_of_ne (not_lt.mp h.1) (Ne.symm h.2), fun h => ⟨by linarith, h.ne'⟩⟩
  rw [e1, e2] at h2
  rw [Finset.card_univ] at h1
  omega

/-- The inertia depends on the matrix only, not on the proof that it is Hermitian nor on the way it
is written. -/
theorem inertia_congr {A B : Matrix n n 𝕜} (h : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    hA.inertia = hB.inertia := by
  subst h
  rfl

/-- The positive count of the inertia is the positive count of the operator `toEuclideanLin A`. -/
private theorem inertia_pos_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    hA.inertia.2.2 = #{k | 0 < (isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
      finrank_euclideanSpace k} := by
  rw [inertia_eq_eigenvalues₀]
  rfl

/-- The negative count of the inertia is the negative count of the operator `toEuclideanLin A`. -/
private theorem inertia_neg_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    hA.inertia.1 = #{k | (isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
      finrank_euclideanSpace k < 0} := by
  rw [inertia_eq_eigenvalues₀]
  rfl

/-- The quadratic form of `Xᴴ A X` at `y` is that of `A` at `X y`. -/
private theorem inner_toEuclideanLin_conj (A X : Matrix n n 𝕜) (y : EuclideanSpace 𝕜 n) :
    inner 𝕜 (toEuclideanLin (Xᴴ * A * X) y) y =
      inner 𝕜 (toEuclideanLin A (toEuclideanLin X y)) (toEuclideanLin X y) := by
  rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, toEuclideanLin_conjTranspose_inner_left]

/-- Half of Sylvester's law: an injective congruence does not increase the positive and negative
counts. -/
private theorem inertia_conj_le {A : Matrix n n 𝕜} (hA : A.IsHermitian) {X : Matrix n n 𝕜}
    (hX : Function.Injective (toEuclideanLin X)) :
    (isHermitian_conjTranspose_mul_mul X hA).inertia.1 ≤ hA.inertia.1 ∧
      (isHermitian_conjTranspose_mul_mul X hA).inertia.2.2 ≤ hA.inertia.2.2 := by
  rw [inertia_pos_eq, inertia_pos_eq, inertia_neg_eq, inertia_neg_eq]
  have hq := fun y => congrArg RCLike.re (inner_toEuclideanLin_conj A X y)
  exact ⟨(isSymmetric_toEuclideanLin_iff.mpr hA).card_neg_eigenvalues_le_of_re_inner_eq
      finrank_euclideanSpace _ finrank_euclideanSpace hX hq,
    (isSymmetric_toEuclideanLin_iff.mpr hA).card_pos_eigenvalues_le_of_re_inner_eq
      finrank_euclideanSpace _ finrank_euclideanSpace hX hq⟩

/-- **Sylvester's law of inertia** ([golub2013matrix] Theorem 8.1.17): a congruence `A ↦ Xᴴ A X`
with `X` invertible preserves the inertia of a Hermitian matrix. The positive and negative counts
can only decrease under an injective congruence
(`LinearMap.IsSymmetric.card_pos_eigenvalues_le_of_re_inner_eq` and its dual), and `X⁻¹` undoes
`X`; the zero count is the rest (`Matrix.IsHermitian.inertia_sum`). -/
theorem inertia_conj {A : Matrix n n 𝕜} (hA : A.IsHermitian) {X : Matrix n n 𝕜} (hX : IsUnit X) :
    (isHermitian_conjTranspose_mul_mul X hA).inertia = hA.inertia := by
  have hinj : ∀ {Y : Matrix n n 𝕜}, IsUnit Y → Function.Injective (toEuclideanLin Y) :=
    fun hY => Function.LeftInverse.injective (toEuclideanLin_nonsing_inv_mul_apply hY)
  set hB := isHermitian_conjTranspose_mul_mul X hA
  have hdet := (isUnit_iff_isUnit_det X).mp hX
  have hback : (X⁻¹)ᴴ * (Xᴴ * A * X) * X⁻¹ = A := by
    rw [show (X⁻¹)ᴴ * (Xᴴ * A * X) * X⁻¹ = (X * X⁻¹)ᴴ * A * (X * X⁻¹) by
        simp only [conjTranspose_mul, Matrix.mul_assoc],
      mul_nonsing_inv X hdet, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have h1 := inertia_conj_le hA (hinj hX)
  have h2 := inertia_conj_le hB (hinj (isUnit_nonsing_inv_iff.mpr hX))
  rw [inertia_congr hback _ hA] at h2
  have hs1 := hA.inertia_sum
  have hs2 := hB.inertia_sum
  ext <;> omega

/-- The inertia of `-A` is that of `A` with the negative and positive counts exchanged. -/
theorem inertia_neg {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    hA.neg.inertia = (hA.inertia.2.2, hA.inertia.2.1, hA.inertia.1) := by
  have hT := isSymmetric_toEuclideanLin_iff.mpr hA
  have hcongr := fun k => LinearMap.IsSymmetric.eigenvalues_congr
    (isSymmetric_toEuclideanLin_iff.mpr hA.neg) hT.neg (map_neg _ A) finrank_euclideanSpace k
  have hpos : hA.neg.inertia.2.2 = hA.inertia.1 := by
    rw [inertia_pos_eq, inertia_neg_eq]
    simp only [hcongr]
    exact hT.card_pos_eigenvalues_neg finrank_euclideanSpace
  have hneg : hA.neg.inertia.1 = hA.inertia.2.2 := by
    rw [inertia_neg_eq, inertia_pos_eq]
    simp only [hcongr]
    rw [← hT.neg.card_pos_eigenvalues_neg finrank_euclideanSpace]
    simp only [LinearMap.IsSymmetric.eigenvalues_congr hT.neg.neg hT (neg_neg _)]
  have hs1 := hA.inertia_sum
  have hs2 := hA.neg.inertia_sum
  ext <;> simp <;> omega

/-- **The inertia of a real diagonal matrix** counts the signs of its entries: its eigenvalues are
the entries up to order (the roots of the characteristic polynomial `∏ (X - d i)`, Mathlib's
`Matrix.IsHermitian.roots_charpoly_eq_eigenvalues`). -/
theorem inertia_diagonal (d : n → ℝ) (hD : (diagonal fun i => (d i : 𝕜)).IsHermitian) :
    hD.inertia = (#{i | d i < 0}, #{i | d i = 0}, #{i | 0 < d i}) := by
  have h1 := hD.roots_charpoly_eq_eigenvalues
  have h2 : (diagonal fun i => (d i : 𝕜)).charpoly.roots =
      Multiset.map (RCLike.ofReal ∘ d) Finset.univ.val := by
    rw [charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  rw [h1, ← Multiset.map_map, ← Multiset.map_map] at h2
  have hm := Multiset.map_injective RCLike.ofReal_injective h2
  have hc : ∀ (p : ℝ → Prop) [DecidablePred p], #{i | p (hD.eigenvalues i)} = #{i | p (d i)} := by
    intro p _
    have := congrArg (Multiset.countP p) hm
    rwa [Multiset.countP_map, Multiset.countP_map] at this
  simp only [inertia]
  rw [hc (· < 0), hc (· = 0), hc (0 < ·)]

/-- Shifting a Hermitian matrix by a real multiple of the identity shifts every sorted eigenvalue:
`λ_k(A - μ I) = λ_k(A) - μ`, the quadratic forms differing by exactly `μ ‖x‖²`
(`LinearMap.IsSymmetric.eigenvalues_le_add_of_re_inner_le` both ways). -/
theorem eigenvalues₀_sub_smul_one {A : Matrix n n 𝕜} (hA : A.IsHermitian) (μ : ℝ)
    (hAμ : (A - (μ : 𝕜) • (1 : Matrix n n 𝕜)).IsHermitian) (k : Fin (Fintype.card n)) :
    hAμ.eigenvalues₀ k = hA.eigenvalues₀ k - μ := by
  have hq : ∀ x : EuclideanSpace 𝕜 n,
      RCLike.re (inner 𝕜 (toEuclideanLin (A - (μ : 𝕜) • 1) x) x) =
        RCLike.re (inner 𝕜 (toEuclideanLin A x) x) - μ * ‖x‖ ^ 2 := fun x => by
    rw [toEuclideanLin_sub_apply, toEuclideanLin_smul_apply, toEuclideanLin_one_apply,
      inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K, map_sub, RCLike.conj_ofReal,
      ← RCLike.ofReal_pow, RCLike.re_ofReal_mul, RCLike.ofReal_re]
  have hT := isSymmetric_toEuclideanLin_iff.mpr hA
  have hTμ := isSymmetric_toEuclideanLin_iff.mpr hAμ
  have h1 := hTμ.eigenvalues_le_add_of_re_inner_le hT finrank_euclideanSpace (C := -μ)
    (fun x => by rw [hq]; linarith) k
  have h2 := hT.eigenvalues_le_add_of_re_inner_le hTμ finrank_euclideanSpace (C := μ)
    (fun x => by rw [hq]; linarith) k
  change hTμ.eigenvalues _ k = hT.eigenvalues _ k - μ
  linarith

/-- The quadratic form of a real matrix is the quadratic form of its Euclidean operator. -/
private theorem toQuadraticForm'_toLp (A : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    Matrix.toQuadraticForm' A (WithLp.ofLp x) = RCLike.re (inner ℝ (toEuclideanLin A x) x) := by
  rw [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply, toLinearMap₂'_apply',
    RCLike.re_to_real, EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanLin, star_trivial]

/-- **Bridge to Mathlib's signature** at `𝕜 = ℝ`: the positive count of the inertia of a real
symmetric `A` is `QuadraticForm.sigPos` of the quadratic form `x ↦ x ⬝ᵥ A x`. Both are the largest
dimension of a subspace on which the form is positive definite
(`LinearMap.IsSymmetric.card_pos_eigenvalues_isGreatest`, `sigPos_isGreatest`),
transported along `EuclideanSpace ℝ n ≃ₗ (n → ℝ)`. -/
theorem inertia_pos_eq_sigPos {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    hA.inertia.2.2 = sigPos (Matrix.toQuadraticForm' A) := by
  rw [inertia_pos_eq]
  refine ((isSymmetric_toEuclideanLin_iff.mpr hA).card_pos_eigenvalues_isGreatest
    finrank_euclideanSpace).unique ?_
  convert sigPos_isGreatest (Matrix.toQuadraticForm' A) using 1
  let e := WithLp.linearEquiv 2 ℝ (n → ℝ)
  ext d
  constructor
  · rintro ⟨S, rfl, hS⟩
    refine ⟨S.map e.toLinearMap, (LinearEquiv.finrank_map_eq e S).symm ▸ rfl, ?_⟩
    rintro ⟨_, x, hx, rfl⟩ hx0
    rw [QuadraticMap.restrict_apply]
    change 0 < Matrix.toQuadraticForm' A (WithLp.ofLp x)
    rw [toQuadraticForm'_toLp]
    exact hS x hx fun h => hx0 (by simp [h])
  · rintro ⟨V, rfl, hV⟩
    refine ⟨V.map e.symm.toLinearMap, LinearEquiv.finrank_map_eq e.symm V, ?_⟩
    rintro _ ⟨v, hv, rfl⟩ hx0
    have := hV ⟨v, hv⟩ fun h => hx0 (by rw [show v = 0 from congrArg Subtype.val h, map_zero])
    rw [QuadraticMap.restrict_apply] at this
    rw [← toQuadraticForm'_toLp]
    exact this

/-- **Bridge to Mathlib's signature**, negative part: the negative count of the inertia of a real
symmetric `A` is `QuadraticForm.sigNeg` of `x ↦ x ⬝ᵥ A x`. The positive part for `-A`
(`Matrix.IsHermitian.inertia_neg`, `sigPos_neg`). -/
theorem inertia_neg_eq_sigNeg {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    hA.inertia.1 = sigNeg (Matrix.toQuadraticForm' A) := by
  have h := hA.neg.inertia_pos_eq_sigPos
  rw [hA.inertia_neg] at h
  dsimp only at h
  rw [h, ← sigPos_neg]
  congr 1
  ext x
  simp [Matrix.toQuadraticForm', toLinearMap₂'_apply']

end Matrix.IsHermitian

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- **Counting eigenvalues with an `L D Lᵀ` factorization** ([golub2013matrix] §8.4.2, last
paragraph): for a real symmetric `A` and an `L D Lᵀ` factorization of `A - μ I`, the number of
eigenvalues of `A` below `μ` is the number of negative pivots `d i`. `A - μ I = L D Lᵀ` is a
congruence by the invertible `Lᵀ` (`Matrix.IsHermitian.inertia_conj`,
`Matrix.IsHermitian.inertia_diagonal`), and the negative eigenvalues of `A - μ I` are the
`λ_i - μ` with `λ_i < μ` (`Matrix.IsHermitian.eigenvalues₀_sub_smul_one`). -/
theorem card_eigenvalues_lt_eq_card_neg_of_isLDM {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {μ : ℝ} {L : Matrix n n ℝ} {d : n → ℝ}
    (h : IsLDM (A - μ • 1) L (diagonal d) L) :
    #{i | hA.eigenvalues i < μ} = #{i | d i < 0} := by
  have hD : (diagonal fun i => ((d i : ℝ) : ℝ)).IsHermitian := isHermitian_diagonal d
  have hL : IsUnit Lᵀ := (isUnit_iff_isUnit_det _).mpr (by
    rw [det_transpose]
    exact (isUnit_iff_isUnit_det _).mp h.isUnitLowerTriangular_left.isUnit)
  have heq : Lᵀᴴ * diagonal d * Lᵀ = A - (μ : ℝ) • 1 := by
    rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose, h.mul_eq]
  have hAμ : (A - (μ : ℝ) • (1 : Matrix n n ℝ)).IsHermitian :=
    heq ▸ isHermitian_conjTranspose_mul_mul _ hD
  have hin := hD.inertia_conj hL
  rw [inertia_congr heq _ hAμ, inertia_diagonal] at hin
  have hneg := congrArg Prod.fst hin
  rw [inertia_eq_eigenvalues₀] at hneg
  simp only [eigenvalues₀_sub_smul_one hA μ hAμ, sub_neg] at hneg
  rw [← hneg]
  exact card_filter_comp_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun x => hA.eigenvalues₀ x < μ)

end Matrix.IsHermitian
