/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Numlib.Data.Finset.Card
import Numlib.Eigen.MinMax
import Numlib.Eigen.Normal
import Numlib.LinearAlgebra.Matrix.LU

/-!
# Sylvester's law of inertia

Let $A \in \mathbb{K}^{n \times n}$ be Hermitian, with $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$.
The **inertia** of $A$ is the triple of the numbers of negative, zero and positive eigenvalues of
$A$, counted with multiplicity. **Sylvester's law of inertia** says that a congruence
$A \mapsto X^H A X$ with $X$ invertible preserves the inertia (Theorem 8.1.17 of [golub2013matrix]).
This file proves it, and uses it to count the eigenvalues of a real symmetric matrix below a number
$\mu$ from an $L D L^T$ factorization of $A - \mu I$ (§8.4.2 of [golub2013matrix]).

## Main definitions

* `Matrix.IsHermitian.inertia`: the inertia of a Hermitian matrix.

## Main results

* `LinearMap.IsSymmetric.card_pos_eigenvalues_isGreatest` and
  `LinearMap.IsSymmetric.card_neg_eigenvalues_isGreatest`: the numbers of positive and of negative
  eigenvalues of a symmetric operator are the largest dimensions of subspaces on which its quadratic
  form is positive definite or negative definite.
* `Matrix.IsHermitian.inertia_eq_eigenvalues₀`: the inertia counts the sorted eigenvalues in the
  same way.
* `Matrix.IsHermitian.inertia_diagonal`: the inertia of a real diagonal matrix counts the signs of
  its entries.
* `Matrix.IsHermitian.inertia_conj`: **Sylvester's law of inertia**.
* `Matrix.IsHermitian.card_eigenvalues_lt_eq_card_neg_of_isLDM`: for a real symmetric $A$ and a
  factorization $A - \mu I = L D L^T$, the number of eigenvalues of $A$ below $\mu$ is the number of
  negative pivots.
* `Matrix.IsHermitian.inertia_pos_eq_sigPos` and `Matrix.IsHermitian.inertia_neg_eq_sigNeg`: for
  $\mathbb{K} = \mathbb{R}$, the positive and negative counts are Mathlib's `sigPos` and `sigNeg` of
  the quadratic form $x \mapsto x^T A x$.

## Proof outline

The proof is variational, for operators. The number of positive eigenvalues of a symmetric operator
$T$ on a finite-dimensional inner product space is the largest dimension of a subspace on which the
quadratic form $\operatorname{Re} \langle T x, x \rangle$ is positive definite. The span of the
eigenvectors for the positive eigenvalues attains it, and any other such subspace meets the span of
the other eigenvectors only in $0$. An injective linear map $\iota$ with $\operatorname{Re} \langle
S y, y \rangle = \operatorname{Re} \langle T (\iota y), \iota y \rangle$ carries a subspace on which
the form of $S$ is positive definite to one for $T$ of the same dimension, so the count can only
grow. For an invertible congruence the count therefore does not change. The negative count is the
positive count of $-T$ (`LinearMap.IsSymmetric.eigenvalues_neg`), and the zero count is the rest.

## Implementation notes

* Mathlib's `sigPos` (in `Mathlib.LinearAlgebra.QuadraticForm.Signature`) is the uniqueness half of
  Sylvester's law for quadratic forms over a linearly ordered field. It does not reach complex
  Hermitian matrices, because a sesquilinear form is not a `QuadraticMap`, and it says nothing about
  eigenvalues. The results for $\mathbb{K} = \mathbb{R}$ let either theory be used on real symmetric
  matrices.
* The eigenvalues of a symmetric operator are `LinearMap.IsSymmetric.eigenvalues`, indexed by
  `Fin n` with $n = \dim E$. The eigenvalues of a Hermitian matrix are
  `Matrix.IsHermitian.eigenvalues`, indexed by the index type of the matrix.
-/

open Finset

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {n : ℕ} {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n)
include hT

/-- Let $T$ be a symmetric operator on a finite-dimensional inner product space $E$. If $x \neq 0$
lies in the span of the eigenvectors of $T$ for the positive eigenvalues, then
$\operatorname{Re} \langle T x, x \rangle > 0$.

In the eigenbasis, $\operatorname{Re} \langle T x, x \rangle = \sum_i \lambda_i |x_i|^2$, every
term is nonnegative, and one term is positive. The span is
`LinearMap.IsSymmetric.eigenvectorSpan`. -/
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

/-- **The positive count is a maximal dimension.** Let $T$ be a symmetric operator on a
finite-dimensional inner product space $E$. Then the number of positive eigenvalues of $T$,
counted with multiplicity, is the largest dimension of a subspace $S \subseteq E$ with
$\operatorname{Re} \langle T x, x \rangle > 0$ for every nonzero $x \in S$.

The span of the eigenvectors for the positive eigenvalues attains the maximum
(`LinearMap.IsSymmetric.re_inner_pos_of_mem_eigenvectorSpan_pos`). Any other such subspace meets
the span of the eigenvectors for the nonpositive eigenvalues, on which
$\operatorname{Re} \langle T x, x \rangle \le 0$, only in $0$, so its dimension is at most
$n - (n - \#\mathrm{pos})$ (`Submodule.exists_mem_inf_ne_zero`). -/
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

/-- Let $T$ be a symmetric operator on a finite-dimensional inner product space. The number of
positive eigenvalues of $-T$ equals the number of negative eigenvalues of $T$.

The eigenvalues of $-T$ are the negatives of those of $T$ in reversed order
(`LinearMap.IsSymmetric.eigenvalues_neg`). -/
theorem card_pos_eigenvalues_neg :
    #{i | 0 < hT.neg.eigenvalues hn i} = #{i | hT.eigenvalues hn i < 0} := by
  simp_rw [hT.eigenvalues_neg hn, neg_pos]
  rw [← Finset.map_univ_equiv Fin.revPerm, Finset.filter_map, Finset.card_map]
  congr 1
  ext i
  simp

/-- **The negative count is a maximal dimension.** Let $T$ be a symmetric operator on a
finite-dimensional inner product space $E$. Then the number of negative eigenvalues of $T$,
counted with multiplicity, is the largest dimension of a subspace $S \subseteq E$ with
$\operatorname{Re} \langle T x, x \rangle < 0$ for every nonzero $x \in S$.

This is `LinearMap.IsSymmetric.card_pos_eigenvalues_isGreatest` for $-T$. -/
theorem card_neg_eigenvalues_isGreatest :
    IsGreatest {d | ∃ S : Submodule 𝕜 E, Module.finrank 𝕜 S = d ∧
        ∀ x ∈ S, x ≠ 0 → RCLike.re (inner 𝕜 (T x) x) < 0}
      #{i | hT.eigenvalues hn i < 0} := by
  rw [← hT.card_pos_eigenvalues_neg hn]
  convert hT.neg.card_pos_eigenvalues_isGreatest hn using 7
  simp [inner_neg_left]

/-- **Congruence can only increase the positive count.** Let $S$ and $T$ be symmetric operators on
finite-dimensional inner product spaces $F$ and $E$, and let $\iota : F \to E$ be linear and
injective with
$$\operatorname{Re} \langle S y, y \rangle = \operatorname{Re} \langle T (\iota y), \iota y
  \rangle \quad \text{for every } y \in F.$$
Then $S$ has at most as many positive eigenvalues as $T$.

The map $\iota$ carries a subspace on which the form of $S$ is positive definite to one for $T$
of the same dimension. -/
theorem card_pos_eigenvalues_le_of_re_inner_eq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] {m : ℕ} {S : F →ₗ[𝕜] F}
    (hS : S.IsSymmetric) (hm : Module.finrank 𝕜 F = m) {ι : F →ₗ[𝕜] E}
    (hι : Function.Injective ι)
    (h : ∀ y, RCLike.re (inner 𝕜 (S y) y) = RCLike.re (inner 𝕜 (T (ι y)) (ι y))) :
    #{i | 0 < hS.eigenvalues hm i} ≤ #{i | 0 < hT.eigenvalues hn i} := by
  obtain ⟨⟨V, hV, hVpos⟩, -⟩ := hS.card_pos_eigenvalues_isGreatest hm
  refine (hT.card_pos_eigenvalues_isGreatest hn).2 ⟨V.map ι, ?_, ?_⟩
  · rw [LinearMap.finrank_map_of_injective _ hι, hV]
  · rintro _ ⟨y, hy, rfl⟩ hy0
    rw [← h]
    exact hVpos y hy fun h0 => hy0 (by simp [h0])

/-- **Congruence can only increase the negative count.** Let $S$ and $T$ be symmetric operators on
finite-dimensional inner product spaces $F$ and $E$, and let $\iota : F \to E$ be linear and
injective with $\operatorname{Re} \langle S y, y \rangle = \operatorname{Re} \langle T (\iota
y), \iota y \rangle$ for every $y \in F$. Then $S$ has at most as many negative eigenvalues as
$T$.

This is `LinearMap.IsSymmetric.card_pos_eigenvalues_le_of_re_inner_eq` applied to $-S$ and $-T$. -/
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

/-- The **inertia** of a Hermitian matrix $A \in \mathbb{K}^{n \times n}$ (§8.1.5 of
[golub2013matrix]): the triple $(n_-, n_0, n_+)$ of the numbers of negative, zero and positive
eigenvalues of $A$, counted with multiplicity.

The counts are taken over `Matrix.IsHermitian.eigenvalues`. Any indexing of the eigenvalues
gives the same counts (`Matrix.IsHermitian.inertia_eq_eigenvalues₀`). -/
noncomputable def inertia {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℕ × ℕ × ℕ :=
  (#{i | hA.eigenvalues i < 0}, #{i | hA.eigenvalues i = 0}, #{i | 0 < hA.eigenvalues i})

/-- The inertia of a Hermitian matrix $A$ is the triple of the numbers of negative, zero and
positive entries of the sorted eigenvalues `Matrix.IsHermitian.eigenvalues₀` of $A$.

The eigenvalues indexed by the index type of $A$ are the sorted eigenvalues composed with a
bijection, which changes no count. -/
theorem inertia_eq_eigenvalues₀ {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    hA.inertia = (#{k | hA.eigenvalues₀ k < 0}, #{k | hA.eigenvalues₀ k = 0},
      #{k | 0 < hA.eigenvalues₀ k}) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact Finset.card_filter_comp_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      (fun x => hA.eigenvalues₀ x < 0)
  · exact Finset.card_filter_comp_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      (fun x => hA.eigenvalues₀ x = 0)
  · exact Finset.card_filter_comp_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      (fun x => 0 < hA.eigenvalues₀ x)

/-- The three counts of the inertia of a Hermitian matrix $A \in \mathbb{K}^{n \times n}$ add up to
$n$: $n_- + n_0 + n_+ = n$. -/
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

/-- The inertia depends only on the matrix, not on the proof that it is Hermitian: if $A = B$, the
two inertias agree. -/
theorem inertia_congr {A B : Matrix n n 𝕜} (h : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    hA.inertia = hB.inertia := by
  subst h
  rfl

/-- The positive count of the inertia of $A$ is the positive count of the operator
`Matrix.toEuclideanLin A`. -/
private theorem inertia_pos_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    hA.inertia.2.2 = #{k | 0 < (isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
      finrank_euclideanSpace k} := by
  rw [inertia_eq_eigenvalues₀]
  rfl

/-- The negative count of the inertia of $A$ is the negative count of the operator
`Matrix.toEuclideanLin A`. -/
private theorem inertia_neg_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    hA.inertia.1 = #{k | (isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
      finrank_euclideanSpace k < 0} := by
  rw [inertia_eq_eigenvalues₀]
  rfl

/-- Half of Sylvester's law: a congruence $A \mapsto X^H A X$ with $X$ injective does not increase
the positive and negative counts. -/
private theorem inertia_conj_le {A : Matrix n n 𝕜} (hA : A.IsHermitian) {X : Matrix n n 𝕜}
    (hX : Function.Injective (toEuclideanLin X)) :
    (isHermitian_conjTranspose_mul_mul X hA).inertia.1 ≤ hA.inertia.1 ∧
      (isHermitian_conjTranspose_mul_mul X hA).inertia.2.2 ≤ hA.inertia.2.2 := by
  rw [inertia_pos_eq, inertia_pos_eq, inertia_neg_eq, inertia_neg_eq]
  have hq := fun y => congrArg RCLike.re (inner_toEuclideanLin_conjTranspose_mul_mul_apply A X y)
  exact ⟨(isSymmetric_toEuclideanLin_iff.mpr hA).card_neg_eigenvalues_le_of_re_inner_eq
      finrank_euclideanSpace _ finrank_euclideanSpace hX hq,
    (isSymmetric_toEuclideanLin_iff.mpr hA).card_pos_eigenvalues_le_of_re_inner_eq
      finrank_euclideanSpace _ finrank_euclideanSpace hX hq⟩

/-- **Sylvester's law of inertia** (Theorem 8.1.17 of [golub2013matrix]). Let
$A \in \mathbb{K}^{n \times n}$ be Hermitian and let $X \in \mathbb{K}^{n \times n}$ be
invertible. Then $X^H A X$ has the same inertia as $A$.

The positive and negative counts can only decrease under an injective congruence
(`LinearMap.IsSymmetric.card_pos_eigenvalues_le_of_re_inner_eq` and
`LinearMap.IsSymmetric.card_neg_eigenvalues_le_of_re_inner_eq`), and $X^{-1}$ undoes $X$. The
zero count is the rest (`Matrix.IsHermitian.inertia_sum`). -/
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

/-- Let $A$ be Hermitian with inertia $(n_-, n_0, n_+)$. Then $-A$ has the inertia
$(n_+, n_0, n_-)$. -/
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

/-- **The inertia of a real diagonal matrix.** For $d \in \mathbb{R}^n$, the matrix
$D = \operatorname{diag}(d)$ over $\mathbb{K}$ has the inertia
$$\bigl(\#\{i : d_i < 0\},\ \#\{i : d_i = 0\},\ \#\{i : d_i > 0\}\bigr).$$

The eigenvalues of $D$ are its entries up to order, since both are the roots of the
characteristic polynomial $\prod_i (X - d_i)$
(`Matrix.IsHermitian.roots_charpoly_eq_eigenvalues`). -/
theorem inertia_diagonal (d : n → ℝ) (hD : (diagonal fun i => (d i : 𝕜)).IsHermitian) :
    hD.inertia = (#{i | d i < 0}, #{i | d i = 0}, #{i | 0 < d i}) := by
  have hm := hD.map_eigenvalues_diagonal
  have hc : ∀ (p : ℝ → Prop) [DecidablePred p], #{i | p (hD.eigenvalues i)} = #{i | p (d i)} := by
    intro p _
    have := congrArg (Multiset.countP p) hm
    rwa [Multiset.countP_map, Multiset.countP_map] at this
  simp only [inertia]
  rw [hc (· < 0), hc (· = 0), hc (0 < ·)]

/-- Let $A \in \mathbb{K}^{n \times n}$ be Hermitian and $\mu \in \mathbb{R}$. Then the sorted
eigenvalues of $A - \mu I$ are those of $A$ shifted by $\mu$:
$$\lambda_k(A - \mu I) = \lambda_k(A) - \mu \quad \text{for every } k.$$

The quadratic forms differ by exactly $\mu \|x\|^2$, and
`LinearMap.IsSymmetric.eigenvalues_le_add_of_re_inner_le` applies in both directions. The sorted
eigenvalues are `Matrix.IsHermitian.eigenvalues₀`. -/
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

/-- **Bridge to Mathlib's signature**, positive part. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric. Then the number of positive eigenvalues of $A$ is `sigPos` of the quadratic form
$x \mapsto x^T A x$ (`Matrix.toQuadraticForm' A`).

Both numbers are the largest dimension of a subspace on which the form is positive definite
(`LinearMap.IsSymmetric.card_pos_eigenvalues_isGreatest` and `sigPos_isGreatest`), transported
along the identification of `EuclideanSpace ℝ n` with `n → ℝ`. -/
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
    rw [toQuadraticForm'_ofLp]
    exact hS x hx fun h => hx0 (by simp [h])
  · rintro ⟨V, rfl, hV⟩
    refine ⟨V.map e.symm.toLinearMap, LinearEquiv.finrank_map_eq e.symm V, ?_⟩
    rintro _ ⟨v, hv, rfl⟩ hx0
    have := hV ⟨v, hv⟩ fun h => hx0 (by rw [show v = 0 from congrArg Subtype.val h, map_zero])
    rw [QuadraticMap.restrict_apply] at this
    rw [← toQuadraticForm'_ofLp]
    exact this

/-- **Bridge to Mathlib's signature**, negative part. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric. Then the number of negative eigenvalues of $A$ is `sigNeg` of the quadratic form
$x \mapsto x^T A x$ (`Matrix.toQuadraticForm' A`).

This is the positive part for $-A$ (`Matrix.IsHermitian.inertia_neg` and `sigPos_neg`). -/
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

/-- **Counting eigenvalues with an $L D L^T$ factorization** (§8.4.2 of [golub2013matrix], last
paragraph). Let $A \in \mathbb{R}^{n \times n}$ be symmetric, let $\mu \in \mathbb{R}$, let $L$
be unit lower triangular and $d \in \mathbb{R}^n$, with
$$A - \mu I = L \operatorname{diag}(d) L^T.$$
Then the number of eigenvalues of $A$ below $\mu$, counted with multiplicity, is the number of
negative pivots: $\#\{i : \lambda_i < \mu\} = \#\{i : d_i < 0\}$.

The factorization $A - \mu I = L D L^T$ is a congruence by the invertible $L^T$
(`Matrix.IsHermitian.inertia_conj` and `Matrix.IsHermitian.inertia_diagonal`), and the negative
eigenvalues of $A - \mu I$ are the $\lambda_i - \mu$ with $\lambda_i < \mu$
(`Matrix.IsHermitian.eigenvalues₀_sub_smul_one`). The factorization is `Matrix.IsLDM`, and the
index type carries a linear order for the triangularity. -/
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
  exact Finset.card_filter_comp_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun x => hA.eigenvalues₀ x < μ)

end Matrix.IsHermitian
