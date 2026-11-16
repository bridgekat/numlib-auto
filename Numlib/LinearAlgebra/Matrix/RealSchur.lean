/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Schur`, beside the complex triangulation.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Numlib.Analysis.Complex.Polynomial.Basic
import Numlib.LinearAlgebra.Matrix.Hessenberg

/-!
# The real Schur form

Every real square matrix $A$ is orthogonally similar to a quasi upper triangular matrix: there is an
orthogonal matrix $Q$ such that $Q^T A Q$ is block upper triangular with diagonal blocks of size
$1 \times 1$ or $2 \times 2$, and the $2 \times 2$ blocks carry the pairs of complex conjugate
eigenvalues. This is the **real Schur form** of Theorem 7.4.1 of [golub2013matrix], called the
quasi-Schur form in §1.8.3 of [saad2003iterative]. The sharper form of Property 5.8 of
[quarteroni2000numerical] also requires that no $2 \times 2$ diagonal block has a real eigenvalue,
and this module proves it too.

The proof of the complex Schur triangulation does not carry over directly, because over $\mathbb{R}$
an operator need not have an eigenvector. The induction instead splits off an invariant subspace of
dimension one or two, and the $2 \times 2$ blocks come from the invariant planes. The module also
shows that the eigenvalues of a real orthogonal matrix of even order $2m$ with determinant $1$ are
$m$ conjugate pairs $e^{\pm i \theta_k}$.

## Main definitions

* `Matrix.IsQuasiUpperTriangular`: $T$ is block upper triangular for a monotone block index whose
  fibres, the diagonal blocks, have at most two elements.

## Main results

* `LinearMap.exists_invariant_finrank_le_two`: a linear operator on a nonzero finite-dimensional
  real vector space has a nonzero invariant subspace of dimension at most two.
* `LinearMap.exists_invariant_finrank_eq_one_or_two`: such an operator has an invariant line, or an
  invariant plane that contains no eigenvector.
* `Matrix.isQuasiUpperTriangular_iff_fin`: a matrix indexed by $\{0, \dots, N - 1\}$ is quasi upper
  triangular if and only if it is upper Hessenberg and has no two consecutive nonzero subdiagonal
  entries.
* `Matrix.IsQuasiUpperTriangular.isUpperHessenberg`: a quasi upper triangular matrix is upper
  Hessenberg.
* `Matrix.IsQuasiUpperTriangular.mul_isUpperTriangular`,
  `Matrix.IsUpperTriangular.mul_isQuasiUpperTriangular`: the product of a quasi upper triangular
  matrix and an upper triangular matrix, in either order, is quasi upper triangular. Chapter 7 of
  [golub2013matrix] uses the quasi upper triangular shape for the real Schur, QR, QZ, periodic and
  Hamiltonian Schur forms.
* `Matrix.exists_orthogonal_conj_isQuasiUpperTriangular`: Theorem 7.4.1 of [golub2013matrix], the
  matrix $Q^T A Q$ is quasi upper triangular for some orthogonal $Q$;
  `LinearMap.exists_orthonormalBasis_isQuasiUpperTriangular` is the operator form.
* `Matrix.exists_orthogonal_conj_quasiUpperTriangular_of_irreducible_blocks`: the form of Property
  5.8 of [quarteroni2000numerical], in which no $2 \times 2$ diagonal block has a real eigenvalue,
  so that the $2 \times 2$ blocks carry exactly the pairs of complex conjugate eigenvalues.
* `Matrix.exists_orthonormal_cols_of_invariant`: an invariant subspace $X$ of a real matrix $M$ has
  a matrix $X_0$ of orthonormal columns in $X$ with $M X_0 = X_0 (X_0^T M X_0)$.
* `Matrix.exists_charpoly_eq_prod_of_mem_specialOrthogonalGroup`: the eigenvalues of a real
  orthogonal matrix of order $2m$ with determinant $1$ are $m$ conjugate pairs $e^{\pm i \theta_k}$,
  as in (12.2.19) of [golub2013matrix], which states it for orthogonal Hessenberg matrices.

## Proof outline

The invariant subspace comes from a factor of the characteristic polynomial. By the Cayley–Hamilton
theorem the characteristic polynomial annihilates every vector, so some irreducible real factor $q$
satisfies $q(A) w = 0$ for a nonzero $w$. An irreducible real polynomial has degree one or two, so
$\operatorname{span}\{w, Aw\}$ is an $A$-invariant subspace of dimension at most two. No
complexification is needed. The induction then follows the complex proof: it passes to the
orthogonal complement of an invariant subspace of the adjoint $A^*$, which is invariant under $A$
itself.

For the special orthogonal matrix, the roots of the complexified characteristic polynomial have
modulus one, come in conjugate pairs and have the product $\det H = 1$, which pairs up the real
roots $\pm 1$. No Schur form is needed.

## Implementation notes

* In the induction, the new basis vectors are appended at the end, as `Fin (m + d)` with
  `Fin.addCases`, where $d \in \{1, 2\}$ is the dimension of the subspace that is split off. The
  block index takes the value $m$ on them, which is larger than every value it takes on the first
  $m$ indices.
* The bound "at most two elements per block" is carried through the induction in the equivalent form
  `∀ i j, p i = p j → (i : ℕ) ≤ (j : ℕ) + 1`, which propagates without counting. It is turned into a
  bound on cardinalities once, at the end.
* The irreducibility of the $2 \times 2$ blocks is carried as the statement that, for two distinct
  indices $i, j$ of one block, the characteristic polynomial
  $(a_{ii} - \mu)(a_{jj} - \mu) - a_{ij} a_{ji}$ of the block has no real root $\mu$. This statement
  is symmetric in $i$ and $j$ and involves only four inner products. At the end it becomes the
  statement that the real spectrum (`spectrum ℝ`) of the diagonal block is empty.
* `Matrix.orthogonalGroup` is `Matrix.unitaryGroup` over a ring with trivial star, so membership of
  $Q$ in it means $Q^T Q = 1$.
-/

open Module Polynomial Submodule

namespace LinearMap

/-! ### An invariant subspace of dimension one or two -/

section Invariant

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- If a nonzero real polynomial annihilates a nonzero vector under a linear operator $A$, then some
irreducible real polynomial $q$ satisfies $q(A) w = 0$ for some nonzero vector $w$. -/
private theorem exists_irreducible_aeval_apply_eq_zero (A : E →ₗ[ℝ] E) (n : ℕ) :
    ∀ f : ℝ[X], f.natDegree = n → f ≠ 0 → ∀ v : E, v ≠ 0 → aeval A f v = 0 →
      ∃ q : ℝ[X], Irreducible q ∧ ∃ w : E, w ≠ 0 ∧ aeval A q w = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hfn hf0 v hv hfv
    by_cases hu : IsUnit f
    · exfalso
      obtain ⟨r, hr, hrf⟩ := Polynomial.isUnit_iff.1 hu
      have hr0 : r ≠ 0 := hr.ne_zero
      rw [← hrf, aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
        Module.End.one_apply] at hfv
      exact hv ((smul_eq_zero_iff_right hr0).1 hfv)
    rcases irreducible_or_factor hu with hirr | ⟨g, h, hgu, hhu, hgh⟩
    · exact ⟨f, hirr, v, hv, hfv⟩
    · have hg0 : g ≠ 0 := by rintro rfl; rw [zero_mul] at hgh; exact hf0 hgh
      have hh0 : h ≠ 0 := by rintro rfl; rw [mul_zero] at hgh; exact hf0 hgh
      have hdegpos : ∀ p : ℝ[X], p ≠ 0 → ¬IsUnit p → 0 < p.natDegree := by
        intro p hp0 hpu
        by_contra hcon
        have hc : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (by omega)
        have hne : p.coeff 0 ≠ 0 := fun hz => hp0 (by rw [hc, hz, map_zero])
        exact hpu (hc ▸ Polynomial.isUnit_C.2 (isUnit_iff_ne_zero.2 hne))
      have hgd := hdegpos g hg0 hgu
      have hhd := hdegpos h hh0 hhu
      have hsum : f.natDegree = g.natDegree + h.natDegree := by
        rw [hgh, Polynomial.natDegree_mul hg0 hh0]
      rw [hgh, map_mul, Module.End.mul_apply] at hfv
      by_cases hzero : aeval A h v = 0
      · exact ih h.natDegree (by omega) h rfl hh0 v hv hzero
      · exact ih g.natDegree (by omega) g rfl hg0 (aeval A h v) hzero hfv

variable [FiniteDimensional ℝ E]

/-- Let $E$ be a nonzero finite-dimensional real vector space and let $A \colon E \to E$ be linear.
Then $A$ has an invariant subspace $W$ with $W \ne 0$ and $\dim W \le 2$.

Over $\mathbb{R}$, this replaces the existence of an eigenvector, and it is the source of the
$2 \times 2$ blocks of the real Schur form. The subspace is $\operatorname{span}\{w, Aw\}$ for a
nonzero $w$ with $q(A) w = 0$, where $q$ is an irreducible real factor of the characteristic
polynomial. -/
theorem exists_invariant_finrank_le_two [Nontrivial E] (A : E →ₗ[ℝ] E) :
    ∃ W : Submodule ℝ E, W ≠ ⊥ ∧ finrank ℝ W ≤ 2 ∧ ∀ w ∈ W, A w ∈ W := by
  classical
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  obtain ⟨q, hq, w, hw, hqw⟩ :=
    exists_irreducible_aeval_apply_eq_zero A A.charpoly.natDegree A.charpoly rfl
      A.charpoly_monic.ne_zero v hv (by rw [A.aeval_self_charpoly]; rfl)
  have hqdeg : q.natDegree ≤ 2 := hq.natDegree_le_two
  have hexp : q.coeff 0 • w + q.coeff 1 • A w + q.coeff 2 • A (A w) = 0 := by
    have h := aeval_eq_sum_range' (p := q) (n := 3) (by omega) A
    rw [h] at hqw
    simpa [Finset.sum_range_succ, pow_succ, Module.End.mul_apply] using hqw
  have hmemw : w ∈ Submodule.span ℝ ({w, A w} : Set E) :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hmemAw : A w ∈ Submodule.span ℝ ({w, A w} : Set E) :=
    Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  refine ⟨Submodule.span ℝ {w, A w}, ?_, ?_, ?_⟩
  · intro hbot
    apply hw
    rw [hbot] at hmemw
    simpa using hmemw
  · calc finrank ℝ (Submodule.span ℝ ({w, A w} : Set E))
        ≤ ({w, A w} : Set E).toFinset.card := finrank_span_le_card _
      _ ≤ 2 := by
          simp only [Set.toFinset_insert, Set.toFinset_singleton]
          exact (Finset.card_insert_le _ _).trans (by simp)
  · have hAAw : A (A w) ∈ Submodule.span ℝ ({w, A w} : Set E) := by
      rcases eq_or_ne (q.coeff 2) 0 with h2 | h2
      · have hdeg1 : q.natDegree = 1 := by
          have hpos := hq.natDegree_pos
          rcases Nat.lt_or_ge q.natDegree 2 with h | h
          · omega
          · exact absurd (Polynomial.leadingCoeff_ne_zero.2 hq.ne_zero)
              (by rw [Polynomial.leadingCoeff, show q.natDegree = 2 by omega]; exact not_not.2 h2)
        have h1 : q.coeff 1 ≠ 0 := by
          have hlc := Polynomial.leadingCoeff_ne_zero.2 hq.ne_zero
          rwa [Polynomial.leadingCoeff, hdeg1] at hlc
        rw [h2, zero_smul, add_zero] at hexp
        have hstep : q.coeff 1 • A w = (-(q.coeff 0)) • w := by
          rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]
          exact hexp
        have hAw : A w = ((q.coeff 1)⁻¹ * -(q.coeff 0)) • w := by
          rw [← smul_smul, ← hstep, smul_smul, inv_mul_cancel₀ h1, one_smul]
        have hstep2 : A (A w) = ((q.coeff 1)⁻¹ * -(q.coeff 0)) • A w := by
          conv_lhs => rw [hAw]
          rw [map_smul]
        rw [hstep2]
        exact Submodule.smul_mem _ _ hmemAw
      · have hstep : q.coeff 2 • A (A w) = (-(q.coeff 0)) • w + (-(q.coeff 1)) • A w := by
          rw [neg_smul, neg_smul, ← neg_add, eq_neg_iff_add_eq_zero, add_comm]
          exact hexp
        have hAAw2 : A (A w)
            = (q.coeff 2)⁻¹ • ((-(q.coeff 0)) • w + (-(q.coeff 1)) • A w) := by
          rw [← hstep, smul_smul, inv_mul_cancel₀ h2, one_smul]
        rw [hAAw2]
        exact Submodule.smul_mem _ _
          (Submodule.add_mem _ (Submodule.smul_mem _ _ hmemw) (Submodule.smul_mem _ _ hmemAw))
    intro x hx
    have hsub : Submodule.span ℝ ({w, A w} : Set E) ≤
        Submodule.comap A (Submodule.span ℝ ({w, A w} : Set E)) := by
      rw [Submodule.span_le]
      rintro y (rfl | rfl)
      · exact hmemAw
      · exact hAAw
    exact hsub hx

/-- Let $E$ be a nonzero finite-dimensional real vector space and let $A \colon E \to E$ be linear.
Then $A$ has an invariant subspace $W$ such that either $\dim W = 1$, or $\dim W = 2$ and $W$
contains no eigenvector of $A$: if $w \in W$, $\mu \in \mathbb{R}$ and $Aw = \mu w$, then
$w = 0$.

This refinement of `LinearMap.exists_invariant_finrank_le_two` gives the real Schur form with
irreducible $2 \times 2$ blocks. If $A$ has an eigenvector, the proof takes the line that it
spans. Otherwise $A$ has no eigenvector at all, and every nonzero invariant subspace of
dimension at most two is a plane, because an invariant line is spanned by an eigenvector. -/
theorem exists_invariant_finrank_eq_one_or_two [Nontrivial E] (A : E →ₗ[ℝ] E) :
    ∃ W : Submodule ℝ E, (∀ w ∈ W, A w ∈ W) ∧
      (finrank ℝ W = 1 ∨ finrank ℝ W = 2 ∧ ∀ (μ : ℝ), ∀ w ∈ W, A w = μ • w → w = 0) := by
  by_cases h : ∃ (μ : ℝ) (v : E), v ≠ 0 ∧ A v = μ • v
  · obtain ⟨μ, v, hv, hAv⟩ := h
    refine ⟨ℝ ∙ v, fun w hw => ?_, Or.inl (finrank_span_singleton hv)⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [map_smul, hAv, smul_smul]
    exact Submodule.mem_span_singleton.2 ⟨_, rfl⟩
  · obtain ⟨W, hW0, hWd, hWinv⟩ := exists_invariant_finrank_le_two A
    refine ⟨W, hWinv, ?_⟩
    have h0 : finrank ℝ W ≠ 0 := fun h0 => hW0 (Submodule.finrank_eq_zero.1 h0)
    rcases (show finrank ℝ W = 1 ∨ finrank ℝ W = 2 by omega) with h1 | h2
    · exact Or.inl h1
    · refine Or.inr ⟨h2, fun μ w _ hw => ?_⟩
      by_contra hne
      exact h ⟨μ, w, hne, hw⟩

end Invariant

/-! ### The quasi-triangular orthonormal basis -/

section QuasiTriangular

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Let $E$ be a finite-dimensional real inner product space, let $A \colon E \to E$ be linear, and
let $W \subseteq E$ be a subspace that is invariant under the adjoint $A^*$. Then the orthogonal
complement $W^\perp$ is invariant under $A$: if $y \in W^\perp$, then $Ay \in W^\perp$.

For $u \in W$, $\langle u, Ay \rangle = \langle A^* u, y \rangle = 0$. -/
theorem mem_orthogonal_of_adjoint_invariant [FiniteDimensional ℝ E] {A : E →ₗ[ℝ] E}
    {W : Submodule ℝ E} (hW : ∀ w ∈ W, LinearMap.adjoint A w ∈ W) {y : E} (hy : y ∈ Wᗮ) :
    A y ∈ Wᗮ := by
  rw [Submodule.mem_orthogonal] at hy ⊢
  intro u hu
  rw [← LinearMap.adjoint_inner_left]
  exact hy _ (hW u hu)

/-- If a plane $W$ is invariant under $A^*$ and contains no eigenvector of $A^*$, $w_0, w_1$ is an
orthonormal basis of $W$, and $a_{ij} = \langle w_i, A w_j \rangle$, then $(a_{ii} -
\mu)(a_{jj} - \mu) - a_{ij} a_{ji} \ne 0$ for distinct $i, j \in \{0, 1\}$ and every real $\mu$. -/
private theorem block_ne_zero [FiniteDimensional ℝ E] {A : E →ₗ[ℝ] E} {W : Submodule ℝ E}
    (hW : ∀ w ∈ W, LinearMap.adjoint A w ∈ W)
    (hW2 : ∀ (μ : ℝ), ∀ w ∈ W, LinearMap.adjoint A w = μ • w → w = 0)
    (wb : OrthonormalBasis (Fin 2) ℝ W) (μ : ℝ) {a b : Fin 2} (hab : a ≠ b) :
    (inner ℝ (wb a : E) (A (wb a)) - μ) * (inner ℝ (wb b : E) (A (wb b)) - μ)
      - inner ℝ (wb a : E) (A (wb b)) * inner ℝ (wb b : E) (A (wb a)) ≠ 0 := by
  suffices key : (inner ℝ (wb 0 : E) (A (wb 0)) - μ) * (inner ℝ (wb 1 : E) (A (wb 1)) - μ)
      - inner ℝ (wb 0 : E) (A (wb 1)) * inner ℝ (wb 1 : E) (A (wb 0)) ≠ 0 by
    have h2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
    rcases h2 a with rfl | rfl <;> rcases h2 b with rfl | rfl
    · exact absurd rfl hab
    · exact key
    · intro h
      apply key
      linear_combination h
    · exact absurd rfl hab
  intro hzero
  obtain ⟨B, hB⟩ : ∃ B : E →ₗ[ℝ] E, B = LinearMap.adjoint A := ⟨_, rfl⟩
  rw [← hB] at hW hW2
  have hadj : ∀ x y : W, inner ℝ (x : E) (A y) = inner ℝ (y : E) (B x) := fun x y => by
    rw [hB, ← LinearMap.adjoint_inner_left, real_inner_comm]
  -- `B` expanded on the orthonormal basis of `W`
  have hexp : ∀ x : W, B x = inner ℝ (wb 0 : E) (B x) • (wb 0 : E)
      + inner ℝ (wb 1 : E) (B x) • (wb 1 : E) := by
    intro x
    have h := congrArg Subtype.val (wb.sum_repr' ⟨B x, hW x x.2⟩)
    rw [Fin.sum_univ_two] at h
    simpa [Submodule.coe_inner] using h.symm
  -- the characteristic polynomial of the block matrix of `B` vanishes at `μ`
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin 2) (Fin 2) ℝ,
      N = Matrix.of fun i j => inner ℝ (wb i : E) (B (wb j)) - if i = j then μ else 0 :=
    ⟨_, rfl⟩
  have hdet : N.det = 0 := by
    rw [Matrix.det_fin_two, hN]
    simp only [Matrix.of_apply, ite_true, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, ite_false,
      sub_zero, OfNat.ofNat_ne_one]
    rw [hadj, hadj, hadj, hadj] at hzero
    linear_combination hzero
  obtain ⟨c, hc0, hNc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have h0 := congrFun hNc 0
  have h1 := congrFun hNc 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hN, Matrix.of_apply, Pi.zero_apply,
    ite_true, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, ite_false, sub_zero,
    OfNat.ofNat_ne_one] at h0 h1
  -- the eigenvector of `B` in `W`
  obtain ⟨v, hv⟩ : ∃ v : W, v = c 0 • wb 0 + c 1 • wb 1 := ⟨_, rfl⟩
  have hBv : B v = μ • (v : E) := by
    rw [hv, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, map_add, map_smul,
      map_smul, hexp (wb 0), hexp (wb 1)]
    linear_combination (norm := module) h0 • (wb 0 : E) + h1 • (wb 1 : E)
  have hv0 : v = 0 := Submodule.coe_eq_zero.1 (hW2 μ v v.2 hBv)
  have hli := Fintype.linearIndependent_iff.1 wb.orthonormal.linearIndependent c
    (by rw [Fin.sum_univ_two, ← hv, hv0])
  exact hc0 (funext hli)

/-- For every linear operator $A$ on a real inner product space of dimension $n$ there are an
orthonormal basis $b_0, \dots, b_{n-1}$ and a monotone block index $p$ with values below $n$
such that $p(i) = p(j)$ implies $i \le j + 1$, the entries $\langle b_i, A b_j \rangle$ with
$p(j) < p(i)$ vanish, and the $2 \times 2$ diagonal blocks have no real eigenvalue. -/
private theorem exists_orthonormalBasis_aux (n : ℕ) :
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
      finrank ℝ E = n → ∀ A : E →ₗ[ℝ] E,
        ∃ (b : OrthonormalBasis (Fin n) ℝ E) (p : Fin n → ℕ), Monotone p ∧ (∀ i, p i < n) ∧
          (∀ i j, p i = p j → (i : ℕ) ≤ (j : ℕ) + 1) ∧
          (∀ i j : Fin n, p j < p i → (inner ℝ (b i) (A (b j)) : ℝ) = 0) ∧
          ∀ i j : Fin n, p i = p j → i ≠ j → ∀ μ : ℝ,
            (inner ℝ (b i) (A (b i)) - μ) * (inner ℝ (b j) (A (b j)) - μ)
              - inner ℝ (b i) (A (b j)) * inner ℝ (b j) (A (b i)) ≠ 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E _ _ _ hE A
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨(stdOrthonormalBasis ℝ E).reindex (finCongr hE), fun i => i.elim0,
        fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    have : Nontrivial E := nontrivial_of_finrank_pos (R := ℝ) (by rw [hE]; exact hn)
    obtain ⟨W, hWinv, hW⟩ := exists_invariant_finrank_eq_one_or_two (LinearMap.adjoint A)
    obtain ⟨d, hd⟩ : ∃ d, finrank ℝ W = d := ⟨_, rfl⟩
    obtain ⟨m, hm⟩ : ∃ m, finrank ℝ (Wᗮ : Submodule ℝ E) = m := ⟨_, rfl⟩
    have hd1 : 1 ≤ d := by rcases hW with h | ⟨h, -⟩ <;> omega
    have hd2 : d ≤ 2 := by rcases hW with h | ⟨h, -⟩ <;> omega
    have hW2 : d = 2 → ∀ (μ : ℝ), ∀ w ∈ W, LinearMap.adjoint A w = μ • w → w = 0 := by
      intro hd2'
      rcases hW with h | ⟨-, h⟩
      · omega
      · exact h
    have hsum : d + m = n := by
      rw [← hd, ← hm, Submodule.finrank_add_finrank_orthogonal, hE]
    have hinv : ∀ y ∈ (Wᗮ : Submodule ℝ E), A y ∈ (Wᗮ : Submodule ℝ E) := fun _ hy =>
      mem_orthogonal_of_adjoint_invariant hWinv hy
    obtain ⟨c, p', hp'mono, hp'lt, hp'close, hp'tri, hp'irr⟩ :=
      ih m (by omega) (E := (Wᗮ : Submodule ℝ E)) hm (A.restrict hinv)
    obtain ⟨wb, -⟩ : ∃ wb : OrthonormalBasis (Fin d) ℝ W, True :=
      ⟨(stdOrthonormalBasis ℝ W).reindex (finCongr hd), trivial⟩
    obtain rfl : n = m + d := by omega
    obtain ⟨f, hf⟩ : ∃ f : Fin (m + d) → E,
        f = Fin.addCases (fun i => ((c i : (Wᗮ : Submodule ℝ E)) : E))
          (fun i => ((wb i : W) : E)) := ⟨_, rfl⟩
    obtain ⟨p, hp⟩ : ∃ p : Fin (m + d) → ℕ,
        p = Fin.addCases (fun i => p' i) (fun _ => m) := ⟨_, rfl⟩
    have hfl : ∀ i : Fin m, f (Fin.castAdd d i) = ((c i : (Wᗮ : Submodule ℝ E)) : E) := by
      intro i; rw [hf]; exact Fin.addCases_left i
    have hfr : ∀ i : Fin d, f (Fin.natAdd m i) = ((wb i : W) : E) := by
      intro i; rw [hf]; exact Fin.addCases_right i
    have hpl : ∀ i : Fin m, p (Fin.castAdd d i) = p' i := by
      intro i; rw [hp]; exact Fin.addCases_left i
    have hpr : ∀ i : Fin d, p (Fin.natAdd m i) = m := by
      intro i; rw [hp]; exact Fin.addCases_right i
    -- the appended vectors lie in `W`, the others in `Wᗮ`
    have hmemW : ∀ i : Fin d, f (Fin.natAdd m i) ∈ W := fun i => by rw [hfr]; exact (wb i).2
    have hmemWo : ∀ i : Fin m, f (Fin.castAdd d i) ∈ (Wᗮ : Submodule ℝ E) := fun i => by
      rw [hfl]; exact (c i).2
    have hon : Orthonormal ℝ f := by
      constructor
      · intro i
        induction i using Fin.addCases with
        | left i => rw [hfl]; exact c.orthonormal.1 i
        | right i => rw [hfr]; exact wb.orthonormal.1 i
      · intro i j hij
        induction i using Fin.addCases with
        | left i =>
          induction j using Fin.addCases with
          | left j =>
            rw [hfl, hfl, ← Submodule.coe_inner]
            exact c.orthonormal.2 fun h => hij (by rw [h])
          | right j =>
            rw [inner_eq_zero_symm]
            exact (Submodule.mem_orthogonal _ _).1 (hmemWo i) _ (hmemW j)
        | right i =>
          induction j using Fin.addCases with
          | left j => exact (Submodule.mem_orthogonal _ _).1 (hmemWo j) _ (hmemW i)
          | right j =>
            rw [hfr, hfr, ← Submodule.coe_inner]
            exact wb.orthonormal.2 fun h => hij (by rw [h])
    have hcard : Fintype.card (Fin (m + d)) = finrank ℝ E := by simp [hE]
    have : Nonempty (Fin (m + d)) := Fin.pos_iff_nonempty.1 (by omega)
    -- the inner products of the first `m` vectors are those of the smaller space
    have hinner : ∀ i j : Fin m, inner ℝ (f (Fin.castAdd d i)) (A (f (Fin.castAdd d j)))
        = inner ℝ (c i) ((A.restrict hinv) (c j)) := fun i j => by
      rw [hfl, hfl, show A ((c j : (Wᗮ : Submodule ℝ E)) : E)
          = (((A.restrict hinv) (c j) : (Wᗮ : Submodule ℝ E)) : E) from rfl,
        ← Submodule.coe_inner]
    refine ⟨(basisOfOrthonormalOfCardEqFinrank hon hcard).toOrthonormalBasis (by simpa using hon),
      p, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hle
      induction i using Fin.addCases with
      | left i =>
        induction j using Fin.addCases with
        | left j =>
          have hle' : (i : ℕ) ≤ (j : ℕ) := by
            rw [Fin.le_def, Fin.val_castAdd, Fin.val_castAdd] at hle
            exact hle
          rw [hpl, hpl]
          exact hp'mono (Fin.le_def.2 hle')
        | right j => rw [hpl, hpr]; exact (hp'lt i).le
      | right i =>
        induction j using Fin.addCases with
        | left j =>
          exfalso
          rw [Fin.le_def, Fin.val_natAdd, Fin.val_castAdd] at hle
          omega
        | right j => rw [hpr, hpr]
    · intro i
      induction i using Fin.addCases with
      | left i => have := hp'lt i; rw [hpl]; omega
      | right i => rw [hpr]; omega
    · intro i j hij
      induction i using Fin.addCases with
      | left i =>
        induction j using Fin.addCases with
        | left j =>
          rw [hpl, hpl] at hij
          simpa [Fin.val_castAdd] using hp'close i j hij
        | right j =>
          rw [hpl, hpr] at hij
          exact absurd hij (Nat.ne_of_lt (hp'lt i))
      | right i =>
        induction j using Fin.addCases with
        | left j =>
          rw [hpr, hpl] at hij
          exact absurd hij.symm (Nat.ne_of_lt (hp'lt j))
        | right j =>
          simp only [Fin.val_natAdd]
          omega
    · intro i j hji
      rw [Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]
      induction i using Fin.addCases with
      | left i =>
        induction j using Fin.addCases with
        | left j =>
          rw [hpl, hpl] at hji
          rw [hinner]
          exact hp'tri i j hji
        | right j =>
          exfalso
          have := hp'lt i
          rw [hpl, hpr] at hji
          omega
      | right i =>
        induction j using Fin.addCases with
        | left j =>
          have hAj : A (f (Fin.castAdd d j)) ∈ (Wᗮ : Submodule ℝ E) := hinv _ (hmemWo j)
          exact (Submodule.mem_orthogonal _ _).1 hAj _ (hmemW i)
        | right j =>
          exfalso
          rw [hpr, hpr] at hji
          omega
    · intro i j hij hne μ
      rw [Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]
      induction i using Fin.addCases with
      | left i =>
        induction j using Fin.addCases with
        | left j =>
          rw [hpl, hpl] at hij
          simp only [hinner]
          exact hp'irr i j hij (fun h => hne (by rw [h])) μ
        | right j =>
          rw [hpl, hpr] at hij
          exact absurd hij (Nat.ne_of_lt (hp'lt i))
      | right i =>
        induction j using Fin.addCases with
        | left j =>
          rw [hpr, hpl] at hij
          exact absurd hij.symm (Nat.ne_of_lt (hp'lt j))
        | right j =>
          -- two distinct indices in the new block: it is a plane without eigenvectors
          have hab : i ≠ j := fun h => hne (by rw [h])
          obtain rfl : d = 2 := by
            have := Fin.val_ne_of_ne hab
            have := i.isLt
            have := j.isLt
            omega
          rw [hfr, hfr]
          exact block_ne_zero hWinv (hW2 rfl) wb μ hab

/-- If a block index $p$ on $\{0, \dots, n - 1\}$ satisfies $i \le j + 1$ whenever $p(i) = p(j)$,
then every fibre of $p$ has at most two elements. -/
private theorem card_filter_le_two {n : ℕ} {p : Fin n → ℕ}
    (h : ∀ i j, p i = p j → (i : ℕ) ≤ (j : ℕ) + 1) (k : ℕ) :
    (Finset.univ.filter fun i => p i = k).card ≤ 2 := by
  by_contra hcon
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.1 (Nat.lt_of_not_le hcon)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
  have hval : ∀ x y : Fin n, x ≠ y → (x : ℕ) ≠ (y : ℕ) :=
    fun x y hxy hv => hxy (Fin.val_injective hv)
  have h1 := h a b (ha.trans hb.symm)
  have h2 := h b a (hb.trans ha.symm)
  have h3 := h a c (ha.trans hc.symm)
  have h4 := h c a (hc.trans ha.symm)
  have h5 := h b c (hb.trans hc.symm)
  have h6 := h c b (hc.trans hb.symm)
  have := hval a b hab
  have := hval a c hac
  have := hval b c hbc
  omega

variable [FiniteDimensional ℝ E]

/-- Let $E$ be a finite-dimensional real inner product space of dimension $n$ and let
$A \colon E \to E$ be linear. Then there are an orthonormal basis $b_0, \dots, b_{n-1}$ of $E$
and a monotone block index $p \colon \{0, \dots, n - 1\} \to \mathbb{N}$ such that, with
$a_{ij} = \langle b_i, A b_j \rangle$:

* every fibre of $p$ has at most two elements;
* $a_{ij} = 0$ whenever $p(j) < p(i)$;
* for distinct $i, j$ with $p(i) = p(j)$ and every real $\mu$, $(a_{ii} - \mu)(a_{jj} - \mu) -
  a_{ij} a_{ji} \ne 0$.

So the matrix of $A$ in the basis $b$ is quasi upper triangular, no $2 \times 2$ diagonal block
has a real eigenvalue, and each $2 \times 2$ block carries a pair of complex conjugate
eigenvalues. This is the operator form of Property 5.8 of [quarteroni2000numerical], the sharper
form of Theorem 7.4.1 of [golub2013matrix].

At each step, the induction splits off an invariant line of the adjoint or an invariant plane on
which the adjoint has no eigenvector (`LinearMap.exists_invariant_finrank_eq_one_or_two`). -/
theorem exists_orthonormalBasis_quasiUpperTriangular_of_irreducible_blocks {n : ℕ}
    (hn : finrank ℝ E = n) (A : E →ₗ[ℝ] E) :
    ∃ (b : OrthonormalBasis (Fin n) ℝ E) (p : Fin n → ℕ), Monotone p ∧
      (∀ k, (Finset.univ.filter fun i => p i = k).card ≤ 2) ∧
      (∀ i j : Fin n, p j < p i → (inner ℝ (b i) (A (b j)) : ℝ) = 0) ∧
      ∀ i j : Fin n, p i = p j → i ≠ j → ∀ μ : ℝ,
        (inner ℝ (b i) (A (b i)) - μ) * (inner ℝ (b j) (A (b j)) - μ)
          - inner ℝ (b i) (A (b j)) * inner ℝ (b j) (A (b i)) ≠ 0 := by
  obtain ⟨b, p, hmono, -, hclose, htri, hirr⟩ := exists_orthonormalBasis_aux n hn A
  exact ⟨b, p, hmono, fun k => card_filter_le_two hclose k, htri, hirr⟩

end QuasiTriangular

end LinearMap

namespace Matrix

/-- Let $A \in \mathbb{R}^{N \times N}$. Then there are an orthogonal
$Q \in \mathbb{R}^{N \times N}$ and a monotone block index
$p \colon \{0, \dots, N - 1\} \to \mathbb{N}$ whose fibres have at most two elements, such that
$Q^T A Q$ is block upper triangular for $p$ and no $2 \times 2$ diagonal block has a real
eigenvalue: for every $k$ whose fibre has two elements, the $k$-th diagonal block of $Q^T A Q$
has no real number in its spectrum. Thus the $2 \times 2$ blocks carry the pairs of complex
conjugate eigenvalues and the $1 \times 1$ blocks carry the real eigenvalues. This is Property
5.8 of [quarteroni2000numerical], the sharper form of Theorem 7.4.1 of [golub2013matrix].

The blocks are the fibres of $p$, and `(Qᵀ * A * Q).toBlock (fun i => p i = k) (fun i => p i =
k)` is the $k$-th diagonal block. Block upper triangular for $p$ is `Matrix.BlockTriangular p`:
the entries $(i, j)$ with $p(j) < p(i)$ vanish. `Matrix.orthogonalGroup` is
`Matrix.unitaryGroup` over a ring with trivial star, so the membership means $Q^T Q = 1$. -/
theorem exists_orthogonal_conj_quasiUpperTriangular_of_irreducible_blocks {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) :
    ∃ Q ∈ Matrix.orthogonalGroup (Fin N) ℝ, ∃ p : Fin N → ℕ, Monotone p ∧
      (∀ k, (Finset.univ.filter fun i => p i = k).card ≤ 2) ∧ (Qᵀ * A * Q).BlockTriangular p ∧
      ∀ k, (Finset.univ.filter fun i => p i = k).card = 2 → ∀ μ : ℝ,
        μ ∉ spectrum ℝ ((Qᵀ * A * Q).toBlock (fun i => p i = k) (fun i => p i = k)) := by
  obtain ⟨b, p, hmono, hcard, htri, hirr⟩ :=
    LinearMap.exists_orthonormalBasis_quasiUpperTriangular_of_irreducible_blocks
      (E := EuclideanSpace ℝ (Fin N)) (n := N) finrank_euclideanSpace_fin (Matrix.toEuclideanLin A)
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)),
      v₀ = EuclideanSpace.basisFun (Fin N) ℝ := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin N) (Fin N) ℝ, Q = v₀.toBasis.toMatrix b.toBasis := ⟨_, rfl⟩
  have hQu : Q ∈ unitaryGroup (Fin N) ℝ := by
    rw [hQdef, OrthonormalBasis.coe_toBasis]
    exact v₀.toMatrix_orthonormalBasis_mem_unitary b
  have hstarQ : star Q = Qᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose, Matrix.transpose]
    ext i j
    simp
  have hA : LinearMap.toMatrix v₀.toBasis v₀.toBasis (Matrix.toEuclideanLin A) = A := by
    rw [hv₀, Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
  have hstar : b.toBasis.toMatrix v₀.toBasis = star Q := by
    have h1 : b.toBasis.toMatrix v₀.toBasis * Q = 1 := by
      rw [hQdef]; exact Module.Basis.toMatrix_mul_toMatrix_flip _ _
    calc b.toBasis.toMatrix v₀.toBasis
        = b.toBasis.toMatrix v₀.toBasis * (Q * star Q) := by
          rw [mem_unitaryGroup_iff.1 hQu, mul_one]
      _ = star Q := by rw [← mul_assoc, h1, one_mul]
  have hconj : Qᵀ * A * Q
      = LinearMap.toMatrix b.toBasis b.toBasis (Matrix.toEuclideanLin A) := by
    conv_lhs => rw [← hA, ← hstarQ, ← hstar, hQdef]
    exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b.toBasis v₀.toBasis
      b.toBasis v₀.toBasis (Matrix.toEuclideanLin A)
  -- the entries of `Qᵀ A Q` are the inner products `⟪b i, A (b j)⟫`
  have hT : ∀ i j, (Qᵀ * A * Q) i j = inner ℝ (b i) (Matrix.toEuclideanLin A (b j)) := by
    intro i j
    rw [hconj, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  refine ⟨Q, hQu, p, hmono, hcard, fun i j hji => ?_, fun k hk μ hμ => ?_⟩
  · rw [hT]
    exact htri i j hji
  · -- a `2 × 2` block with a real eigenvalue would contradict the irreducibility
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot.def,
      Matrix.eval_charpoly] at hμ
    have hcard2 : Fintype.card {i // p i = k} = 2 := by
      rw [Fintype.card_subtype]
      exact hk
    obtain ⟨e, he⟩ : ∃ e : {i // p i = k} ≃ Fin 2, e = Fintype.equivFinOfCardEq hcard2 :=
      ⟨_, rfl⟩
    rw [← Matrix.det_reindex_self e, Matrix.det_fin_two] at hμ
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Matrix.toBlock_apply, hT] at hμ
    have hne : e.symm 0 ≠ e.symm 1 := e.symm.injective.ne (by decide)
    rw [Matrix.diagonal_apply_ne _ hne, Matrix.diagonal_apply_ne _ hne.symm] at hμ
    refine hirr (e.symm 0).1 (e.symm 1).1 (by rw [(e.symm 0).2, (e.symm 1).2])
      (fun h => hne (Subtype.ext h)) μ ?_
    linear_combination hμ

/-! ### Orthonormal columns for an invariant subspace -/

/-- Let $\iota$ be a finite index type, let $M \in \mathbb{R}^{\iota \times \iota}$, and let
$X \subseteq \mathbb{R}^\iota$ be an $M$-invariant subspace of dimension $d$. Then there is
$X_0 \in \mathbb{R}^{\iota \times d}$ with orthonormal columns, $X_0^T X_0 = I$, whose columns
lie in $X$, such that $M$ acts on them through the compression $X_0^T M X_0$:
$$M X_0 = X_0 (X_0^T M X_0).$$

The $d$ orthonormal columns lie in the $d$-dimensional space $X$, so they span it. -/
theorem exists_orthonormal_cols_of_invariant {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ)
    (X : Submodule ℝ (ι → ℝ)) (hinv : ∀ x ∈ X, M *ᵥ x ∈ X) {d : ℕ}
    (hd : Module.finrank ℝ X = d) :
    ∃ X₀ : Matrix ι (Fin d) ℝ, X₀ᵀ * X₀ = 1 ∧ M * X₀ = X₀ * (X₀ᵀ * M * X₀) ∧
      ∀ j, (fun r => X₀ r j) ∈ X := by
  set e : (ι → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ ι := (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm
  set XE := X.map (e : (ι → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι)
  have hdE : Module.finrank ℝ XE = d := (LinearEquiv.finrank_map_eq e X).trans hd
  set b := (stdOrthonormalBasis ℝ XE).reindex (finCongr hdE)
  set X₀ : Matrix ι (Fin d) ℝ := of fun r j => WithLp.ofLp ((b j : XE) : EuclideanSpace ℝ ι) r
    with hX₀
  have hmemE : ∀ y : ι → ℝ, y ∈ X ↔ e y ∈ XE := fun y =>
    ⟨fun h => Submodule.mem_map_of_mem h, fun h => by
      obtain ⟨z, hz, hze⟩ := Submodule.mem_map.1 h
      rw [← e.injective hze]; exact hz⟩
  have hcol : ∀ j, (fun r => X₀ r j) ∈ X := fun j => by
    rw [hmemE]
    exact (b j).2
  have horth : X₀ᵀ * X₀ = 1 := by
    ext i j
    have h := orthonormal_iff_ite.1 b.orthonormal i j
    rw [Submodule.coe_inner, PiLp.inner_apply] at h
    simp only [transpose_apply, Matrix.mul_apply, hX₀, of_apply, Matrix.one_apply]
    rw [← h]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [mul_comm]
  refine ⟨X₀, horth, ?_, hcol⟩
  · -- every vector of `X` is a combination of the columns
    have hspan : ∀ y ∈ X, ∃ c : Fin d → ℝ, y = X₀ *ᵥ c := by
      intro y hy
      refine ⟨fun i => inner ℝ (b i : EuclideanSpace ℝ ι) (e y), ?_⟩
      have h := b.sum_repr' ⟨e y, (hmemE y).1 hy⟩
      have h2 := congrArg (fun v : XE => WithLp.ofLp (v : EuclideanSpace ℝ ι)) h
      simp only [Submodule.coe_sum, Submodule.coe_smul, WithLp.ofLp_sum, WithLp.ofLp_smul,
        Submodule.coe_inner] at h2
      ext r
      have h3 := congrFun h2 r
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h3
      rw [mulVec, dotProduct]
      simp only [hX₀, of_apply]
      rw [← show WithLp.ofLp (e y) r = y r from rfl, ← h3]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    choose c hc using fun j => hspan _ (hinv _ (hcol j))
    set C : Matrix (Fin d) (Fin d) ℝ := of fun i j => c j i
    have hMX : M * X₀ = X₀ * C := by
      ext r j
      have := congrFun (hc j) r
      simp only [mulVec, dotProduct] at this
      simp only [Matrix.mul_apply, C, of_apply]
      exact this
    rw [Matrix.mul_assoc, hMX, ← Matrix.mul_assoc X₀ᵀ, horth, Matrix.one_mul]

end Matrix

/-! ### The quasi upper triangular shape -/

namespace Matrix

section QuasiTriangular

variable {n R : Type*} [Fintype n] [LinearOrder n]

/-- Let $n$ be a finite linearly ordered index type. A matrix $T \in R^{n \times n}$ is **upper
quasi-triangular** if there is a monotone block index $p \colon n \to \mathbb{N}$ whose fibres
have at most two elements each, such that $T$ is block upper triangular for $p$: $T_{ij} = 0$
whenever $p(j) < p(i)$. The fibres of $p$ are the diagonal blocks, of size $1 \times 1$ or
$2 \times 2$. This is the quasi-triangular shape of §7.4.1 of [golub2013matrix].

It is the shape of the real Schur form (`Matrix.exists_orthogonal_conj_isQuasiUpperTriangular`)
and of the real QR, QZ, periodic and Hamiltonian Schur forms of §7.4–§7.8 of [golub2013matrix].
Block upper triangularity is `Matrix.BlockTriangular p`. -/
def IsQuasiUpperTriangular [Zero R] (T : Matrix n n R) : Prop :=
  ∃ p : n → ℕ, Monotone p ∧ (∀ k, (Finset.univ.filter fun i => p i = k).card ≤ 2) ∧
    T.BlockTriangular p

omit [Fintype n] in
/-- Let $n$ be a linearly ordered index type, let $M \in R^{n \times n}$ be upper triangular, and
let $p \colon n \to \mathbb{N}$ be monotone. Then $M$ is block upper triangular for $p$:
$M_{ij} = 0$ whenever $p(j) < p(i)$.

A nonzero entry $M_{ij}$ has $i \le j$, hence $p(i) \le p(j)$. -/
theorem IsUpperTriangular.blockTriangular_of_monotone [Zero R] {M : Matrix n n R}
    (hM : M.IsUpperTriangular) {p : n → ℕ} (hp : Monotone p) : M.BlockTriangular p :=
  fun _ _ h => hM (lt_of_not_ge fun hij => absurd h (not_lt.mpr (hp hij)))

omit [Fintype n] in
/-- Let $n$ be a linearly ordered index type, let $M \in R^{n \times n}$ be lower triangular, and
let $p \colon n \to \mathbb{N}$ be monotone. Then $M$ is block lower triangular for $p$:
$M_{ij} = 0$ whenever $p(i) < p(j)$. In Lean this is `Matrix.BlockTriangular` for
`OrderDual.toDual ∘ p`, and it is the transpose of
`Matrix.IsUpperTriangular.blockTriangular_of_monotone`. -/
theorem IsLowerTriangular.blockTriangular_of_monotone [Zero R] {M : Matrix n n R}
    (hM : M.IsLowerTriangular) {p : n → ℕ} (hp : Monotone p) :
    M.BlockTriangular (OrderDual.toDual ∘ p) :=
  fun _ _ h => hM (lt_of_not_ge fun hij => absurd h (not_lt.mpr (hp hij)))

/-- An upper triangular matrix $T \in R^{n \times n}$ is upper quasi-triangular, with blocks of size
$1 \times 1$.

The block index that counts the smaller indices is strictly monotone, so its fibres have one
element each. -/
theorem IsUpperTriangular.isQuasiUpperTriangular [Zero R] {T : Matrix n n R}
    (hT : T.IsUpperTriangular) : T.IsQuasiUpperTriangular := by
  classical
  let p : n → ℕ := fun i => (Finset.univ.filter fun j => j < i).card
  have hsm : StrictMono p := by
    intro i i' h
    apply Finset.card_lt_card
    refine (Finset.ssubset_iff_of_subset fun j hj => ?_).mpr ⟨i, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact hj.trans h
    · simpa using h
    · simp
  refine ⟨p, hsm.monotone, fun k => ?_, hT.blockTriangular_of_monotone hsm.monotone⟩
  calc (Finset.univ.filter fun i => p i = k).card ≤ 1 :=
        Finset.card_le_one.mpr fun a ha b hb => hsm.injective (by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
          rw [ha, hb])
    _ ≤ 2 := by norm_num

/-- If every fibre of $p$ has at most two elements, then no three indices $a < b < c$ lie in one
fibre. -/
private theorem not_three_of_card_le_two {p : n → ℕ}
    (hcard : ∀ k, (Finset.univ.filter fun i => p i = k).card ≤ 2) {a b c : n} (hab : a < b)
    (hbc : b < c) (h1 : p b = p a) (h2 : p c = p a) : False := by
  have h3 : 2 < (Finset.univ.filter fun x => p x = p a).card :=
    Finset.two_lt_card.mpr ⟨a, by simp, b, by simp [h1], c, by simp [h2], hab.ne,
      (hab.trans hbc).ne, hbc.ne⟩
  exact absurd (hcard (p a)) (not_le.mpr h3)

/-- An upper quasi-triangular matrix $T \in R^{n \times n}$ is upper Hessenberg: $T_{ij} = 0$
whenever some index lies strictly between $j$ and $i$.

If an index $k$ lies strictly between $j$ and $i$, the three indices cannot share a block, so
$p(j) < p(i)$. -/
theorem IsQuasiUpperTriangular.isUpperHessenberg [Zero R] {T : Matrix n n R}
    (hT : T.IsQuasiUpperTriangular) : T.IsUpperHessenberg := by
  obtain ⟨p, hmono, hcard, htri⟩ := hT
  rintro i j ⟨k, hjk, hki⟩
  refine htri (lt_of_le_of_ne (hmono (hjk.trans hki).le) fun heq => ?_)
  have hk : p k = p j := le_antisymm ((hmono hki.le).trans heq.ge) (hmono hjk.le)
  exact not_three_of_card_le_two hcard hjk hki hk heq.symm

/-- Let $R$ be a semiring, not necessarily unital or associative, and let $T, M \in R^{n \times n}$
with $T$ upper quasi-triangular and $M$ upper triangular. Then $TM$ is upper quasi-triangular.

The proof keeps the block index of $T$. The matrix $M$ is block triangular for this monotone
index (`Matrix.IsUpperTriangular.blockTriangular_of_monotone`), and the block triangular
matrices for one index are closed under multiplication. The result is used for the periodic
Schur form. -/
theorem IsQuasiUpperTriangular.mul_isUpperTriangular [NonUnitalNonAssocSemiring R]
    {T M : Matrix n n R} (hT : T.IsQuasiUpperTriangular) (hM : M.IsUpperTriangular) :
    (T * M).IsQuasiUpperTriangular := by
  obtain ⟨p, hmono, hcard, htri⟩ := hT
  exact ⟨p, hmono, hcard, htri.mul (hM.blockTriangular_of_monotone hmono)⟩

/-- Let $R$ be a semiring, not necessarily unital or associative, and let $M, T \in R^{n \times n}$
with $M$ upper triangular and $T$ upper quasi-triangular. Then $MT$ is upper quasi-triangular.
This is the mirror image of `Matrix.IsQuasiUpperTriangular.mul_isUpperTriangular`. -/
theorem IsUpperTriangular.mul_isQuasiUpperTriangular [NonUnitalNonAssocSemiring R]
    {T M : Matrix n n R} (hM : M.IsUpperTriangular) (hT : T.IsQuasiUpperTriangular) :
    (M * T).IsQuasiUpperTriangular := by
  obtain ⟨p, hmono, hcard, htri⟩ := hT
  exact ⟨p, hmono, hcard, (hM.blockTriangular_of_monotone hmono).mul htri⟩

end QuasiTriangular

section Fin

variable {R : Type*} [Zero R] {N : ℕ}

/-- A matrix $T \in R^{N \times N}$, indexed by $\{0, \dots, N - 1\}$, is upper quasi-triangular if
and only if it is upper Hessenberg and has no two consecutive nonzero subdiagonal entries: for
every $i$ with $i + 2 < N$,
$$T_{i+1, i} = 0 \quad \text{or} \quad T_{i+2, i+1} = 0.$$

For the converse, the block index of an index counts the zero subdiagonal entries before it. A
nonzero subdiagonal entry keeps its two indices in one block, and two consecutive nonzero
subdiagonal entries would put three indices in one block. -/
theorem isQuasiUpperTriangular_iff_fin {T : Matrix (Fin N) (Fin N) R} :
    T.IsQuasiUpperTriangular ↔ T.IsUpperHessenberg ∧ ∀ i : ℕ, (hi : i + 2 < N) →
      T ⟨i + 1, by omega⟩ ⟨i, by omega⟩ = 0 ∨ T ⟨i + 2, hi⟩ ⟨i + 1, by omega⟩ = 0 := by
  classical
  constructor
  · intro hT
    refine ⟨hT.isUpperHessenberg, fun i hi => ?_⟩
    obtain ⟨p, hmono, hcard, htri⟩ := hT
    by_contra! h
    obtain ⟨h1, h2⟩ := h
    have e1 : p ⟨i + 1, by omega⟩ = p ⟨i, by omega⟩ :=
      le_antisymm (not_lt.mp fun hlt => h1 (htri hlt))
        (hmono (Fin.mk_le_mk.mpr (by omega)))
    have e2 : p ⟨i + 2, hi⟩ = p ⟨i + 1, by omega⟩ :=
      le_antisymm (not_lt.mp fun hlt => h2 (htri hlt))
        (hmono (Fin.mk_le_mk.mpr (by omega)))
    exact not_three_of_card_le_two hcard (b := ⟨i + 1, by omega⟩) (c := ⟨i + 2, hi⟩)
      (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega)) e1 (e2.trans e1)
  · rintro ⟨hH, hsub⟩
    let s : ℕ → Prop := fun j => ∃ h : j + 1 < N, T ⟨j + 1, h⟩ ⟨j, by omega⟩ = 0
    let P : ℕ → ℕ := fun m => ((Finset.range m).filter s).card
    have hPsucc : ∀ m, P (m + 1) = P m + if s m then 1 else 0 := fun m => by
      simp only [P, Finset.range_add_one, Finset.filter_insert]
      split_ifs
      · rw [Finset.card_insert_of_notMem (by simp)]
      · rfl
    have hPmono : Monotone P := monotone_nat_of_le_succ fun m => by rw [hPsucc]; omega
    have hns : ∀ j (h : j + 1 < N), P (j + 1) = P j → T ⟨j + 1, h⟩ ⟨j, by omega⟩ ≠ 0 :=
      fun j h hP h0 => by
        rw [hPsucc] at hP
        simp only [show s j from ⟨h, h0⟩, ↓reduceIte] at hP
        omega
    -- equal block indices are at distance at most one
    have hclose : ∀ i j : Fin N, P i = P j → (i : ℕ) ≤ (j : ℕ) + 1 := by
      intro i j hij
      by_contra! hlt
      have a1 := hPmono (show (j : ℕ) ≤ j + 1 by omega)
      have a2 := hPmono (show (j : ℕ) + 1 ≤ j + 1 + 1 by omega)
      have a3 := hPmono (show (j : ℕ) + 1 + 1 ≤ i by omega)
      have hN : (j : ℕ) + 2 < N := by omega
      rcases hsub j hN with h0 | h0
      · exact hns j (by omega) (by omega) h0
      · exact hns (j + 1) hN (by omega) h0
    refine ⟨fun i => P i, fun a b hab => hPmono hab, LinearMap.card_filter_le_two hclose,
      fun i j hji => ?_⟩
    have hji' : (j : ℕ) < i := by
      by_contra! hle
      exact absurd hji (not_lt.mpr (hPmono hle))
    rcases (show (j : ℕ) + 1 = i ∨ (j : ℕ) + 1 < i by omega) with he | hlt
    · have hs : s j := by
        by_contra hns'
        have := hPsucc j
        simp only [hns', ↓reduceIte, add_zero] at this
        rw [he] at this
        simp only at hji
        rw [this] at hji
        exact lt_irrefl _ hji
      obtain ⟨h, h0⟩ := hs
      convert h0 using 2
      exact Fin.ext he.symm
    · exact hH i j ⟨⟨j + 1, by omega⟩, Fin.lt_def.mpr (by simp),
        Fin.lt_def.mpr (by simp only; omega)⟩

end Fin

/-- The **real Schur form**: for every $A \in \mathbb{R}^{N \times N}$ there is an orthogonal
$Q \in \mathbb{R}^{N \times N}$ such that $Q^T A Q$ is upper quasi-triangular, that is, block
upper triangular with diagonal blocks of size $1 \times 1$ or $2 \times 2$. This is Theorem
7.4.1 of [golub2013matrix], and the quasi-Schur form of §1.8.3 of [saad2003iterative].

Unlike the complex Schur triangulation, this form needs no complex arithmetic. The refinement
that no $2 \times 2$ diagonal block has a real eigenvalue needs the block index in the
statement, and it is `Matrix.exists_orthogonal_conj_quasiUpperTriangular_of_irreducible_blocks`.
`Matrix.orthogonalGroup` is `Matrix.unitaryGroup` over a ring with trivial star, so the
membership means $Q^T Q = 1$. -/
theorem exists_orthogonal_conj_isQuasiUpperTriangular {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    ∃ Q ∈ Matrix.orthogonalGroup (Fin N) ℝ, (Qᵀ * A * Q).IsQuasiUpperTriangular := by
  obtain ⟨Q, hQ, p, hmono, hcard, htri, -⟩ :=
    exists_orthogonal_conj_quasiUpperTriangular_of_irreducible_blocks A
  exact ⟨Q, hQ, p, hmono, hcard, htri⟩

end Matrix

/-- The **real Schur form**, operator form: let $E$ be a finite-dimensional real inner product space
of dimension $n$ and let $A \colon E \to E$ be linear. Then $E$ has an orthonormal basis in
which the matrix of $A$ is upper quasi-triangular.

Over $\mathbb{C}$ all blocks could be taken of size $1 \times 1$, which is Schur's theorem. Over
$\mathbb{R}$ an operator need not have an eigenvector, and a pair of complex conjugate
eigenvalues needs a $2 \times 2$ block. -/
theorem LinearMap.exists_orthonormalBasis_isQuasiUpperTriangular {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
    (hn : finrank ℝ E = n) (A : E →ₗ[ℝ] E) :
    ∃ b : OrthonormalBasis (Fin n) ℝ E,
      (LinearMap.toMatrix b.toBasis b.toBasis A).IsQuasiUpperTriangular := by
  obtain ⟨b, p, hmono, hcard, htri, -⟩ :=
    LinearMap.exists_orthonormalBasis_quasiUpperTriangular_of_irreducible_blocks hn A
  refine ⟨b, p, hmono, hcard, fun i j hji => ?_⟩
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  exact htri i j hji

namespace Matrix

/-! ### The spectrum of a special orthogonal matrix -/

section SpecialOrthogonal

open Complex Polynomial

/-- The multiset $\{e^{i\theta}, e^{-i\theta}\}$ of two conjugate points of the unit circle. -/
private noncomputable def circlePair (θ : ℝ) : Multiset ℂ := {exp (θ * I), exp (-θ * I)}

open scoped Matrix.Norms.L2Operator in
/-- Let $H \in \mathbb{R}^{N \times N}$ be orthogonal. Then every root $z$ of the characteristic
polynomial of $H$, taken as a complex matrix, has $|z| = 1$.

The complex matrix $H$ is a unitary element of the $C^*$-algebra of complex matrices, and the
spectrum of a unitary element lies on the unit circle (`spectrum.norm_eq_one_of_unitary`). -/
theorem norm_eq_one_of_mem_orthogonalGroup_of_mem_roots_charpoly {N : ℕ}
    {H : Matrix (Fin N) (Fin N) ℝ} (hH : H ∈ orthogonalGroup (Fin N) ℝ) {z : ℂ}
    (hz : z ∈ (H.map (algebraMap ℝ ℂ)).charpoly.roots) : ‖z‖ = 1 := by
  set A := H.map (algebraMap ℝ ℂ) with hA
  have hAA : star A * A = 1 := by
    rw [hA, star_eq_conjTranspose, ← conjTranspose_map _ (fun _ => by simp), ← Matrix.map_mul,
      conjTranspose_eq_transpose_of_trivial, (mem_orthogonalGroup_iff' (Fin N) ℝ).1 hH,
      Matrix.map_one _ (map_zero _) (map_one _)]
  refine spectrum.norm_eq_one_of_unitary (mem_unitaryGroup_iff'.2 hAA) ?_
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  exact (mem_roots A.charpoly_monic.ne_zero).1 hz

/-- A multiset of complex numbers of modulus one that is closed under conjugation, has even size and
has product $1$ is a union of conjugate pairs $\{e^{i\theta}, e^{-i\theta}\}$. -/
private theorem exists_circlePairs (s : Multiset ℂ) (hconj : s.map (starRingEnd ℂ) = s)
    (hnorm : ∀ z ∈ s, ‖z‖ = 1) (hprod : s.prod = 1) (hcard : Even (Multiset.card s)) :
    ∃ T : Multiset ℝ, 2 * Multiset.card T = Multiset.card s ∧ s = T.bind circlePair := by
  induction hk : Multiset.card s using Nat.strong_induction_on generalizing s with
  | _ k ih =>
  by_cases hreal : ∃ z ∈ s, z.im ≠ 0
  · obtain ⟨z, hzs, hzi⟩ := hreal
    have hcz : starRingEnd ℂ z ≠ z := fun h => hzi (Complex.conj_eq_iff_im.1 h)
    have hczs : starRingEnd ℂ z ∈ s.erase z := by
      rw [Multiset.mem_erase_of_ne hcz, ← hconj]
      exact Multiset.mem_map_of_mem _ hzs
    set s' := (s.erase z).erase (starRingEnd ℂ z) with hs'
    have hs : s = z ::ₘ starRingEnd ℂ z ::ₘ s' := by
      rw [hs', Multiset.cons_erase hczs, Multiset.cons_erase hzs]
    have hzz : z * starRingEnd ℂ z = 1 := by
      rw [Complex.mul_conj', hnorm z hzs]
      simp
    have hconj' : s'.map (starRingEnd ℂ) = s' := by
      have := hconj
      rw [hs, Multiset.map_cons, Multiset.map_cons, Complex.conj_conj, Multiset.cons_swap] at this
      exact (Multiset.cons_inj_right _).1 ((Multiset.cons_inj_right _).1 this)
    have hcard' : Multiset.card s' + 2 = k := by rw [← hk, hs]; simp
    obtain ⟨T, hT, hTs⟩ := ih (Multiset.card s') (by omega) s' hconj'
      (fun w hw => hnorm w (by rw [hs]; simp [hw]))
      (by rw [hs, Multiset.prod_cons, Multiset.prod_cons, ← mul_assoc, hzz, one_mul] at hprod
          exact hprod)
      (by rw [hk] at hcard; obtain ⟨t, ht⟩ := hcard; exact ⟨t - 1, by omega⟩) rfl
    refine ⟨arg z ::ₘ T, by simp; omega, ?_⟩
    have h1 : exp (arg z * I) = z := by
      simpa [hnorm z hzs] using norm_mul_exp_arg_mul_I z
    have h2 : exp (-arg z * I) = starRingEnd ℂ z := by
      conv_rhs => rw [← h1]
      rw [← exp_conj, map_mul, conj_ofReal, conj_I, mul_neg, neg_mul]
    rw [Multiset.cons_bind, ← hTs, circlePair, h1, h2, hs, Multiset.insert_eq_cons,
      Multiset.cons_add, Multiset.singleton_add]
  · push Not at hreal
    have hpm : ∀ z ∈ s, z = 1 ∨ z = -1 := fun z hz => by
      have hzr : z = (z.re : ℂ) := Complex.ext rfl (by simp [hreal z hz])
      have hn := hnorm z hz
      rw [hzr, Complex.norm_real, Real.norm_eq_abs] at hn
      rcases abs_eq (zero_le_one) |>.1 hn with h | h
      · left; rw [hzr, h]; simp
      · right; rw [hzr, h]; simp
    set a := Multiset.card (s.filter (· = 1)) with ha
    set b := Multiset.card (s.filter (fun z => ¬ z = 1)) with hb
    have hfa : s.filter (· = 1) = Multiset.replicate a 1 :=
      Multiset.eq_replicate.2 ⟨rfl, fun z hz => (Multiset.mem_filter.1 hz).2⟩
    have hfb : s.filter (fun z => ¬ z = 1) = Multiset.replicate b (-1) :=
      Multiset.eq_replicate.2 ⟨rfl, fun z hz => by
        obtain ⟨hzs, hz1⟩ := Multiset.mem_filter.1 hz
        exact (hpm z hzs).resolve_left hz1⟩
    have hsab : s = Multiset.replicate a 1 + Multiset.replicate b (-1) := by
      rw [← hfa, ← hfb, Multiset.filter_add_not]
    have hbeven : Even b := by
      rw [hsab, Multiset.prod_add, Multiset.prod_replicate, Multiset.prod_replicate, one_pow,
        one_mul] at hprod
      exact (neg_one_pow_eq_one_iff_even (by norm_num)).1 hprod
    have haeven : Even a := by
      rw [hsab, Multiset.card_add, Multiset.card_replicate, Multiset.card_replicate] at hcard
      exact (Nat.even_add.1 hcard).2 hbeven
    obtain ⟨a', ha'⟩ := haeven
    obtain ⟨b', hb'⟩ := hbeven
    refine ⟨Multiset.replicate a' 0 + Multiset.replicate b' Real.pi, ?_, ?_⟩
    · rw [← hk, hsab]
      simp
      omega
    · have hc0 : circlePair 0 = Multiset.replicate 2 1 := by
        simp [circlePair, Multiset.replicate_succ]
      have hcpi : circlePair Real.pi = Multiset.replicate 2 (-1) := by
        simp [circlePair, Multiset.replicate_succ, neg_mul, exp_neg_pi_mul_I, exp_pi_mul_I]
      have hrb : ∀ (t : ℕ) (x : ℝ) (w : ℂ), circlePair x = Multiset.replicate 2 w →
          (Multiset.replicate t x).bind circlePair = Multiset.replicate (t + t) w := by
        intro t x w hx
        induction t with
        | zero => simp
        | succ t ih =>
          rw [Multiset.replicate_succ, Multiset.cons_bind, ih, hx, ← Multiset.replicate_add]
          congr 1
          omega
      rw [Multiset.add_bind, hrb a' 0 1 hc0, hrb b' Real.pi (-1) hcpi, hsab, ← ha', ← hb']

/-- Let $H \in \mathbb{R}^{2m \times 2m}$ be orthogonal with $\det H = 1$. Then there are
$\theta_0, \dots, \theta_{m-1} \in \mathbb{R}$ such that the characteristic polynomial of $H$,
taken as a complex matrix, is
$$\det(XI - H) = \prod_{k=0}^{m-1} (X - e^{i \theta_k})(X - e^{-i \theta_k}).$$
So the eigenvalues of $H$ are $m$ conjugate pairs $e^{\pm i \theta_k}$ on the unit circle, and
the real eigenvalues $\pm 1$ occur in pairs. This is (12.2.19) of [golub2013matrix], which
states it for orthogonal upper Hessenberg matrices; it holds for all special orthogonal matrices
of even order.

The roots of the characteristic polynomial have modulus one
(`Matrix.norm_eq_one_of_mem_orthogonalGroup_of_mem_roots_charpoly`) and come in conjugate pairs,
because the polynomial is real. The eigenvalue $-1$ has even multiplicity because the product of
the roots is $\det H = 1$, and then so has $1$, because the order is even. -/
theorem exists_charpoly_eq_prod_of_mem_specialOrthogonalGroup {m : ℕ}
    {H : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ} (hH : H ∈ specialOrthogonalGroup (Fin (2 * m)) ℝ) :
    ∃ θ : Fin m → ℝ, (H.map (algebraMap ℝ ℂ)).charpoly =
      ∏ k, (X - C (exp (θ k * I))) * (X - C (exp (-θ k * I))) := by
  obtain ⟨hO, hdet⟩ := mem_specialOrthogonalGroup_iff.1 hH
  set A := H.map (algebraMap ℝ ℂ) with hA
  have hmap : A.charpoly = H.charpoly.map (algebraMap ℝ ℂ) := charpoly_map H _
  have hsplit : Multiset.card A.charpoly.roots = A.charpoly.natDegree :=
    splits_iff_card_roots.1 (IsAlgClosed.splits _)
  have hconj : A.charpoly.roots.map (starRingEnd ℂ) = A.charpoly.roots := by
    rw [hmap]
    exact roots_map_algebraMap_conj _
  have hprod : A.charpoly.roots.prod = 1 := by
    rw [← det_eq_prod_roots_charpoly, hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet,
      map_one]
  have hcard : Multiset.card A.charpoly.roots = 2 * m := by
    rw [hsplit, charpoly_natDegree_eq_dim, Fintype.card_fin]
  obtain ⟨T, hT, hTs⟩ := exists_circlePairs A.charpoly.roots hconj
    (fun z hz => norm_eq_one_of_mem_orthogonalGroup_of_mem_roots_charpoly hO hz) hprod ⟨m, by omega⟩
  have hTm : Multiset.card T = m := by omega
  set l := T.toList with hl
  have hlen : l.length = m := by rw [hl, Multiset.length_toList, hTm]
  refine ⟨fun k => l[(k : ℕ)]'(by rw [hlen]; exact k.2), ?_⟩
  rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq A.charpoly_monic hsplit, hTs,
    Multiset.map_bind, Multiset.prod_bind, ← Multiset.coe_toList T, ← hl, Multiset.map_coe,
    Multiset.prod_coe, ← List.ofFn_getElem_eq_map, List.prod_ofFn]
  refine Fintype.prod_equiv (finCongr hlen) _ _ fun k => ?_
  simp [circlePair]

end SpecialOrthogonal

end Matrix
