import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.LinearCombination
import Numlib.LinearAlgebra.CyclicDecomposition.InvariantFactors
import Numlib.LinearAlgebra.Matrix.Jordan
import Numlib.LinearAlgebra.Matrix.UnreducedHessenberg
import Numlib.LinearAlgebra.MinpolyOn

/-!
# Liesen and Strakoš, Section 4.2: Cyclic subspaces and the Jordan canonical form

Section 4.2 of [liesen2013krylov] introduces minimal polynomials of vectors and invariant subspaces.
Cyclic subspaces and grades come from `Numlib.Krylov.Subspace`, and the existence of a Jordan
basis comes from `Numlib.LinearAlgebra.Matrix.Jordan`.

## Main definitions

* Definition 4.2.1, `LiesenStrakos.vectorMinimalPolynomial`: the monic annihilator of one vector
  of least degree.
* Definition 4.2.1, `LiesenStrakos.vectorGrade`: the degree of that polynomial.
* Definition 4.2.5, `LiesenStrakos.subspaceMinimalPolynomial`: the monic annihilator of an
  invariant subspace of least degree.
* Definition 4.2.5, `LiesenStrakos.operatorMinimalPolynomial`: the monic annihilator of the
  entire space of least degree.
* Definition 4.2.5, `LiesenStrakos.operatorMinimalDegree`: the degree of the operator's
  minimal polynomial.

## Main results

* Theorem 4.2.2, `LiesenStrakos.theorem_4_2_2`: existence and uniqueness in polynomial division.
* Lemma 4.2.3, `LiesenStrakos.lemma_4_2_3`: the minimal polynomial of a vector divides any
  polynomial that annihilates it.
* Lemma 4.2.4, `LiesenStrakos.lemma_4_2_4`: the minimal polynomial of an invariant subspace
  is monic and divides every annihilator of that subspace.
* Lemma 4.2.6, `LiesenStrakos.lemma_4_2_6`: vector grades and the operator minimal degree are
  invariant under shifts of the operator by a scalar.
* Lemma 4.2.7, `LiesenStrakos.lemma_4_2_7`: the generator and its cyclic subspace have
  the same minimal polynomial.
* Theorem 4.2.8, `LiesenStrakos.theorem_4_2_8`: the space decomposes into cyclic subspaces
  with primary minimal polynomials.
* Lemma 4.2.9, `LiesenStrakos.lemma_4_2_9`: adding generators with coprime minimal polynomials
  adds grades, multiplies the minimal polynomials, and gives the direct sum of the cyclic spaces.
* Corollary 4.2.10, `LiesenStrakos.corollary_4_2_10`: the cyclic generators can be ordered by
  reverse divisibility of their minimal polynomials.
* Lemma 4.2.11, `LiesenStrakos.lemma_4_2_11`: a basis can be chosen entirely from full-grade
  vectors.
* Remark 4.2.12, `LiesenStrakos.remark_4_2_12`: the determinant formula for a full-grade vector.
* Theorem 4.2.13, `LiesenStrakos.theorem_4_2_13`: the Jordan blocks can be ordered by
  decreasing size.

## Deviations from the source

* **Definitions 4.2.1 and 4.2.5** (generalization). Grade and operator minimal-polynomial
  definitions allow arbitrary dimensions and fields. The invariant-subspace definition also
  includes the zero subspace.
* **Lemma 4.2.9** (generalization). Either summand may be zero because its vector minimal
  polynomial is $1$ and its cyclic space is zero.
* **Corollary 4.2.10** (generalization). The zero space admits the empty cyclic decomposition. See
  `LiesenStrakos.corollary_4_2_10`.
-/

open Polynomial

namespace LiesenStrakos

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The minimal polynomial $p_v$ of a vector $v$ with respect to a complex endomorphism $A$ is the
monic polynomial of least degree such that $p_v(A)v=0$. In particular $p_0=1$.
This is Definition 4.2.1 of [liesen2013krylov]. -/
noncomputable abbrev vectorMinimalPolynomial (A : Module.End ℂ V) (v : V) : ℂ[X] :=
  Krylov.minpolyVec A v

/-- The grade $d(A,v)$ of $v$ with respect to $A$ is the degree of its minimal polynomial.
Equivalently it is the dimension of the span of $v,Av,A^2v,\ldots$. This is Definition 4.2.1
of [liesen2013krylov].

**Generalization.** The ambient vector space and scalar field are arbitrary. An infinite-
dimensional cyclic span gives grade zero under the finite-rank convention. -/
noncomputable abbrev vectorGrade {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (A : Module.End K W) (v : W) : ℕ := Krylov.grade A v

/-- If $g\ne0$, then there is a unique pair of complex polynomials $(q,r)$ such that
$f=gq+r$ and $\deg r<\deg g$. This is Theorem 4.2.2 of [liesen2013krylov]. -/
theorem theorem_4_2_2 (f g : ℂ[X]) (hg : g ≠ 0) :
    ∃! qr : ℂ[X] × ℂ[X], f = g * qr.1 + qr.2 ∧ qr.2.degree < g.degree := by
  refine ⟨⟨f / g, f % g⟩, ⟨(EuclideanDomain.div_add_mod f g).symm, degree_mod_lt f hg⟩, ?_⟩
  rintro ⟨q, r⟩ ⟨he, hr⟩
  dsimp only at he hr
  have hrem : f % g = r := by
    rw [he, Polynomial.add_mod,
      (EuclideanDomain.mod_eq_zero.mpr (dvd_mul_right g q)),
      (Polynomial.mod_eq_self_iff hg).2 hr, zero_add]
  have hquot : g * (f / g) = g * q := by
    apply add_right_cancel (b := r)
    rw [← hrem, EuclideanDomain.div_add_mod, hrem, ← he]
  exact Prod.ext ((mul_left_cancel₀ hg hquot).symm) hrem.symm

omit [FiniteDimensional ℂ V] in
/-- If $p(A)v=0$ then $p_v$ divides $p$. This is Lemma 4.2.3 of [liesen2013krylov]. -/
theorem lemma_4_2_3 (A : Module.End ℂ V) (v : V) (p : ℂ[X])
    (hp : aeval A p v = 0) : vectorMinimalPolynomial A v ∣ p :=
  (Krylov.minpolyVec_dvd_iff A v).2 hp

/-- The minimal polynomial of $A$ on an invariant subspace $W$ is the minimal polynomial of the
endomorphism induced by $A$ on $W$. This is Definition 4.2.5 of [liesen2013krylov].

**Generalization.** The definition includes the zero invariant subspace, with minimal
polynomial $1$. -/
noncomputable abbrev subspaceMinimalPolynomial (A : Module.End ℂ V) (W : Submodule ℂ V)
    (hW : Set.MapsTo A W W) : ℂ[X] := A.minpolyOn W hW

/-- The minimal polynomial of $A$ on the full space is its monic annihilator of least degree.
This is Definition 4.2.5 of [liesen2013krylov].

**Generalization.** Any scalar field and ambient dimension are allowed. A nonintegral operator
has minimal polynomial zero. -/
noncomputable abbrev operatorMinimalPolynomial {K W : Type*} [Field K] [AddCommGroup W]
    [Module K W] (A : Module.End K W) : K[X] := minpoly K A

/-- The degree $d_{\min}(A)$ of the minimal polynomial of the operator $A$.
This is Definition 4.2.5 of [liesen2013krylov].

**Generalization.** This natural degree is zero for a nonintegral operator, whose minimal
polynomial is zero. -/
noncomputable abbrev operatorMinimalDegree {K W : Type*} [Field K] [AddCommGroup W]
    [Module K W] (A : Module.End K W) : ℕ :=
  (operatorMinimalPolynomial A).natDegree

/-- The invariant-subspace minimal polynomial is monic, divides exactly the polynomials that
annihilate the subspace, and is divisible by each vector minimal polynomial in the subspace.
For an annihilating monic polynomial, equality of degree forces equality with the minimal
polynomial. This is Lemma 4.2.4 of [liesen2013krylov].

**Generalization.** The characterization also includes the zero invariant subspace. -/
theorem lemma_4_2_4 (A : Module.End ℂ V) (W : Submodule ℂ V) (hW : Set.MapsTo A W W) :
    let μ := subspaceMinimalPolynomial A W hW
    μ.Monic ∧ (∀ p : ℂ[X], μ ∣ p ↔ ∀ v ∈ W, aeval A p v = 0) ∧
      (∀ v ∈ W, vectorMinimalPolynomial A v ∣ μ) ∧
      (∀ p : ℂ[X], p.Monic → (∀ v ∈ W, aeval A p v = 0) →
        μ.natDegree ≤ p.natDegree ∧ (p.natDegree = μ.natDegree → p = μ)) := by
  dsimp only
  let μ := subspaceMinimalPolynomial A W hW
  have hm : μ.Monic := minpoly.monic (IsIntegral.of_finite ℂ (A.restrict hW))
  have hd (p : ℂ[X]) : μ ∣ p ↔ ∀ v ∈ W, aeval A p v = 0 :=
    LinearMap.minpolyOn_dvd_iff A hW
  refine ⟨hm, hd, fun v hv => lemma_4_2_3 A v μ ((hd μ).1 dvd_rfl v hv), ?_⟩
  intro p hp hv
  have hdvd := (hd p).2 hv
  refine ⟨natDegree_le_of_dvd hdvd hp.ne_zero, fun he => ?_⟩
  exact (eq_of_dvd_of_natDegree_le_of_leadingCoeff hdvd (le_of_eq he)
    (hm.leadingCoeff.trans hp.leadingCoeff.symm)).symm

private theorem operatorMinimalDegree_sub_le (A : Module.End ℂ V) (c : ℂ) :
    operatorMinimalDegree (A - algebraMap ℂ (Module.End ℂ V) c) ≤ operatorMinimalDegree A := by
  let T := A - algebraMap ℂ (Module.End ℂ V) c
  let p := operatorMinimalPolynomial A
  have h : aeval T (p.comp (X + C c)) = 0 := by
    rw [aeval_comp]
    simp [T, p]
  have hmonic : (p.comp (X + C c)).Monic :=
    (minpoly.monic (IsIntegral.of_finite ℂ A)).comp (monic_X_add_C c)
      (by rw [natDegree_X_add_C]; decide)
  have hb := natDegree_le_of_dvd (minpoly.dvd ℂ T h) hmonic.ne_zero
  simpa [T, p, operatorMinimalDegree, natDegree_comp, natDegree_X_add_C] using hb

/-- The vector grade and the operator's minimal-polynomial degree are invariant under subtraction
of a scalar multiple of the identity. This is Lemma 4.2.6 of [liesen2013krylov]. -/
theorem lemma_4_2_6 (A : Module.End ℂ V) (c : ℂ) :
    (∀ v : V, vectorGrade A v = vectorGrade (A - algebraMap ℂ (Module.End ℂ V) c) v) ∧
      operatorMinimalDegree A = operatorMinimalDegree (A - algebraMap ℂ (Module.End ℂ V) c) := by
  refine ⟨fun v => ?_, le_antisymm ?_ (operatorMinimalDegree_sub_le A c)⟩
  · simpa [sub_eq_add_neg] using (Krylov.grade_add_algebraMap A v (-c)).symm
  · simpa [sub_eq_add_neg, add_assoc] using
      operatorMinimalDegree_sub_le (A - algebraMap ℂ (Module.End ℂ V) c) (-c)

/-- A vector and its cyclic subspace have the same minimal polynomial. Every vector in its
cyclic subspace has a minimal polynomial dividing that polynomial. This is Lemma 4.2.7 of
[liesen2013krylov]. -/
theorem lemma_4_2_7 (A : Module.End ℂ V) (v : V) :
    let hW := (Module.End.mem_invtSubmodule_iff_mapsTo A).1
      (Krylov.fullSubspace_mem_invtSubmodule A v)
    vectorMinimalPolynomial A v = subspaceMinimalPolynomial A (Krylov.fullSubspace A v) hW ∧
      ∀ w ∈ Krylov.fullSubspace A v, vectorMinimalPolynomial A w ∣ vectorMinimalPolynomial A v := by
  let hW := (Module.End.mem_invtSubmodule_iff_mapsTo A).1
    (Krylov.fullSubspace_mem_invtSubmodule A v)
  have he := LinearMap.minpolyOn_fullKrylovSubspace A v hW
  refine ⟨he.symm, fun w hw => ?_⟩
  change Krylov.minpolyVec A w ∣ Krylov.minpolyVec A v
  rw [← he]
  exact (lemma_4_2_4 A _ hW).2.2.1 w hw

/-- If the vector minimal polynomials of $v$ and $w$ are coprime, then the minimal
polynomial of $v+w$ is their product and its grade is the sum of their grades. Its
cyclic subspace is the internal direct sum of the two cyclic subspaces.
This is Lemma 4.2.9 of [liesen2013krylov].

**Generalization.** The source assumes both vectors are nonzero. The monic annihilator
of the zero vector is $1$, and the formula remains valid with a zero summand. -/
theorem lemma_4_2_9 (A : Module.End ℂ V) (v w : V)
    (hcop : IsCoprime (vectorMinimalPolynomial A v) (vectorMinimalPolynomial A w)) :
    vectorMinimalPolynomial A (v + w) =
        vectorMinimalPolynomial A v * vectorMinimalPolynomial A w ∧
      vectorGrade A (v + w) = vectorGrade A v + vectorGrade A w ∧
      Krylov.fullSubspace A (v + w) = Krylov.fullSubspace A v ⊔ Krylov.fullSubspace A w ∧
      Disjoint (Krylov.fullSubspace A v) (Krylov.fullSubspace A w) :=
  Krylov.minpolyVec_fullSubspace_add_of_isCoprime A v w hcop

/-- The space is an internal direct sum of cyclic spaces generated by
$w_1,\ldots,w_m$ of positive, nonincreasing grades. For $i\le j$ the minimal
polynomial of $w_j$ divides that of $w_i$, and the first polynomial equals the
operator's minimal polynomial when $m>0$. This is Corollary 4.2.10 of [liesen2013krylov].

**Generalization.** The source refers to the first generator. The zero space admits the
empty decomposition, for which there is no first vector. -/
theorem corollary_4_2_10 (A : Module.End ℂ V) :
    ∃ (m : ℕ) (w : Fin m → V),
      Antitone (fun j => vectorGrade A (w j)) ∧
      (∀ j, 0 < vectorGrade A (w j)) ∧
      DirectSum.IsInternal (fun j => Krylov.fullSubspace A (w j)) ∧
      (∀ h : 0 < m, vectorMinimalPolynomial A (w ⟨0, h⟩) = operatorMinimalPolynomial A) ∧
      (∀ i j, i ≤ j → vectorMinimalPolynomial A (w j) ∣ vectorMinimalPolynomial A (w i)) := by
  obtain ⟨m, w, hsum, hpos, hdvd, hfirst⟩ := A.exists_isInternal_invariantFactorKrylov
  refine ⟨m, w, ?_, hpos, hsum, hfirst, hdvd⟩
  intro i j hij
  change Krylov.grade A (w j) ≤ Krylov.grade A (w i)
  rw [← Krylov.natDegree_minpolyVec, ← Krylov.natDegree_minpolyVec]
  exact natDegree_le_of_dvd (hdvd i j hij) (Krylov.minpolyVec_ne_zero A (w i))

/-- Every finite-dimensional complex endomorphism has a basis consisting of vectors
whose grades equal its minimal-polynomial degree. This is Lemma 4.2.11 of
[liesen2013krylov]. -/
theorem lemma_4_2_11 (A : Module.End ℂ V) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ V),
      ∀ i, vectorGrade A (b i) = operatorMinimalDegree A :=
  A.exists_basis_fullGrade

/-- A finite-dimensional complex endomorphism has a Jordan basis. Its positive block sizes can
be taken in nonincreasing order. This is Theorem 4.2.13 of [liesen2013krylov]. -/
theorem theorem_4_2_13 (A : Module.End ℂ V) :
    ∃ (n : ℕ) (sizes : Fin n → ℕ) (eigenvalues : Fin n → ℂ)
      (b : Module.Basis ((i : Fin n) × Fin (sizes i)) ℂ V),
      Antitone sizes ∧ (∀ i, 0 < sizes i) ∧
        LinearMap.toMatrix b b A = Matrix.jordanForm sizes eigenvalues := by
  classical
  obtain ⟨n, sizes, eigenvalues, b, hpos, hmat⟩ := A.exists_basis_toMatrix_eq_jordanForm
  let σ := Tuple.sortDesc sizes
  let τ := Equiv.sigmaCongrLeft (β := fun i => Fin (sizes i)) σ
  refine ⟨n, sizes ∘ σ, eigenvalues ∘ σ, b.reindex τ.symm,
    Tuple.antitone_sortDesc sizes, fun i => hpos (σ i), ?_⟩
  rw [LinearMap.toMatrix_reindex, Equiv.symm_symm, hmat]
  exact Matrix.blockDiagonal'_submatrix_sigmaCongrLeft _ σ

/-- The space is an internal direct sum of cyclic spaces of positive, nonincreasing grades
$d_1,\ldots,d_m$, with each generator's minimal polynomial a power $(X-\lambda_i)^{d_i}$
of one linear polynomial. This is Theorem 4.2.8 of [liesen2013krylov]. -/
theorem theorem_4_2_8 (A : Module.End ℂ V) :
    ∃ (m : ℕ) (v : Fin m → V) (μ : Fin m → ℂ),
      Antitone (fun i => vectorGrade A (v i)) ∧
      (∀ i, 0 < vectorGrade A (v i)) ∧
      (∀ i, vectorMinimalPolynomial A (v i) = (X - C (μ i)) ^ vectorGrade A (v i)) ∧
      DirectSum.IsInternal (fun i => Krylov.fullSubspace A (v i)) := by
  obtain ⟨m, e, μ, b, horder, hpos, hmat⟩ := theorem_4_2_13 A
  obtain ⟨v, hv, hpol, hsum⟩ := A.exists_isInternal_primaryKrylov e μ b hpos hmat
  have hgrade : (fun i => vectorGrade A (v i)) = e := funext hv
  refine ⟨m, v, μ, ?_, ?_, ?_, hsum⟩
  · rwa [hgrade]
  · intro i
    change 0 < Krylov.grade A (v i)
    rw [hv i]
    exact hpos i
  · intro i
    change Krylov.minpolyVec A (v i) = (X - C (μ i)) ^ Krylov.grade A (v i)
    rw [hv i]
    exact hpol i

open Matrix in
/-- **Remark 4.2.12** of [liesen2013krylov]. If a vector $v$ has grade $N$ for an
$N$-by-$N$ matrix $A$, then its vector minimal polynomial equals the characteristic
polynomial of $A$. Its value at $z$ is the determinant of the bordered matrix
$$\begin{bmatrix}v&Av&\cdots&A^{N-1}v&A^N v\\
1&z&\cdots&z^{N-1}&z^N\end{bmatrix}$$
divided by the determinant of the square Krylov matrix. -/
theorem remark_4_2_12 {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ)
    (hv : Krylov.grade A.toLin' v = N) (z : ℂ) :
    let K := A.krylovMatrix v N
    let p := Krylov.minpolyVec A.toLin' v
    let W : Matrix (Fin N) Unit ℂ := Matrix.of fun i _ => (A ^ N *ᵥ v) i
    let R : Matrix Unit (Fin N) ℂ := Matrix.of fun _ j => z ^ (j : ℕ)
    let D : Matrix Unit Unit ℂ := Matrix.of fun _ _ => z ^ N
    p = A.charpoly ∧ p.eval z = (Matrix.fromBlocks K W R D).det / K.det := by
  intro K p W R D
  let T := A.toLin'
  have hdeg : p.natDegree = N := (Krylov.natDegree_minpolyVec T v).trans hv
  have hmon : p.Monic := Krylov.minpolyVec_monic T v (Krylov.minpolyVec_ne_zero T v)
  have hcoeff : p.coeff N = 1 := hdeg ▸ hmon.coeff_natDegree
  have hchar : T.charpoly = p := by
    apply eq_of_monic_of_dvd_of_natDegree_le hmon (LinearMap.charpoly_monic T)
    · exact (Krylov.minpolyVec_dvd_iff T v).2 (by rw [LinearMap.aeval_self_charpoly]; rfl)
    · rw [LinearMap.charpoly_natDegree, hdeg, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hAchar : T.charpoly = A.charpoly := by
    rw [← LinearMap.charpoly_toMatrix T (Pi.basisFun ℂ (Fin N))]
    change (LinearMap.toMatrix' (Matrix.toLin' A)).charpoly = _
    rw [LinearMap.toMatrix'_toLin']
  refine ⟨hchar.symm.trans hAchar, ?_⟩
  have hLI : LinearIndependent ℂ K.col := by
    have h := Krylov.linearIndependent_of_le_grade T v hv.ge
    have heq : K.col = fun j : Fin N => (T ^ (j : ℕ)) v := by
      funext j
      rw [show K = A.krylovMatrix v N from rfl, Matrix.col_krylovMatrix]
      change _ = (A.toLin' ^ (j : ℕ)) v
      rw [← Matrix.toLin'_pow]
      rfl
    exact heq ▸ h
  have hK : K.det ≠ 0 :=
    (isUnit_iff_ne_zero.1 <| (Matrix.isUnit_iff_isUnit_det K).1
      (Matrix.linearIndependent_col_iff_isUnit.1 hLI))
  have hsum : (∑ j : Fin N, p.coeff j • (A ^ (j : ℕ) *ᵥ v)) + A ^ N *ᵥ v = 0 := by
    have hzero : aeval T p v = 0 := Krylov.aeval_minpolyVec T v
    rw [aeval_eq_sum_range, hdeg, Finset.sum_range_succ, hcoeff, one_smul,
      LinearMap.add_apply, LinearMap.sum_apply, ← Fin.sum_univ_eq_sum_range] at hzero
    simpa only [T, LinearMap.smul_apply, ← Matrix.toLin'_pow, Matrix.toLin'_apply] using hzero
  let C : Matrix (Fin N) Unit ℂ := Matrix.of fun j _ => -p.coeff j
  have hKC : K * C = W := by
    ext i u
    have hi := congrFun hsum i
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    simp only [C, W, K, Matrix.mul_apply, Matrix.of_apply, Matrix.krylovMatrix_apply,
      mul_neg, Finset.sum_neg_distrib]
    have heq : ∑ j : Fin N, (A ^ (j : ℕ) *ᵥ v) i * p.coeff j =
        ∑ j : Fin N, p.coeff j * (A ^ (j : ℕ) *ᵥ v) i :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [heq]
    linear_combination -hi
  have hsmall : (D - R * C).det = p.eval z := by
    rw [Matrix.det_unique, eval_eq_sum_range, hdeg, Finset.sum_range_succ, hcoeff, one_mul,
      ← Fin.sum_univ_eq_sum_range]
    simp only [D, R, C, Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply, mul_neg,
      Finset.sum_neg_distrib, sub_neg_eq_add]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hfactor : Matrix.fromBlocks K W R D =
      Matrix.fromBlocks K (0 : Matrix (Fin N) Unit ℂ) R (D - R * C) *
        Matrix.fromBlocks 1 C 0 1 := by
    rw [Matrix.fromBlocks_multiply]
    simp [hKC, add_comm]
  rw [hfactor, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, Matrix.det_one, mul_one, mul_one, hsmall, mul_comm K.det,
    mul_div_cancel_right₀ _ hK]

end LiesenStrakos
