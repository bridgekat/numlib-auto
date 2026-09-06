/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Schur`, beside the complex triangulation.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The real Schur form

A real square matrix is orthogonally similar to a *quasi upper triangular* matrix: block upper
triangular with diagonal blocks of size `1 × 1` or `2 × 2`, the `2 × 2` blocks carrying the pairs
of complex conjugate eigenvalues. This is the **real Schur form**, or *quasi-Schur form*, of
[saad2003iterative] §1.8.3.

The complex triangulation does not specialize: over `ℝ` an operator need not have an eigenvector,
so the induction of Schur's theorem has to peel off an invariant subspace of dimension one *or
two*, and that is exactly where the `2 × 2` blocks come from.

## Main results

* `LinearMap.exists_invariant_finrank_le_two`: a real operator on a nonzero finite-dimensional
  space has an invariant subspace of dimension at most two, and nonzero.
* `LinearMap.exists_orthonormalBasis_quasiUpperTriangular`: the operator form. There is an
  orthonormal basis and a monotone block index `p : Fin n → ℕ` whose fibres have at most two
  elements, with `⟪b i, A (b j)⟫ = 0` whenever `p j < p i`.
* `Matrix.exists_orthogonal_conj_quasiUpperTriangular`: the matrix form, `Qᵀ A Q` quasi upper
  triangular for an orthogonal `Q`.

## Implementation notes

The invariant subspace comes from a factor of the characteristic polynomial. Cayley–Hamilton
annihilates every vector, so some *irreducible* real factor `q` has `q(A) w = 0` for a nonzero
`w`; an irreducible real polynomial has degree one or two, so `span {w, A w}` is `A`-invariant of
dimension at most two. No complexification is needed.

The induction then follows the complex proof: descend through the orthogonal complement of an
invariant subspace **of the adjoint**, which is invariant under `A` itself. The new basis vectors
are appended at the end, `Fin (m + d)` with `Fin.addCases`, `d ∈ {1, 2}` being the dimension of the
peeled subspace; the block index takes the value `m` on them, which is larger than every value it
takes on the first `m`.

The bound "at most two elements per block" is carried through the induction in the equivalent form
`∀ i j, p i = p j → (i : ℕ) ≤ (j : ℕ) + 1`, which propagates without any counting, and is turned
into a statement about cardinalities once, at the end.
-/

open Module Polynomial Submodule

namespace LinearMap

/-! ### An invariant subspace of dimension one or two -/

section Invariant

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Some *irreducible* real polynomial annihilates a nonzero vector, given that some nonzero
polynomial does. The induction splits a reducible annihilator `f = g h`: either `h` already
annihilates `v`, or it sends `v` to a nonzero vector annihilated by `g`. -/
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

/-- **A real operator has an invariant subspace of dimension one or two.** This is the substitute,
over `ℝ`, for the existence of an eigenvector, and it is what makes the `2 × 2` blocks of the real
Schur form appear. -/
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

end Invariant

/-! ### The quasi-triangular orthonormal basis -/

section QuasiTriangular

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The orthogonal complement of a subspace invariant under the **adjoint** is invariant under the
operator itself: `⟪u, A y⟫ = ⟪A† u, y⟫` vanishes for `u` in the subspace. -/
theorem mem_orthogonal_of_adjoint_invariant [FiniteDimensional ℝ E] {A : E →ₗ[ℝ] E}
    {W : Submodule ℝ E} (hW : ∀ w ∈ W, LinearMap.adjoint A w ∈ W) {y : E} (hy : y ∈ Wᗮ) :
    A y ∈ Wᗮ := by
  rw [Submodule.mem_orthogonal] at hy ⊢
  intro u hu
  rw [← LinearMap.adjoint_inner_left]
  exact hy _ (hW u hu)

/-- The induction behind the real Schur form: an orthonormal basis in which the entries of `A`
below the diagonal blocks vanish. The space is quantified inside the statement because the
induction descends to the orthogonal complement of the peeled subspace, and the block bound is
carried in the form `p i = p j → (i : ℕ) ≤ (j : ℕ) + 1`. -/
private theorem exists_orthonormalBasis_aux (n : ℕ) :
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
      finrank ℝ E = n → ∀ A : E →ₗ[ℝ] E,
        ∃ (b : OrthonormalBasis (Fin n) ℝ E) (p : Fin n → ℕ), Monotone p ∧ (∀ i, p i < n) ∧
          (∀ i j, p i = p j → (i : ℕ) ≤ (j : ℕ) + 1) ∧
          ∀ i j : Fin n, p j < p i → (inner ℝ (b i) (A (b j)) : ℝ) = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E _ _ _ hE A
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨(stdOrthonormalBasis ℝ E).reindex (finCongr hE), fun i => i.elim0,
        fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    have : Nontrivial E := nontrivial_of_finrank_pos (R := ℝ) (by rw [hE]; exact hn)
    obtain ⟨W, hW0, hWd, hWinv⟩ := exists_invariant_finrank_le_two (LinearMap.adjoint A)
    obtain ⟨d, hd⟩ : ∃ d, finrank ℝ W = d := ⟨_, rfl⟩
    obtain ⟨m, hm⟩ : ∃ m, finrank ℝ (Wᗮ : Submodule ℝ E) = m := ⟨_, rfl⟩
    have hd1 : 1 ≤ d := by
      rw [← hd]
      exact Submodule.one_le_finrank_iff.2 hW0
    have hd2 : d ≤ 2 := hd ▸ hWd
    have hsum : d + m = n := by
      rw [← hd, ← hm, Submodule.finrank_add_finrank_orthogonal, hE]
    have hinv : ∀ y ∈ (Wᗮ : Submodule ℝ E), A y ∈ (Wᗮ : Submodule ℝ E) := fun _ hy =>
      mem_orthogonal_of_adjoint_invariant hWinv hy
    obtain ⟨c, p', hp'mono, hp'lt, hp'close, hp'tri⟩ :=
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
    refine ⟨(basisOfOrthonormalOfCardEqFinrank hon hcard).toOrthonormalBasis (by simpa using hon),
      p, ?_, ?_, ?_, ?_⟩
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
          rw [hfl, hfl, show A ((c j : (Wᗮ : Submodule ℝ E)) : E)
              = (((A.restrict hinv) (c j) : (Wᗮ : Submodule ℝ E)) : E) from rfl,
            ← Submodule.coe_inner]
          rw [hpl, hpl] at hji
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

/-- A block index on `Fin n` whose equal values are always within one of each other has fibres of
at most two elements: three of them would contain two at distance two or more. -/
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

/-- **The real Schur form**, operator form: a real operator has an orthonormal basis in which its
matrix is *quasi upper triangular* — block upper triangular for a monotone block index `p` whose
blocks carry at most two indices each. Over `ℂ` the blocks would all be singletons, which is
Schur's theorem; over `ℝ` an operator need not have an eigenvector, and a `2 × 2` block appears
wherever a pair of complex conjugate eigenvalues does. -/
theorem exists_orthonormalBasis_quasiUpperTriangular {n : ℕ} (hn : finrank ℝ E = n)
    (A : E →ₗ[ℝ] E) :
    ∃ (b : OrthonormalBasis (Fin n) ℝ E) (p : Fin n → ℕ), Monotone p ∧
      (∀ k, (Finset.univ.filter fun i => p i = k).card ≤ 2) ∧
      ∀ i j : Fin n, p j < p i → (inner ℝ (b i) (A (b j)) : ℝ) = 0 := by
  obtain ⟨b, p, hmono, -, hclose, htri⟩ := exists_orthonormalBasis_aux n hn A
  exact ⟨b, p, hmono, fun k => card_filter_le_two hclose k, htri⟩

end QuasiTriangular

end LinearMap

namespace Matrix

/-- **The real Schur form**, matrix form: a real square matrix is orthogonally similar to a *quasi
upper triangular* matrix, `Qᵀ A Q` block upper triangular with diagonal blocks of size `1 × 1` or
`2 × 2`. This is the quasi-Schur form of [saad2003iterative] §1.8.3, and unlike the complex Schur
triangulation it needs no complex arithmetic.

`Matrix.orthogonalGroup` is `Matrix.unitaryGroup` over a ring with trivial star, so the membership
below is `Qᵀ Q = 1`. -/
theorem exists_orthogonal_conj_quasiUpperTriangular {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    ∃ Q ∈ Matrix.orthogonalGroup (Fin N) ℝ, ∃ p : Fin N → ℕ, Monotone p ∧
      (∀ k, (Finset.univ.filter fun i => p i = k).card ≤ 2) ∧ (Qᵀ * A * Q).BlockTriangular p := by
  obtain ⟨b, p, hmono, hcard, htri⟩ :=
    LinearMap.exists_orthonormalBasis_quasiUpperTriangular
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
  refine ⟨Q, hQu, p, hmono, hcard, ?_⟩
  intro i j hji
  rw [hconj, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  exact htri i j hji

end Matrix
