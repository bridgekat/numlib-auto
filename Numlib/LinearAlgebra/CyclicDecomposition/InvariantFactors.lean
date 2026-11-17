import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Order.CompactlyGenerated.Basic
import Numlib.Krylov.Coprime
import Numlib.LinearAlgebra.CyclicDecomposition

/-!
# Invariant factors from Jordan chains

Over an algebraically closed field, a finite-dimensional space decomposes into
cyclic subspaces whose minimal polynomials are ordered by divisibility.

## Main results

* `Module.End.exists_isInternal_invariantFactorKrylov`: the invariant-factor decomposition.

## Proof outline

Sort the Jordan chains for each eigenvalue by decreasing length. Sum the generators
at each position across the different eigenvalues. The minimal polynomials of those
generators are coprime, so the resulting vector generates the corresponding sum of
cyclic spaces. Its minimal polynomial has one factor for each eigenvalue, with
exponents that decrease from one position to the next.
-/

open Polynomial

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

private theorem exists_sorted_primaryKrylov [IsAlgClosed K] (A : End K V) :
    ∃ (q : ℕ) (μ : Fin q → K) (d : Fin q → ℕ) (e : ∀ i, Fin (d i) → ℕ)
      (v : ∀ i, Fin (d i) → V),
      Function.Injective μ ∧ (∀ i, Antitone (e i)) ∧ (∀ i j, 0 < e i j) ∧
      (∀ i j, Krylov.minpolyVec A (v i j) = (X - C (μ i)) ^ e i j) ∧
      DirectSum.IsInternal (fun p : (i : Fin q) × Fin (d i) => Krylov.fullSubspace A (v p.1 p.2)) := by
  classical
  obtain ⟨q, μ, d, e, b, hinj, -, he, hb⟩ := A.exists_basis_toMatrix_eq_blockDiagonal'_jordanForm
  let τ := Equiv.sigmaAssoc fun (i : Fin q) (j : Fin (d i)) => Fin (e i j)
  let e' : ((i : Fin q) × Fin (d i)) → ℕ := fun p => e p.1 p.2
  let μ' : ((i : Fin q) × Fin (d i)) → K := fun p => μ p.1
  let b' := b.reindex τ.symm
  have hb' : LinearMap.toMatrix b' b' A = Matrix.jordanForm e' μ' := by
    rw [show b' = b.reindex τ.symm from rfl, LinearMap.toMatrix_reindex, Equiv.symm_symm, hb]
    simp_rw [Matrix.jordanForm_def]
    rw [Matrix.blockDiagonal'_blockDiagonal' fun i j => Matrix.jordanBlock (e i j) (μ i),
      Matrix.submatrix_submatrix]
    rw [show (⇑τ.symm ∘ ⇑τ) = id from funext fun p => τ.symm_apply_apply p]
    rfl
  obtain ⟨v, -, hp, hd⟩ := A.exists_isInternal_primaryKrylov e' μ' b'
    (fun p => he p.1 p.2) hb'
  let σ (i : Fin q) := Tuple.sortDesc (e i)
  let σ' := Equiv.sigmaCongrRight σ
  refine ⟨q, μ, d, (fun i j => e i (σ i j)), (fun i j => v ⟨i, σ i j⟩), hinj,
    (fun i => Tuple.antitone_sortDesc (e i)), (fun i j => he i (σ i j)),
    (fun i j => hp ⟨i, σ i j⟩), ?_⟩
  change DirectSum.IsInternal (fun p => Krylov.fullSubspace A (v (σ' p)))
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (hd.submodule_iSupIndep.comp σ'.injective)
    (σ'.iSup_comp.trans hd.submodule_iSup_eq_top)

omit [FiniteDimensional K V] in
private theorem isInternal_fiberSup {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    (W : ι → Submodule K V) (f : ι → J) (hW : DirectSum.IsInternal W) :
    DirectSum.IsInternal (fun j => ⨆ i, ⨆ _ : f i = j, W i) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    intro j
    have hs : Disjoint {i | f i = j} {i | f i ≠ j} :=
      Set.disjoint_left.2 fun _ he hn => hn he
    refine (hW.submodule_iSupIndep.disjoint_biSup_biSup hs).mono_right ?_
    refine iSup_le fun k => iSup_le fun hk => iSup_le fun i => iSup_le fun hi => ?_
    exact le_iSup_of_le i (le_iSup_of_le (fun hj => hk (hi.symm.trans hj)) le_rfl)
  · apply top_unique
    rw [← hW.submodule_iSup_eq_top]
    exact iSup_le fun i => le_iSup_of_le (f i)
      (le_iSup_of_le i (le_iSup_of_le rfl le_rfl))

/-- A finite-dimensional endomorphism over an algebraically closed field admits a
direct sum decomposition into nonzero cyclic subspaces. Their vector minimal polynomials
are ordered by reverse divisibility, and the first equals the operator's minimal polynomial
when the decomposition is nonempty. -/
theorem exists_isInternal_invariantFactorKrylov [IsAlgClosed K] (A : End K V) :
    ∃ (m : ℕ) (w : Fin m → V),
      DirectSum.IsInternal (fun j => Krylov.fullSubspace A (w j)) ∧
      (∀ j, 0 < Krylov.grade A (w j)) ∧
      (∀ i j, i ≤ j → Krylov.minpolyVec A (w j) ∣ Krylov.minpolyVec A (w i)) ∧
      (∀ h : 0 < m, Krylov.minpolyVec A (w ⟨0, h⟩) = minpoly K A) := by
  classical
  obtain ⟨q, μ, d, e, v, hμ, he, hpos, hp, hsum⟩ := exists_sorted_primaryKrylov A
  let m := Finset.univ.sup d
  let W (p : (i : Fin q) × Fin (d i)) := Krylov.fullSubspace A (v p.1 p.2)
  let ψ (p : (i : Fin q) × Fin (d i)) : Fin m :=
    ⟨p.2, p.2.isLt.trans_le (Finset.le_sup (Finset.mem_univ p.1))⟩
  let u (j : Fin m) (i : Fin q) : V :=
    if h : (j : ℕ) < d i then v i ⟨j, h⟩ else 0
  let k (j : Fin m) (i : Fin q) : ℕ :=
    if h : (j : ℕ) < d i then e i ⟨j, h⟩ else 0
  let w (j : Fin m) := ∑ i, u j i
  let f (j : Fin m) (i : Fin q) := (X - C (μ i)) ^ k j i
  have hu (j : Fin m) (i : Fin q) : Krylov.minpolyVec A (u j i) = f j i := by
    by_cases hi : (j : ℕ) < d i
    · simp [u, f, k, hi, hp]
    · simp [u, f, k, hi]
  have hk (i : Fin q) : Antitone (fun j : Fin m => k j i) := by
    intro j j' h
    by_cases hh : (j' : ℕ) < d i
    · have hj : (j : ℕ) < d i := lt_of_le_of_lt h hh
      simpa [k, hj, hh] using he i (show (⟨j, hj⟩ : Fin (d i)) ≤ ⟨j', hh⟩ from h)
    · simp [k, hh]
  have hcol (j : Fin m) :
      Krylov.minpolyVec A (w j) = ∏ i, f j i ∧
        Krylov.fullSubspace A (w j) = ⨆ i, Krylov.fullSubspace A (u j i) := by
    have hc : Pairwise fun i l => IsCoprime (Krylov.minpolyVec A (u j i))
        (Krylov.minpolyVec A (u j l)) := by
      intro i l hne
      rw [hu, hu]
      exact ((pairwise_coprime_X_sub_C hμ) hne).pow
    obtain ⟨hc₁, hc₂⟩ := Krylov.minpolyVec_fullSubspace_finsetSum_of_pairwise_isCoprime A
      (u j) hc Finset.univ
    exact ⟨by simpa only [hu] using hc₁, by simpa [Finset.sup_eq_iSup] using hc₂⟩
  have hfiber (j : Fin m) : Krylov.fullSubspace A (w j) = ⨆ p, ⨆ _ : ψ p = j, W p := by
    rw [(hcol j).2]
    apply le_antisymm
    · refine iSup_le fun i => ?_
      by_cases hi : (j : ℕ) < d i
      · rw [show u j i = v i ⟨j, hi⟩ from dite_eq_left hi]
        exact le_iSup_of_le ⟨i, ⟨j, hi⟩⟩ (le_iSup_of_le (Fin.ext rfl) le_rfl)
      · simp [u, hi]
    · refine iSup_le fun ⟨i, p⟩ => iSup_le fun h => ?_
      have hval : (p : ℕ) = (j : ℕ) := congrArg Fin.val h
      have hi : (j : ℕ) < d i := hval ▸ p.isLt
      have h' : u j i = v i p := by
        rw [show u j i = v i ⟨j, hi⟩ from dite_eq_left hi, show (⟨j, hi⟩ : Fin (d i)) = p
          from Fin.ext hval.symm]
      exact le_iSup_of_le i (le_of_eq (congrArg (Krylov.fullSubspace A) h'.symm))
  have hdvd (j : Fin m) (i : Fin q) : f j i ∣ Krylov.minpolyVec A (w j) := by
    rw [(hcol j).1]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  refine ⟨m, w, ?_, ?_, ?_, ?_⟩
  · simp_rw [hfiber]
    exact isInternal_fiberSup W ψ hsum
  · intro j
    have hex : ∃ i, (j : ℕ) < d i := by
      by_contra! h
      exact j.isLt.not_ge (Finset.sup_le fun i _ => h i)
    obtain ⟨i, hi⟩ := hex
    have hd := natDegree_le_of_dvd (hdvd j i) (Krylov.minpolyVec_ne_zero A (w j))
    rw [Krylov.natDegree_minpolyVec] at hd
    exact (hpos i ⟨j, hi⟩).trans_le (by simpa [f, k, hi, natDegree_pow] using hd)
  · intro i j hij
    rw [(hcol i).1, (hcol j).1]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun l _ => pow_dvd_pow _ (hk l hij)
  · intro hm
    let j : Fin m := ⟨0, hm⟩
    let p := Krylov.minpolyVec A (w j)
    have hann : aeval A p = 0 := by
      apply LinearMap.ker_eq_top.1
      apply top_unique
      rw [← hsum.submodule_iSup_eq_top]
      refine iSup_le fun ⟨i, l⟩ => (Krylov.fullSubspace_le_ker_aeval_iff A _ _).2 ?_
      have hi : (j : ℕ) < d i := Nat.zero_lt_of_lt l.isLt
      have he' : e i l ≤ e i ⟨j, hi⟩ := he i (Nat.zero_le _)
      rw [hp]
      apply dvd_trans _ (hdvd j i)
      exact pow_dvd_pow _ (by simpa [k, hi] using he')
    have hd : minpoly K A ∣ p := minpoly.dvd K A hann
    have hd' : p ∣ minpoly K A := (Krylov.minpolyVec_dvd_iff A (w j)).2
      (by rw [minpoly.aeval, LinearMap.zero_apply])
    have hp' : p.Monic := Krylov.minpolyVec_monic A (w j) (Krylov.minpolyVec_ne_zero A (w j))
    have hm' := minpoly.monic (IsIntegral.of_finite K A)
    exact eq_of_dvd_of_natDegree_le_of_leadingCoeff hd'
      (natDegree_le_of_dvd hd hp'.ne_zero) (hp'.leadingCoeff.trans hm'.leadingCoeff.symm)

end Module.End
