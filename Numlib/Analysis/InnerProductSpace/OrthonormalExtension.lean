import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Orthonormal completion with prescribed orthogonality

Complete a finite partial orthonormal family while requiring all new vectors to be
orthogonal to a second finite family. The dimension budget counts every prescribed vector;
no linear independence of the additional family is required.
-/

noncomputable section
open scoped InnerProductSpace

namespace InnerProductSpace

/-- Retain a prescribed partial orthonormal family and complete the frame with columns
orthogonal to every prescribed query. The cardinality budget counts queries without requiring
that they be independent. -/
theorem exists_orthonormal_extension_orthogonal {E ι κ : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] [Fintype κ] (s : Finset ι) (v : ι → E)
    (hv : Orthonormal ℝ (fun i : s => v i)) (Q : κ → E)
    (hbudget : Fintype.card ι + Fintype.card κ ≤ Module.finrank ℝ E) :
    ∃ w : ι → E, Orthonormal ℝ w ∧ (∀ i ∈ s, w i = v i) ∧
      ∀ i ∉ s, ∀ j, ⟪Q j, w i⟫_ℝ = 0 := by
  classical
  let a : Sum s κ → E := Sum.elim (fun i => v i) Q
  let S := Submodule.span ℝ (Set.range a)
  have hd : Module.finrank ℝ S ≤ s.card + Fintype.card κ := by
    simpa only [Fintype.card_sum, Fintype.card_coe, S, Set.finrank] using
      finrank_range_le_card (R := ℝ) a
  have ht := S.finrank_add_finrank_orthogonal
  have hc : Fintype.card {i : ι // i ∉ s} ≤ Module.finrank ℝ Sᗮ := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_coe]
    omega
  obtain ⟨e⟩ : Nonempty ({i : ι // i ∉ s} ↪ Fin (Module.finrank ℝ Sᗮ)) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hc)
  let b := stdOrthonormalBasis ℝ Sᗮ
  let z : {i : ι // i ∉ s} → E := fun i => b (e i)
  have hz : Orthonormal ℝ z :=
    ((b.orthonormal.comp e e.injective).comp_linearIsometry Sᗮ.subtypeₗᵢ)
  have hzs : ∀ i, z i ∈ Sᗮ := fun i => (b (e i)).property
  have hvo : ∀ i ∈ s, ∀ j, ⟪v i, z j⟫_ℝ = 0 := by
    intro i hi j
    apply Submodule.inner_right_of_mem_orthogonal _ (hzs j)
    exact Submodule.subset_span ⟨Sum.inl ⟨i, hi⟩, rfl⟩
  have hQo : ∀ i j, ⟪Q j, z i⟫_ℝ = 0 := by
    intro i j
    apply Submodule.inner_right_of_mem_orthogonal _ (hzs i)
    exact Submodule.subset_span ⟨Sum.inr j, rfl⟩
  let w : ι → E := fun i => if hi : i ∈ s then v i else z ⟨i, hi⟩
  refine ⟨w, ?_, ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro i j
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ s
    · simpa [w, hi, hj, Subtype.ext_iff] using
        (orthonormal_iff_ite.mp hv ⟨i, hi⟩ ⟨j, hj⟩)
    · have hij : i ≠ j := by rintro rfl; exact hj hi
      simp only [w, hi, hj, ↓reduceDIte, hij, ↓reduceIte]
      exact hvo i hi ⟨j, hj⟩
    · have hij : i ≠ j := by rintro rfl; exact hi hj
      simp only [w, hi, hj, ↓reduceDIte, hij, ↓reduceIte]
      rw [real_inner_comm]
      exact hvo j hj ⟨i, hi⟩
    · simpa [w, hi, hj, Subtype.ext_iff] using
        (orthonormal_iff_ite.mp hz ⟨i, hi⟩ ⟨j, hj⟩)
  · intro i hi
    simp [w, hi]
  · intro i hi j
    simpa [w, hi] using hQo ⟨i, hi⟩ j

end InnerProductSpace
