/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: a new `Mathlib.LinearAlgebra.Tensor` directory beside `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.LinearAlgebra.Tensor.Unfolding

/-!
# The CP format and tensor rank

A CP (CANDECOMP/PARAFAC) tensor ([golub2013matrix] §12.5.4–12.5.5) is a weighted sum of `r`
rank-one tensors, `𝒳 = ∑_j λ_j F⁽¹⁾(:, j) ∘ ⋯ ∘ F⁽ᵈ⁾(:, j)`, given by the weights `c : ρ → R` and
the factor matrices `F i : Matrix (κ i) ρ R` whose columns are the rank-one factors. Its unfoldings
are products with the Khatri–Rao product of the other factors, and the tensor rank is the least
number of terms of a CP representation.

The ALS iteration of the book is an unnumbered "Repeat" framework; what each of its updates
solves is a matrix least-squares problem on the unfolding `Tensor.modeUnfold_cp`. The weights'
normalization (unit columns) is a constraint of the approximation problem, not of the format.

## Main definitions

* `Tensor.cp c F`: the CP tensor.
* `Tensor.tensorRank A`: the least number of rank-one terms representing `A`.

## Main statements

* `Tensor.modeUnfold_cp`: `𝒳_(k) = F_k diag(c) (⊙_{j ≠ k} F_j)ᵀ`.
* `Tensor.vecFin_cp`: `vec 𝒳 = (F_d ⊙ ⋯ ⊙ F_1) c`.
* `Tensor.tensorRank_le_iff`, `Tensor.isRankOne_iff_tensorRank_le_one`.

## References

* [golub2013matrix], §12.5.4–12.5.5.
-/

universe u v w

open Matrix

namespace Tensor

variable {ι : Type u} {κ : ι → Type v} {R : Type w} {ρ ρ' : Type*}

section CP

variable [Fintype ι] [CommSemiring R] [Fintype ρ]

/-- The CP tensor ([golub2013matrix] (12.5.15), (12.5.21)): `∑_j c_j F_1(:, j) ∘ ⋯ ∘ F_d(:, j)`. -/
def cp (c : ρ → R) (F : ∀ i, Matrix (κ i) ρ R) : Tensor κ R :=
  ∑ j, c j • rankOne fun i a => F i a j

/-- The entries of a CP tensor. -/
theorem cp_apply (c : ρ → R) (F : ∀ i, Matrix (κ i) ρ R) (a : ∀ i, κ i) :
    cp c F a = ∑ j, c j * ∏ i, F i (a i) j := by
  simp [cp]

/-- A CP tensor is a CP tensor over any larger index set of terms, padded by zero weights. -/
theorem cp_eq_cp_of_injective (e : ρ → ρ') (he : Function.Injective e) [Fintype ρ']
    (c : ρ → R) (F : ∀ i, Matrix (κ i) ρ R) :
    ∃ (c' : ρ' → R) (F' : ∀ i, Matrix (κ i) ρ' R), cp c F = cp c' F' := by
  classical
  refine ⟨fun j => if h : ∃ x, e x = j then c h.choose else 0,
    fun i => Matrix.of fun a j => if h : ∃ x, e x = j then F i a h.choose else 0,
    ext fun a => ?_⟩
  simp only [cp_apply, Matrix.of_apply]
  refine Fintype.sum_of_injective e he (fun j => c j * ∏ i, F i (a i) j) _ (fun j hj => ?_)
    (fun x => ?_)
  · rw [dite_eq_right (by simpa using hj), zero_mul]
  · have h : ∃ y, e y = e x := ⟨x, rfl⟩
    have hx : h.choose = x := he h.choose_spec
    simp only [dite_eq_left h, hx]

variable [DecidableEq ι]

/-- The mode-`k` unfolding of a CP tensor ([golub2013matrix] the displays before (12.5.16) and
after (12.5.21)): `𝒳_(k) = F_k diag(c) (⊙_{j ≠ k} F_j)ᵀ`. -/
theorem modeUnfold_cp [DecidableEq ρ] (c : ρ → R) (F : ∀ i, Matrix (κ i) ρ R) (k : ι) :
    (cp c F).modeUnfold k = F k * diagonal c * (piKhatriRao fun j : {j // j ≠ k} => F j)ᵀ := by
  ext x col
  rw [mul_apply]
  simp only [mul_diagonal, transpose_apply, piKhatriRao_apply, modeUnfold, Matrix.of_apply,
    cp_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ k]
  have h1 : F k ((Equiv.piSplitAt k κ).symm (x, col) k) j = F k x j := by
    simp [Equiv.piSplitAt_symm_apply]
  have h2 : ∏ l : {l // l ≠ k}, F l ((Equiv.piSplitAt k κ).symm (x, col) l) j
      = ∏ l : {l // l ≠ k}, F l (col l) j :=
    Finset.prod_congr rfl fun l _ => by rw [Equiv.piSplitAt_symm_apply, dite_eq_right l.2]
  rw [h1, h2]
  ring

end CP

section VecFin

variable {d : ℕ} {n : Fin d → ℕ} [CommSemiring R] [Fintype ρ]

/-- `vec 𝒳 = (F_d ⊙ ⋯ ⊙ F_1) c` for a `Fin`-shaped CP tensor ([golub2013matrix] P12.5.6), the
flattened `piKhatriRao` being the book's reversed Khatri–Rao product. -/
theorem vecFin_cp (c : ρ → R) (F : ∀ k, Matrix (Fin (n k)) ρ R) :
    vecFin (cp c F) = (piKhatriRao F).reindex finPiFinEquiv (Equiv.refl _) *ᵥ c := by
  funext t
  simp only [vecFin, cp_apply, reindex_apply, submatrix_apply, mulVec, dotProduct,
    piKhatriRao_apply, Equiv.refl_symm, Equiv.refl_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end VecFin

/-! ### Tensor rank -/

section Rank

variable [Fintype ι] [CommSemiring R]

/-- Every tensor is a CP tensor, with one term per entry. -/
theorem exists_eq_cp [DecidableEq ι] [∀ i, Fintype (κ i)] (A : Tensor κ R) :
    ∃ (c : Fin (Fintype.card (∀ i, κ i)) → R) (F : ∀ i, Matrix (κ i) _ R), A = cp c F := by
  classical
  set e := (Fintype.equivFin (∀ i, κ i)).symm
  refine ⟨fun j => A (e j), fun i x j => (Pi.single (e j i) 1 : κ i → R) x, ?_⟩
  unfold cp
  conv_lhs => rw [eq_sum_rankOne_single A]
  exact (Fintype.sum_equiv e
    (fun j => A (e j) • rankOne fun i x => (Pi.single (e j i) (1 : R) : κ i → R) x)
    (fun b => A b • rankOne fun i => (Pi.single (b i) (1 : R) : κ i → R)) fun _ => rfl).symm

/-- The rank of a tensor ([golub2013matrix] §12.5.5): the least `r` such that `A` is a sum of `r`
rank-one tensors (with weights). -/
noncomputable def tensorRank (A : Tensor κ R) : ℕ :=
  sInf {r | ∃ (c : Fin r → R) (F : ∀ i, Matrix (κ i) (Fin r) R), A = cp c F}

/-- `tensorRank A ≤ r` iff `A` is a CP tensor with `r` terms. -/
theorem tensorRank_le_iff [∀ i, Finite (κ i)] (A : Tensor κ R) (r : ℕ) :
    tensorRank A ≤ r ↔ ∃ (c : Fin r → R) (F : ∀ i, Matrix (κ i) (Fin r) R), A = cp c F := by
  classical
  have : ∀ i, Fintype (κ i) := fun i => Fintype.ofFinite _
  constructor
  · intro h
    have hne : {r | ∃ (c : Fin r → R) (F : ∀ i, Matrix (κ i) (Fin r) R), A = cp c F}.Nonempty :=
      ⟨_, exists_eq_cp A⟩
    obtain ⟨c, F, hA⟩ := Nat.sInf_mem hne
    obtain ⟨c', F', h'⟩ := cp_eq_cp_of_injective (Fin.castLE h) (Fin.castLE_injective h) c F
    exact ⟨c', F', hA.trans h'⟩
  · rintro ⟨c, F, hA⟩
    exact Nat.sInf_le ⟨c, F, hA⟩

/-- A scalar multiple of a rank-one tensor is rank-one, when there is a mode to absorb it. -/
theorem smul_rankOne_isRankOne [Nonempty ι] (a : R) (z : ∀ i, κ i → R) :
    (a • rankOne z).IsRankOne := by
  classical
  obtain ⟨k⟩ := ‹Nonempty ι›
  refine ⟨Function.update z k (a • z k), ?_⟩
  rw [rankOne_update_smul, Function.update_eq_self]

/-- A tensor with at least one mode is rank-one iff its tensor rank is at most one. -/
theorem isRankOne_iff_tensorRank_le_one [Nonempty ι] [∀ i, Finite (κ i)] (A : Tensor κ R) :
    A.IsRankOne ↔ tensorRank A ≤ 1 := by
  rw [tensorRank_le_iff]
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨fun _ => 1, fun i a _ => z i a, ?_⟩
    simp [cp]
  · rintro ⟨c, F, rfl⟩
    simpa [cp] using smul_rankOne_isRankOne (c 0) fun i a => F i a 0

end Rank

end Tensor
