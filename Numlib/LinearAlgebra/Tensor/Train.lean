/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: a new `Mathlib.LinearAlgebra.Tensor` directory beside `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.LinearAlgebra.Matrix.Rank
import Numlib.LinearAlgebra.Tensor.Unfolding

/-!
# Tensor trains

A tensor train ([golub2013matrix] §12.5.8, (12.5.25)–(12.5.29); Oseledets–Tyrtyshnikov 2009) with
mode sizes `n : ℕ → ℕ` and ranks `r : ℕ → ℕ`, `r 0 = r d = 1`, is given by cores
`G k : Fin (n k) → Matrix (Fin (r k)) (Fin (r (k + 1))) R`: the book's carriages
`𝒢_k ∈ ℝ^{r_{k−1} × n_k × r_k}` read as matrix-valued functions of the middle index. The entry
`𝒯(i)` is the `1 × 1` matrix product `G 0 (i 0) ⋯ G (d − 1) (i (d − 1))`. The partial products are
defined by recursion on `d` with `Fin.castSucc`/`Fin.last`, which reduces definitionally.

## Main definitions

* `Tensor.ttPartial G d i`: the left partial product `G 0 (i 0) ⋯ G (d − 1) (i (d − 1))`.
* `Tensor.tensorTrain d h0 hd G`: the tensor train.

## Main statements

* `Tensor.exists_ttCore_of_rank`: one step of the TT-SVD, a core from a rank factorization.
* `Tensor.exists_tensorTrain_of_ne_zero`: every tensor of order `d ≥ 1` is a tensor train whose
  ranks are those of its sequential unfoldings `A_{[0,k) × [k,d)}` (the TT-SVD, (12.5.29)). The
  proof chooses, for each `k`, a basis of the column space of the `k`-th sequential unfolding (as
  functions of the first `k` indices); fixing the `k`-th index maps the column space at `k + 1`
  into the one at `k`, and the coefficients are the cores
  (`Tensor.exists_ttPartial_eq_of_mem_span`).

## References

* [golub2013matrix], §12.5.8.
-/

universe u

open Matrix

namespace Tensor

variable {R : Type u} [CommSemiring R] {n r : ℕ → ℕ}

/-- The left partial products of a tensor train ([golub2013matrix] §12.5.8):
`ttPartial G d i = G 0 (i 0) * ⋯ * G (d − 1) (i (d − 1))`, an `r 0 × r d` matrix. -/
def ttPartial (G : ∀ k, Fin (n k) → Matrix (Fin (r k)) (Fin (r (k + 1))) R) :
    ∀ d : ℕ, (∀ k : Fin d, Fin (n k)) → Matrix (Fin (r 0)) (Fin (r d)) R
  | 0, _ => 1
  | d + 1, i => ttPartial G d (fun k => i k.castSucc) * G d (i (Fin.last d))

variable (G : ∀ k, Fin (n k) → Matrix (Fin (r k)) (Fin (r (k + 1))) R)

@[simp]
theorem ttPartial_zero (i : ∀ k : Fin 0, Fin (n k)) : ttPartial G 0 i = 1 :=
  rfl

theorem ttPartial_succ (d : ℕ) (i : ∀ k : Fin (d + 1), Fin (n k)) :
    ttPartial G (d + 1) i = ttPartial G d (fun k => i k.castSucc) * G d (i (Fin.last d)) :=
  rfl

/-- The entries of the partial products: a sum over the rank index of the last contraction. -/
theorem ttPartial_succ_apply (d : ℕ) (i : ∀ k : Fin (d + 1), Fin (n k)) (p : Fin (r 0))
    (q : Fin (r (d + 1))) :
    ttPartial G (d + 1) i p q
      = ∑ s, ttPartial G d (fun k => i k.castSucc) p s * G d (i (Fin.last d)) s q :=
  mul_apply

/-- The tensor train ([golub2013matrix] (12.5.25)) with boundary ranks `r 0 = r d = 1`:
`𝒯(i) = 𝒢₁(i₁) 𝒢₂(i₂) ⋯ 𝒢_d(i_d)`, a `1 × 1` product. -/
def tensorTrain (d : ℕ) (h0 : r 0 = 1) (hd : r d = 1) :
    Tensor (fun k : Fin d => Fin (n k)) R :=
  of fun i => ttPartial G d i (Fin.cast h0.symm 0) (Fin.cast hd.symm 0)

theorem tensorTrain_apply (d : ℕ) (h0 : r 0 = 1) (hd : r d = 1) (i : ∀ k : Fin d, Fin (n k)) :
    tensorTrain G d h0 hd i = ttPartial G d i (Fin.cast h0.symm 0) (Fin.cast hd.symm 0) :=
  rfl

/-- One step of the TT-SVD construction ([golub2013matrix] (12.5.26)–(12.5.28), P12.5.11): a
matrix `C` whose rows are indexed by a previous rank index `k` and the next mode `i`, of rank at
most `s`, factors through a core: `C (k, i) c = (G i * C') k c` with `G i : p × s` (the book takes
`G' = U₃`, `C' = Σ₃ V₃ᵀ` from an SVD; any rank factorization works). -/
theorem exists_ttCore_of_rank {K : Type*} [Field K] {p m s : ℕ} {N : Type*} [Fintype N]
    (C : Matrix (Fin p × Fin m) N K) (hC : C.rank ≤ s) :
    ∃ (G : Fin m → Matrix (Fin p) (Fin s) K) (C' : Matrix (Fin s) N K),
      ∀ k i c, C (k, i) c = (G i * C') k c := by
  obtain ⟨G', C', h⟩ := (Matrix.rank_le_iff_exists_mul C s).1 hC
  refine ⟨fun i => Matrix.of fun k k' => G' (k, i) k', C', fun k i c => ?_⟩
  rw [h, mul_apply, mul_apply]
  rfl

/-! ### Existence: the TT-SVD -/

section Existence

variable {K : Type*} [Field K]

/-- The recursion of the TT-SVD, abstracted: families `P k` of `r k` functions of the first `k`
indices, with `P 0 = 1` and each `β ↦ P (k + 1) t (β, i)` in the span of the family `P k`, are the
partial products `ttPartial G k` of some cores `G` (the coefficients of those spans). -/
theorem exists_ttPartial_eq_of_mem_span {d : ℕ} (h0 : r 0 = 1)
    (P : ∀ k, Fin (r k) → (∀ j : Fin k, Fin (n j)) → K) (hP0 : ∀ t β, P 0 t β = 1)
    (hP : ∀ k < d, ∀ t (i : Fin (n k)),
      (fun β => P (k + 1) t (Fin.snoc (α := fun j : Fin (k + 1) => Fin (n j)) β i)) ∈
        Submodule.span K (Set.range (P k))) :
    ∃ G : ∀ k, Fin (n k) → Matrix (Fin (r k)) (Fin (r (k + 1))) K,
      ∀ k ≤ d, ∀ β p t, ttPartial G k β p t = P k t β := by
  choose c hc using fun k (hk : k < d) t i =>
    (Submodule.mem_span_range_iff_exists_fun K).1 (hP k hk t i)
  refine ⟨fun k i => Matrix.of fun s t => if hk : k < d then c k hk t i s else 0, fun k => ?_⟩
  induction k with
  | zero =>
    intro _ β p t
    have : Subsingleton (Fin (r 0)) := by rw [h0]; infer_instance
    obtain rfl := Subsingleton.elim p t
    rw [ttPartial_zero, one_apply_eq, hP0]
  | succ k ih =>
    intro hk β p t
    have h : ∑ s, c k hk t (β (Fin.last k)) s * P k s (Fin.init β) = P (k + 1) t β := by
      have := congrFun (hc k hk t (β (Fin.last k))) (Fin.init β)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rwa [Fin.snoc_init_self] at this
    rw [ttPartial_succ_apply, ← h]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ih (by omega), Matrix.of_apply, dite_eq_left (show k < d by omega), mul_comm]
    rfl

variable {d : ℕ} (A : Tensor (fun k : Fin d => Fin (n k)) K)

/-- The fibres of `A` in its first `k` modes: `seqCol A k a` is the column of the sequential
unfolding `A_{[0,k) × [k,d)}` through the multi-index `a` (its first `k` entries ignored), as a
function of the first `k` indices. -/
private def seqCol (k : ℕ) (a : ∀ i : Fin d, Fin (n i)) : (∀ j : Fin k, Fin (n j)) → K :=
  fun β => A fun i => if h : (i : ℕ) < k then β ⟨i, h⟩ else a i

/-- The column space of the sequential unfolding `A_{[0,k) × [k,d)}`. -/
private def seqSpan (k : ℕ) : Submodule K ((∀ j : Fin k, Fin (n j)) → K) :=
  Submodule.span K (Set.range (seqCol A k))

/-- The dimension of `seqSpan A k` is the rank of the sequential unfolding. -/
private theorem rank_unfold_eq_finrank_seqSpan {k : ℕ} (hk : k ≤ d) :
    (A.unfold fun i : Fin d => (i : ℕ) < k).rank = Module.finrank K (seqSpan A k) := by
  rcases isEmpty_or_nonempty (∀ i : Fin d, Fin (n i)) with he | hne
  · have hU : A.unfold (fun i : Fin d => (i : ℕ) < k) = 0 := by
      ext ρ c
      exact isEmptyElim ((Equiv.piEquivPiSubtypeProd (fun i : Fin d => (i : ℕ) < k)
        (fun i : Fin d => Fin (n i))).symm (ρ, c))
    have hS : seqSpan A k = ⊥ := by
      rw [seqSpan, Set.range_eq_empty, Submodule.span_empty]
    rw [hU, rank_zero, hS, finrank_bot]
  · obtain ⟨a₀⟩ := hne
    let e : (∀ j : Fin k, Fin (n j)) ≃ (∀ i : {i : Fin d // (i : ℕ) < k}, Fin (n i)) :=
      { toFun := fun β i => β ⟨i, i.2⟩
        invFun := fun ρ j => ρ ⟨⟨j, j.2.trans_le hk⟩, j.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [rank_eq_finrank_span_cols, ← LinearEquiv.finrank_map_eq (LinearEquiv.funCongrLeft K K e),
      Submodule.map_span, ← Set.range_comp, seqSpan]
    refine congrArg (fun s => Module.finrank K (Submodule.span K s)) (Set.ext fun v => ⟨?_, ?_⟩)
    · rintro ⟨c, rfl⟩
      refine ⟨(Equiv.piEquivPiSubtypeProd (fun i : Fin d => (i : ℕ) < k)
        (fun i : Fin d => Fin (n i))).symm (fun i => a₀ i, c), funext fun β => ?_⟩
      simp only [seqCol, Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply,
        LinearMap.funLeft_apply, col_apply, unfold, Matrix.of_apply]
      congr 1
      funext i
      by_cases h : (i : ℕ) < k <;> simp [h, e]
    · rintro ⟨a, rfl⟩
      refine ⟨fun i => a i, funext fun β => ?_⟩
      simp only [seqCol, Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply,
        LinearMap.funLeft_apply, col_apply, unfold, Matrix.of_apply]
      congr 1

/-- Fixing the next index maps the column space at `k + 1` into the column space at `k`. -/
private theorem snoc_mem_seqSpan {k : ℕ} (hk : k < d) (i : Fin (n k))
    {v : (∀ j : Fin (k + 1), Fin (n j)) → K} (hv : v ∈ seqSpan A (k + 1)) :
    (fun β => v (Fin.snoc (α := fun j : Fin (k + 1) => Fin (n j)) β i)) ∈ seqSpan A k := by
  let L : ((∀ j : Fin (k + 1), Fin (n j)) → K) →ₗ[K] ((∀ j : Fin k, Fin (n j)) → K) :=
    LinearMap.funLeft K K fun β => Fin.snoc (α := fun j : Fin (k + 1) => Fin (n j)) β i
  have hL : (seqSpan A (k + 1)).map L ≤ seqSpan A k := by
    rw [seqSpan, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨Function.update a ⟨k, hk⟩ i, funext fun β => ?_⟩
    simp only [seqCol, L, LinearMap.funLeft_apply]
    congr 1
    funext j
    rcases lt_trichotomy (j : ℕ) k with hj | hj | hj
    · rw [dite_eq_left hj, dite_eq_left (by omega)]
      exact (Fin.snoc_castSucc (α := fun j : Fin (k + 1) => Fin (n j)) (p := β) (x := i)
        ⟨j, hj⟩).symm
    · obtain rfl : j = ⟨k, hk⟩ := Fin.ext hj
      rw [dite_eq_right (lt_irrefl _), dite_eq_left (Nat.lt_succ_self _), Function.update_self]
      exact (Fin.snoc_last (α := fun j : Fin (k + 1) => Fin (n j)) (p := β) (x := i)).symm
    · rw [dite_eq_right (by omega), dite_eq_right (by omega),
        Function.update_of_ne (fun h => by rw [h] at hj; exact lt_irrefl _ hj)]
  exact hL (Submodule.mem_map_of_mem hv)

/-- Past the last mode the column space contains `A` itself. -/
private theorem mem_seqSpan_of_le {k : ℕ} (hk : d ≤ k) :
    (fun β : ∀ j : Fin k, Fin (n j) => A fun i => β ⟨i, i.2.trans_le hk⟩) ∈ seqSpan A k := by
  rcases isEmpty_or_nonempty (∀ i : Fin d, Fin (n i)) with he | ⟨⟨a⟩⟩
  · convert zero_mem (seqSpan A k) using 1
    funext β
    exact isEmptyElim (fun i : Fin d => β ⟨i, i.2.trans_le hk⟩)
  · refine Submodule.subset_span ⟨a, funext fun β => ?_⟩
    simp only [seqCol]
    congr 1
    funext i
    rw [dite_eq_left (i.2.trans_le hk)]

/-- The TT-ranks of `A`: `1` at the ends, the ranks of the sequential unfoldings between. -/
private noncomputable def seqRank (k : ℕ) : ℕ :=
  open Classical in if k = 0 ∨ k = d then 1 else Module.finrank K (seqSpan A k)

private theorem seqRank_of_ne {k : ℕ} (h₀ : k ≠ 0) (hd : k ≠ d) :
    seqRank A k = Module.finrank K (seqSpan A k) := by
  rw [seqRank, ite_eq_right (by tauto)]

/-- The left factors of the TT-SVD: `1`, then bases of the column spaces `seqSpan A k`, then
`A`. -/
private noncomputable def seqFactor (k : ℕ) (t : Fin (seqRank A k)) :
    (∀ j : Fin k, Fin (n j)) → K :=
  if h₀ : k = 0 then fun _ => 1
  else if hd : k = d then fun β => A fun i => β ⟨i, hd ▸ i.2⟩
  else (Module.finBasis K (seqSpan A k) (Fin.cast (seqRank_of_ne A h₀ hd) t) : _)

/-- The column space at `k < d` lies in the span of the left factors. -/
private theorem seqSpan_le_span_seqFactor {k : ℕ} (hk : k < d) :
    seqSpan A k ≤ Submodule.span K (Set.range (seqFactor A k)) := by
  intro v hv
  by_cases h₀ : k = 0
  · subst h₀
    have h1 : seqRank A 0 = 1 := by rw [seqRank, ite_eq_left (Or.inl rfl)]
    have hv : v = v default • seqFactor A 0 (Fin.cast h1.symm 0) := by
      funext β
      rw [Pi.smul_apply, seqFactor, dite_eq_left rfl, smul_eq_mul, mul_one, Subsingleton.elim β]
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · obtain ⟨x, rfl⟩ : ∃ x : seqSpan A k, (x : _) = v := ⟨⟨v, hv⟩, rfl⟩
    rw [← (Module.finBasis K (seqSpan A k)).sum_repr x, Submodule.coe_sum]
    refine Submodule.sum_mem _ fun s _ => ?_
    rw [Submodule.coe_smul]
    refine Submodule.smul_mem _ _
      (Submodule.subset_span ⟨Fin.cast (seqRank_of_ne A h₀ hk.ne).symm s, ?_⟩)
    rw [seqFactor, dite_eq_right h₀, dite_eq_right hk.ne]
    rfl

/-- The left factor at `k + 1 ≤ d` lies in the column space. -/
private theorem seqFactor_mem_seqSpan {k : ℕ} (t : Fin (seqRank A (k + 1))) :
    seqFactor A (k + 1) t ∈ seqSpan A (k + 1) := by
  by_cases hd : k + 1 = d
  · rw [seqFactor, dite_eq_right k.succ_ne_zero, dite_eq_left hd]
    exact mem_seqSpan_of_le A hd.ge
  · rw [seqFactor, dite_eq_right k.succ_ne_zero, dite_eq_right hd]
    exact Submodule.coe_mem _

/-- **Every tensor of order `d ≥ 1` is a tensor train** with the TT-ranks of its sequential
unfoldings ([golub2013matrix] (12.5.29); Oseledets–Tyrtyshnikov 2009): there are ranks `r` with
`r 0 = r d = 1` and `r k = rank A_{[0,k) × [k,d)}` for `0 < k < d`, and cores `G` with
`A = tensorTrain G d`. The cores express a basis of the column space of each sequential
unfolding, with the next index fixed, in a basis of the previous one (the book's successive SVDs
choose these bases). For `d = 0` the train is the constant `1`, so `d ≠ 0` is needed. -/
theorem exists_tensorTrain_of_ne_zero (hd : d ≠ 0) :
    ∃ (r : ℕ → ℕ) (h0 : r 0 = 1) (hr : r d = 1),
      (∀ k, 0 < k → k < d → r k = (A.unfold fun i : Fin d => (i : ℕ) < k).rank) ∧
      ∃ G : ∀ k, Fin (n k) → Matrix (Fin (r k)) (Fin (r (k + 1))) K,
        A = tensorTrain G d h0 hr := by
  have h0 : seqRank A 0 = 1 := by rw [seqRank, ite_eq_left (Or.inl rfl)]
  have hr : seqRank A d = 1 := by rw [seqRank, ite_eq_left (Or.inr rfl)]
  refine ⟨seqRank A, h0, hr, fun k hk hkd => ?_, ?_⟩
  · rw [seqRank_of_ne A hk.ne' hkd.ne, rank_unfold_eq_finrank_seqSpan A hkd.le]
  obtain ⟨G, hG⟩ := exists_ttPartial_eq_of_mem_span (d := d) h0 (seqFactor A)
    (fun t β => by rw [seqFactor, dite_eq_left rfl])
    (fun k hk t i => seqSpan_le_span_seqFactor A hk
      (snoc_mem_seqSpan A hk i (seqFactor_mem_seqSpan A t)))
  refine ⟨G, ext fun α => ?_⟩
  rw [tensorTrain_apply, hG d le_rfl, seqFactor, dite_eq_right hd, dite_eq_left rfl]

end Existence

end Tensor
