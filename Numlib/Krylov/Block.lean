import Numlib.Analysis.InnerProductSpace.GramSchmidt
import Numlib.Krylov.Hessenberg

/-!
# Block Krylov subspaces and the block Arnoldi process

The block Krylov subspace of a finite family `v : Fin p → M` is `Krylov.blockSubspace A v m = ⨆ i,
Krylov.subspace A (v i) m`, the span of the vectors `A^j (v i)` with `j < m`. Enumerating that
family in the order `(j, i)` — the `k`-th vector is `Krylov.blockSeq A v k = A^(k / p) (v (k % p))`,
so that consecutive blocks of `p` indices carry one more power of `A` — turns the block process into
an ordinary Gram–Schmidt orthonormalization: `BlockArnoldi.vec` is `gramSchmidtNormed` of
`Krylov.blockSeq`, which is Ruhe's variant of the block Arnoldi process ([saad2003iterative],
Algorithm 6.24). The block methods of [saad2011numerical], Ch. 6 use the same vectors.

Because `A (blockSeq A v k) = blockSeq A v (k + p)`, the vectors satisfy a banded Hessenberg
relation of bandwidth `p`, `A v_k = ∑_{i ≤ k + p} h_{ik} v_i`, that is `A V_m = V_{m+p} H̄_m`
([saad2011numerical], (6.129)–(6.130)). This is recorded as `Krylov.BandRelation`, which at `p = 1`
is `Krylov.HessenbergRelation` (`Krylov.bandRelation_one_iff`); for `p = 1` the whole file
specializes to `Numlib/Krylov/Arnoldi`, `BlockArnoldi.vec_one` and
`BlockArnoldi.hessenbergRelation_one`.

The blockwise algorithms ([saad2011numerical], Algorithms 6.22–6.23: a block orthogonalization
followed by a QR factorization of the resulting block) are described by their specification rather
than by an implementation. `IsBlockArnoldiBasis A v u` says that `u` is orthonormal and spans the
same flag as the enumerated block Krylov family — which any QR convention achieves — and
`BlockArnoldi.blockVec_eq_vec` says that such a `u` *is* `BlockArnoldi.vec` under the Gram–Schmidt
sign convention, and agrees with it up to unimodular scalars in general
(`IsBlockArnoldiBasis.exists_norm_eq_one_smul_vec`). That is [saad2011numerical] "mathematical
equivalence" of Algorithms 6.23 and 6.24, and it is the flag-uniqueness principle of
`Numlib/Analysis/InnerProductSpace/GramSchmidt`.

The residual formula `B - A X = V_{m+p} (E₁ R - H̄_m Y)` ([saad2011numerical], (6.135)) holds column
by column for any band relation, so block FOM and block GMRES — `IsGalerkin` and `IsMinRes` on the
block subspace, one right-hand side at a time — are the small banded systems (6.135)–(6.136):
`BlockArnoldi.isGalerkin_iff_mulVec_eq` and `BlockArnoldi.isMinRes_iff`. Ruhe's variant makes sense
at every step `m`, and `BlockArnoldi.span_vec_eq_blockSubspace` identifies the space it builds with
the block Krylov subspace exactly at the multiples of `p`.
-/

open InnerProductSpace

namespace Krylov

/-! ### The block Krylov sequence and the block Krylov subspaces -/

section BlockSequence

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A finite family `v : Fin p → M` read as a sequence indexed by `ℕ`, extended by `0` past `p`.
Auxiliary to `Krylov.blockSeq`, where it is what makes the enumeration total in `p`. -/
def blockPad {p : ℕ} (v : Fin p → M) (i : ℕ) : M := if h : i < p then v ⟨i, h⟩ else 0

/-- On its own range the padded family is the original one. -/
@[simp]
theorem blockPad_coe {p : ℕ} (v : Fin p → M) (i : Fin p) : blockPad v (i : ℕ) = v i := by
  simp [blockPad]

/-- The block Krylov sequence of `v : Fin p → M`, enumerated in the order `(j, i)`: the vector at
index `k = j * p + i` with `i < p` is `A^j (v i)`, so that each consecutive block of `p` indices
carries one more power of `A`. For `p = 0` the sequence is `0`. -/
def blockSeq (A : Module.End R M) {p : ℕ} (v : Fin p → M) (k : ℕ) : M :=
  (A ^ (k / p)) (blockPad v (k % p))

variable (A : Module.End R M) {p : ℕ} (v : Fin p → M)

/-- The enumeration: index `j * p + i` carries `A^j (v i)`. -/
theorem blockSeq_mul_add (j : ℕ) (i : Fin p) : blockSeq A v (j * p + (i : ℕ)) = (A ^ j) (v i) := by
  have hmod : (j * p + (i : ℕ)) % p = (i : ℕ) := by
    rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt]
  have hdiv : (j * p + (i : ℕ)) / p = j := by
    rw [mul_comm, Nat.mul_add_div i.pos, Nat.div_eq_of_lt i.isLt, Nat.add_zero]
  rw [blockSeq, hmod, hdiv, blockPad_coe]

/-- A degenerate family of no vectors generates nothing. -/
theorem blockSeq_of_p_eq_zero (v : Fin 0 → M) (k : ℕ) : blockSeq A v k = 0 := by
  simp [blockSeq, blockPad]

/-- One power of `A` shifts the enumeration by exactly one block. This single identity is what gives
the block Arnoldi vectors their bandwidth-`p` Hessenberg structure. -/
theorem apply_blockSeq (k : ℕ) : A (blockSeq A v k) = blockSeq A v (k + p) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · rw [blockSeq_of_p_eq_zero, blockSeq_of_p_eq_zero, map_zero]
  · rw [blockSeq, blockSeq, Nat.add_mod_right, Nat.add_div_right k hp, pow_succ']
    rfl

/-- For a single starting vector the block Krylov sequence is the Krylov sequence. -/
theorem blockSeq_one (v : Fin 1 → M) (k : ℕ) : blockSeq A v k = (A ^ k) (v 0) := by
  rw [blockSeq, Nat.div_one, Nat.mod_one]
  rfl

/-- The `m`-th block Krylov subspace `𝒦_m(A, v_0) + ⋯ + 𝒦_m(A, v_{p-1})` ([saad2003iterative],
§6.12). -/
def blockSubspace (A : Module.End R M) {p : ℕ} (v : Fin p → M) (m : ℕ) : Submodule R M :=
  ⨆ i, subspace A (v i) m

/-- Each individual Krylov subspace sits inside the block one. -/
theorem subspace_le_blockSubspace (i : Fin p) (m : ℕ) :
    subspace A (v i) m ≤ blockSubspace A v m := le_iSup (fun i => subspace A (v i) m) i

/-- The block Krylov subspaces grow with the number of steps. -/
theorem blockSubspace_mono : Monotone (blockSubspace A v) :=
  fun _ _ h => iSup_mono fun i => subspace_mono A (v i) h

/-- `A` maps the `m`-th block Krylov subspace into the `(m+1)`-st. -/
theorem map_blockSubspace_le (m : ℕ) :
    (blockSubspace A v m).map A ≤ blockSubspace A v (m + 1) := by
  rw [blockSubspace, Submodule.map_iSup]
  exact iSup_mono fun i => map_subspace_le A (v i) m

/-- No steps, no space. -/
@[simp]
theorem blockSubspace_zero : blockSubspace A v 0 = ⊥ := by
  simp [blockSubspace]

/-- For a single starting vector the block Krylov subspace is the Krylov subspace. -/
theorem blockSubspace_one (v : Fin 1 → M) (m : ℕ) :
    blockSubspace A v m = subspace A (v 0) m := iSup_unique _

/-- The generators of the block Krylov subspace, listed as a `Fin m × Fin p` family and as the first
`m * p` entries of the block Krylov sequence. -/
private theorem range_eq_blockSeq_image (m : ℕ) :
    (Set.range fun q : Fin m × Fin p => (A ^ (q.1 : ℕ)) (v q.2)) =
      blockSeq A v '' Set.Iio (m * p) := by
  ext x
  constructor
  · rintro ⟨⟨j, i⟩, rfl⟩
    refine ⟨(j : ℕ) * p + (i : ℕ), ?_, blockSeq_mul_add A v _ _⟩
    have h : ((j : ℕ) + 1) * p ≤ m * p := Nat.mul_le_mul_right p j.isLt
    have hi : (i : ℕ) < p := i.isLt
    calc (j : ℕ) * p + (i : ℕ) < (j : ℕ) * p + p := by omega
      _ = ((j : ℕ) + 1) * p := by ring
      _ ≤ m * p := h
  · rintro ⟨k, hk, rfl⟩
    have hp : 0 < p := by
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · simp at hk
      · exact hp
    have hkm : k / p < m := Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hk)
    refine ⟨(⟨k / p, hkm⟩, ⟨k % p, Nat.mod_lt k hp⟩), ?_⟩
    rw [blockSeq, blockPad]
    simp [Nat.mod_lt k hp]

/-- [saad2003iterative], §6.12: the block Krylov subspace is spanned by the `A^j (v i)` with `j <
m`. -/
theorem blockSubspace_eq_span (m : ℕ) :
    blockSubspace A v m =
      Submodule.span R (Set.range fun q : Fin m × Fin p => (A ^ (q.1 : ℕ)) (v q.2)) := by
  refine le_antisymm (iSup_le fun i => ?_) ?_
  · rw [subspace, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨(j, i), rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨⟨j, i⟩, rfl⟩
    exact subspace_le_blockSubspace A v i m (pow_apply_mem_subspace A (v i) j.isLt)

/-- The block Krylov subspace is spanned by the first `m * p` entries of the block Krylov sequence:
the form in which it matches Gram–Schmidt spans. -/
theorem blockSubspace_eq_span_image_Iio (m : ℕ) :
    blockSubspace A v m = Submodule.span R (blockSeq A v '' Set.Iio (m * p)) := by
  rw [blockSubspace_eq_span, range_eq_blockSeq_image]

end BlockSequence

/-! ### Band relations

`Krylov.HessenbergRelation` has bandwidth `1`. The block Arnoldi vectors satisfy the same relation
with bandwidth `p`, and the residual formula is the same computation. -/

section BandMatrix

variable {𝕜 : Type*}

/-- The `(m + p) × m` band Hessenberg matrix `H̄_m` of a coefficient function `h`
([saad2003iterative], (6.129)). -/
def bandOf (h : ℕ → ℕ → 𝕜) (p m : ℕ) : Matrix (Fin (m + p)) (Fin m) 𝕜 :=
  Matrix.of fun i j => h i j

/-- Bandwidth `1` is the ordinary rectangular Hessenberg matrix. -/
theorem bandOf_one (h : ℕ → ℕ → 𝕜) (m : ℕ) : bandOf h 1 m = hessenbergOf h m := rfl

end BandMatrix

section Band

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A sequence `v` satisfying the banded Hessenberg relation `A v_j = ∑_{i ≤ j+p} h i j v_i` of
bandwidth `p` ([saad2003iterative], (6.129)–(6.130)), without orthogonality. The case `p = 1` is
`Krylov.HessenbergRelation` (`Krylov.bandRelation_one_iff`). -/
structure BandRelation (A : E →ₗ[𝕜] E) (v : ℕ → E) (h : ℕ → ℕ → 𝕜) (p : ℕ) : Prop where
  /-- `A v_j` is a combination of `v_0, …, v_{j+p}` with the coefficients `h`. -/
  apply_eq : ∀ j, A (v j) = ∑ i ∈ Finset.range (j + p + 1), h i j • v i
  /-- The coefficients vanish more than `p` places below the diagonal. -/
  eq_zero_of_lt : ∀ i j, j + p < i → h i j = 0

/-- `E₁ g`: the vector of `𝕜^n` whose first `p` entries are `g 0, …, g_{p-1}` and whose remaining
entries vanish. It is the coordinate vector of a right-hand side expanded in the first block of
Arnoldi vectors ([saad2003iterative], (6.135)). -/
def firstBlockVec (g : ℕ → 𝕜) (p n : ℕ) : Fin n → 𝕜 := fun i => if (i : ℕ) < p then g i else 0

/-- A single right-hand side: `E₁ g` is `β e₁`. -/
theorem firstBlockVec_one (β : 𝕜) (n : ℕ) :
    firstBlockVec (fun _ => β) 1 n = firstVec β n := by
  funext i
  simp [firstBlockVec, firstVec]

/-- Bandwidth `1` is the ordinary Hessenberg relation, so `Arnoldi.hessenbergRelation` is the `p =
1` case of `BlockArnoldi.hessenbergRelation` (`BlockArnoldi.hessenbergRelation_one`). -/
theorem bandRelation_one_iff {A : E →ₗ[𝕜] E} {v : ℕ → E} {h : ℕ → ℕ → 𝕜} :
    BandRelation A v h 1 ↔ HessenbergRelation A v h :=
  ⟨fun hv => ⟨hv.apply_eq, hv.eq_zero_of_lt⟩, fun hv => ⟨hv.apply_eq, hv.eq_zero_of_lt⟩⟩

namespace BandRelation

variable {A : E →ₗ[𝕜] E} {v : ℕ → E} {h : ℕ → ℕ → 𝕜} {p : ℕ} (hv : BandRelation A v h p)
include hv

/-- The band expansion of `A v_j` may be taken over any range containing `j + p + 1`. -/
private theorem apply_eq_range (j n : ℕ) (hj : j + p + 1 ≤ n) :
    A (v j) = ∑ i ∈ Finset.range n, h i j • v i := by
  rw [hv.apply_eq j]
  refine Finset.sum_subset (by simpa using hj) fun i _ hi' => ?_
  rw [Finset.mem_range] at hi'
  rw [hv.eq_zero_of_lt i j (by omega), zero_smul]

/-- `A V_m = V_{m+p} H̄_m` ([saad2003iterative], (6.129)) in coordinates. -/
theorem apply_sum (m : ℕ) (y : Fin m → 𝕜) :
    A (∑ j, y j • v j) = ∑ i : Fin (m + p), (bandOf h p m).mulVec y i • v i := by
  rw [map_sum]
  have hleft : ∀ j : Fin m, A (y j • v j) = ∑ i : Fin (m + p), (y j * h i j) • v i := by
    intro j
    have hj : (j : ℕ) + p + 1 ≤ m + p := by have := j.isLt; omega
    rw [map_smul, hv.apply_eq_range (j : ℕ) (m + p) hj, Finset.smul_sum,
      ← Fin.sum_univ_eq_sum_range (fun i => y j • h i (j : ℕ) • v i) (m + p)]
    exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
  rw [Finset.sum_congr rfl fun j _ => hleft j, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [bandOf, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]

/-- [saad2003iterative], (6.135): if the starting residual is `V_p g`, the residual of `x₀ + V_m y`
is `V_{m+p} (E₁ g - H̄_m y)`. This is the block residual formula, read one right-hand side at a
time. -/
theorem residual_eq {b x₀ : E} {g : ℕ → 𝕜} (hr : b - A x₀ = ∑ i ∈ Finset.range p, g i • v i)
    (m : ℕ) (y : Fin m → 𝕜) :
    b - A (x₀ + ∑ j, y j • v j) =
      ∑ i : Fin (m + p), (firstBlockVec g p (m + p) - (bandOf h p m).mulVec y) i • v i := by
  have hsub : Finset.range p ⊆ Finset.range (m + p) := fun i hi =>
    Finset.mem_range.2 ((Finset.mem_range.1 hi).trans_le (Nat.le_add_left p m))
  have hzero : ∀ i ∈ Finset.range (m + p), i ∉ Finset.range p →
      (if i < p then g i else 0) • v i = 0 := by
    intro i _ hi
    rw [Finset.mem_range, not_lt] at hi
    simp [Nat.not_lt.2 hi]
  have hconv : ∑ i : Fin (m + p), firstBlockVec g p (m + p) i • v i
      = ∑ i ∈ Finset.range (m + p), (if i < p then g i else 0) • v i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => (if i < p then g i else 0) • v i) (m + p)]
    rfl
  have hfirst : ∑ i : Fin (m + p), firstBlockVec g p (m + p) i • v i
      = ∑ i ∈ Finset.range p, g i • v i := by
    rw [hconv, ← Finset.sum_subset hsub hzero]
    exact Finset.sum_congr rfl fun i hi => by simp [Finset.mem_range.1 hi]
  have hAx : A (x₀ + ∑ j, y j • v j) =
      A x₀ + ∑ i : Fin (m + p), (bandOf h p m).mulVec y i • v i := by
    rw [map_add, hv.apply_sum m y]
  have hsplit : ∑ i : Fin (m + p), (firstBlockVec g p (m + p) - (bandOf h p m).mulVec y) i • v i
      = (∑ i ∈ Finset.range p, g i • v i) -
        ∑ i : Fin (m + p), (bandOf h p m).mulVec y i • v i := by
    rw [← hfirst, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply, sub_smul]
  rw [hsplit, hAx, ← hr]
  abel

end BandRelation

end Band

end Krylov

open Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The specification of a block Arnoldi implementation ([saad2003iterative], Algorithms 6.22–6.23):
an orthonormal sequence `u` spanning the same flag as the block Krylov sequence. Every choice of QR
factorization inside a block produces such a sequence, and `BlockArnoldi.blockVec_eq_vec` identifies
it with the vectors of Ruhe's variant. -/
structure IsBlockArnoldiBasis (A : E →ₗ[𝕜] E) {p : ℕ} (v : Fin p → E) (u : ℕ → E) : Prop where
  /-- The vectors are orthonormal, so no breakdown has occurred. -/
  orthonormal : Orthonormal 𝕜 u
  /-- The first `k + 1` vectors span the first `k + 1` block Krylov directions. -/
  span_eq : ∀ k, Submodule.span 𝕜 (u '' Set.Iic k) =
    Submodule.span 𝕜 (blockSeq A v '' Set.Iic k)

namespace BlockArnoldi

/-! ### Gram–Schmidt with breakdown

The block Arnoldi vectors are `gramSchmidtNormed` of the block Krylov sequence, hence `0` from the
first linear dependence onwards. These auxiliary lemmas are the hypothesis-free facts about
`gramSchmidtNormed` that survive breakdown; they are stated for an arbitrary sequence because
nothing about the Krylov structure enters. -/

section GramSchmidtAux

/-- The companion of `Submodule.mem_orthogonal_span` with the roles of the two slots exchanged. -/
private theorem inner_eq_zero_of_mem_span {s : Set E} {x y : E}
    (hx : ∀ u ∈ s, inner 𝕜 u x = (0 : 𝕜)) (hy : y ∈ Submodule.span 𝕜 s) :
    inner 𝕜 x y = 0 :=
  Submodule.inner_left_of_mem_orthogonal hy (Submodule.mem_orthogonal_span.2 hx)

/-- Pythagoras for an orthonormal family: the norm of a combination is the `ℓ²` norm of the
coefficient vector. -/
private theorem norm_sum_smul_eq {n : ℕ} {u : Fin n → E} (hu : Orthonormal 𝕜 u) (c : Fin n → 𝕜) :
    ‖∑ i, c i • u i‖ = ‖(WithLp.toLp 2 c : EuclideanSpace 𝕜 (Fin n))‖ := by
  have hK : ((‖∑ i, c i • u i‖ : ℝ) : 𝕜) ^ 2 = ((∑ i, ‖c i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← inner_self_eq_norm_sq_to_K, sum_inner]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, hu.inner_right_sum c (Finset.mem_univ i), RCLike.conj_mul]
  have hsq : ‖∑ i, c i • u i‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by exact_mod_cast hK
  have hrhs : ‖(WithLp.toLp 2 c : EuclideanSpace 𝕜 (Fin n))‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 :=
    EuclideanSpace.norm_sq_eq _
  rw [← Real.sqrt_sq (norm_nonneg (∑ i, c i • u i)),
    ← Real.sqrt_sq (norm_nonneg (WithLp.toLp 2 c : EuclideanSpace 𝕜 (Fin n))), hsq, hrhs]

variable (f : ℕ → E)

/-- Distinct Gram–Schmidt vectors are orthogonal at every pair of indices and with no hypothesis:
past breakdown they are `0`, and the inner product vanishes for that reason. -/
private theorem inner_gsn_eq_zero {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (gramSchmidtNormed 𝕜 f i) (gramSchmidtNormed 𝕜 f j) = 0 := by
  simp [gramSchmidtNormed, inner_smul_left, inner_smul_right, gramSchmidt_orthogonal 𝕜 f h]

/-- The Gram–Schmidt flag: the first `n` normalized vectors span the first `n` entries of `f`. -/
private theorem span_gsn_Iio (n : ℕ) :
    Submodule.span 𝕜 (gramSchmidtNormed 𝕜 f '' Set.Iio n) =
      Submodule.span 𝕜 (f '' Set.Iio n) :=
  (span_gramSchmidtNormed f (Set.Iio n)).trans (span_gramSchmidt_Iio 𝕜 f n)

/-- What is left of `x` after subtracting its expansion in the first `n` Gram–Schmidt vectors is
orthogonal to all of them. -/
private theorem sub_sum_inner_smul_gsn_mem_orthogonal (x : E) (n : ℕ) :
    x - ∑ i ∈ Finset.range n, inner 𝕜 (gramSchmidtNormed 𝕜 f i) x • gramSchmidtNormed 𝕜 f i ∈
      (Submodule.span 𝕜 (gramSchmidtNormed 𝕜 f '' Set.Iio n))ᗮ := by
  refine Submodule.mem_orthogonal_span.2 ?_
  rintro _ ⟨k, hk, rfl⟩
  rw [inner_sub_right, inner_sum, Finset.sum_eq_single k]
  · rcases eq_or_ne (gramSchmidtNormed 𝕜 f k) 0 with h0 | h0
    · simp [h0]
    · rw [inner_smul_right, inner_self_eq_norm_sq_to_K, gramSchmidtNormed_unit_length' h0]
      simp
  · intro i _ hik
    rw [inner_smul_right, inner_gsn_eq_zero f (Ne.symm hik), mul_zero]
  · intro hk'
    exact absurd (Finset.mem_range.2 hk) hk'

/-- Every element of the span of the first `n` Gram–Schmidt vectors is its own orthonormal expansion
in them; the vectors that vanish after breakdown contribute nothing. -/
private theorem eq_sum_inner_smul_gsn {x : E} {n : ℕ}
    (hx : x ∈ Submodule.span 𝕜 (gramSchmidtNormed 𝕜 f '' Set.Iio n)) :
    x = ∑ i ∈ Finset.range n, inner 𝕜 (gramSchmidtNormed 𝕜 f i) x • gramSchmidtNormed 𝕜 f i := by
  have hy : x - ∑ i ∈ Finset.range n, inner 𝕜 (gramSchmidtNormed 𝕜 f i) x •
      gramSchmidtNormed 𝕜 f i ∈ Submodule.span 𝕜 (gramSchmidtNormed 𝕜 f '' Set.Iio n) :=
    Submodule.sub_mem _ hx (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, Finset.mem_range.1 hi, rfl⟩))
  have h0 := Submodule.inner_right_of_mem_orthogonal hy
    (sub_sum_inner_smul_gsn_mem_orthogonal f x n)
  rw [inner_self_eq_zero, sub_eq_zero] at h0
  exact h0

end GramSchmidtAux

/-! ### The block Arnoldi vectors -/

/-- The block Arnoldi vectors, Ruhe's variant ([saad2003iterative], Algorithm 6.24): the
Gram–Schmidt orthonormalization of the block Krylov sequence, one vector at a time. As for
`Arnoldi.vec`, the vectors are `0` after breakdown. -/
noncomputable def vec (A : E →ₗ[𝕜] E) {p : ℕ} (v : Fin p → E) : ℕ → E :=
  gramSchmidtNormed 𝕜 (blockSeq A v)

/-- The band Hessenberg coefficients `h i k = ⟪v_i, A v_k⟫` ([saad2003iterative], (6.130)). -/
noncomputable def coeff (A : E →ₗ[𝕜] E) {p : ℕ} (v : Fin p → E) (i k : ℕ) : 𝕜 :=
  inner 𝕜 (vec A v i) (A (vec A v k))

variable (A : E →ₗ[𝕜] E) {p : ℕ} (v : Fin p → E)

/-- The definition of the block Arnoldi vectors, in the form in which the Gram–Schmidt lemmas apply.
-/
theorem vec_eq_gramSchmidtNormed : vec A v = gramSchmidtNormed 𝕜 (blockSeq A v) := rfl

/-- The band coefficients are the inner products against `A v_k`. -/
theorem coeff_apply (i k : ℕ) : coeff A v i k = inner 𝕜 (vec A v i) (A (vec A v k)) := rfl

/-- The vectors that survive the process are unit vectors. -/
theorem norm_vec_eq_one_of_ne_zero {k : ℕ} (h : vec A v k ≠ 0) : ‖vec A v k‖ = 1 :=
  gramSchmidtNormed_unit_length' h

/-- Distinct block Arnoldi vectors are orthogonal, at every pair of indices and with no hypothesis:
past breakdown they are `0`. -/
theorem inner_vec_eq_zero {i j : ℕ} (h : i ≠ j) : inner 𝕜 (vec A v i) (vec A v j) = 0 :=
  inner_gsn_eq_zero _ h

/-- [saad2003iterative], §6.12: the block Arnoldi vectors that survive the process are orthonormal.
-/
theorem orthonormal_vec {n : ℕ} (h : ∀ k < n, vec A v k ≠ 0) :
    Orthonormal 𝕜 fun i : Fin n => vec A v (i : ℕ) :=
  ⟨fun i => norm_vec_eq_one_of_ne_zero A v (h i i.isLt),
    fun _ _ hij => inner_vec_eq_zero A v fun hc => hij (Fin.val_injective hc)⟩

/-- The block Arnoldi vectors span the same flag as the block Krylov sequence. -/
theorem span_vec (n : ℕ) :
    Submodule.span 𝕜 (vec A v '' Set.Iio n) = Submodule.span 𝕜 (blockSeq A v '' Set.Iio n) :=
  span_gsn_Iio _ n

/-- [saad2003iterative], §6.12: the first `m * p` block Arnoldi vectors span the `m`-th block Krylov
subspace. Ruhe's variant reaches the block Krylov subspaces exactly at the multiples of `p`. -/
theorem span_vec_eq_blockSubspace (m : ℕ) :
    Submodule.span 𝕜 (vec A v '' Set.Iio (m * p)) = blockSubspace A v m := by
  rw [span_vec, blockSubspace_eq_span_image_Iio]

/-- The `k`-th block Arnoldi vector only combines the first `k + 1` block Krylov directions. -/
theorem vec_mem_span (k : ℕ) :
    vec A v k ∈ Submodule.span 𝕜 (blockSeq A v '' Set.Iio (k + 1)) := by
  rw [← span_vec]
  exact Submodule.subset_span ⟨k, Nat.lt_succ_self k, rfl⟩

/-- `A` advances the block Krylov flag by exactly one block. -/
private theorem map_span_blockSeq_le (n : ℕ) :
    (Submodule.span 𝕜 (blockSeq A v '' Set.Iio n)).map A ≤
      Submodule.span 𝕜 (blockSeq A v '' Set.Iio (n + p)) := by
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, apply_blockSeq]
  exact Submodule.subset_span ⟨k + p, Nat.add_lt_add_right hk p, rfl⟩

/-- `A v_k` lies in the span of the first `k + p + 1` block Arnoldi vectors: the source of the
bandwidth-`p` structure. -/
theorem apply_vec_mem (k : ℕ) :
    A (vec A v k) ∈ Submodule.span 𝕜 (vec A v '' Set.Iio (k + p + 1)) := by
  rw [span_vec]
  have h := map_span_blockSeq_le A v (k + 1) ⟨_, vec_mem_span A v k, rfl⟩
  rwa [show k + 1 + p = k + p + 1 by omega] at h

/-- Band structure ([saad2003iterative], (6.130)): `h i k = 0` for `i > k + p`. -/
theorem coeff_eq_zero_of_lt {i k : ℕ} (h : k + p < i) : coeff A v i k = 0 := by
  rw [coeff_apply]
  refine inner_eq_zero_of_mem_span (s := vec A v '' Set.Iio i) ?_ ?_
  · rintro _ ⟨j, hj, rfl⟩
    exact inner_vec_eq_zero A v (Nat.ne_of_lt hj)
  · exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (by omega)))
      (apply_vec_mem A v k)

/-- [saad2003iterative], (6.129): `A v_k = ∑_{i ≤ k + p} h_{ik} v_i`. -/
theorem apply_vec (k : ℕ) :
    A (vec A v k) = ∑ i ∈ Finset.range (k + p + 1), coeff A v i k • vec A v i :=
  eq_sum_inner_smul_gsn (blockSeq A v) (apply_vec_mem A v k)

/-- [saad2003iterative], (6.129)–(6.130): the block Arnoldi vectors satisfy the band Hessenberg
relation of bandwidth `p`, `A V_m = V_{m+p} H̄_m`. -/
theorem hessenbergRelation : BandRelation A (vec A v) (coeff A v) p :=
  ⟨apply_vec A v, fun _ _ h => coeff_eq_zero_of_lt A v h⟩

/-! ### The case of one starting vector -/

/-- For a single starting vector, Ruhe's variant is Arnoldi's process. -/
theorem vec_one (A : E →ₗ[𝕜] E) (v : Fin 1 → E) : vec A v = Arnoldi.vec A (v 0) := by
  have h : blockSeq A v = fun k : ℕ => (A ^ k) (v 0) := funext (blockSeq_one A v)
  rw [vec_eq_gramSchmidtNormed, h]
  rfl

/-- For a single starting vector, the band coefficients are the Arnoldi coefficients. -/
theorem coeff_one (A : E →ₗ[𝕜] E) (v : Fin 1 → E) : coeff A v = Arnoldi.coeff A (v 0) := by
  funext i k
  rw [coeff_apply, vec_one]
  rfl

/-- `Arnoldi.hessenbergRelation` is the `p = 1` case of `BlockArnoldi.hessenbergRelation`. -/
theorem hessenbergRelation_one (A : E →ₗ[𝕜] E) (v : Fin 1 → E) :
    HessenbergRelation A (Arnoldi.vec A (v 0)) (Arnoldi.coeff A (v 0)) := by
  rw [← vec_one, ← coeff_one]
  exact bandRelation_one_iff.1 (hessenbergRelation A v)

end BlockArnoldi

/-! ### Equivalence of the blockwise algorithms with Ruhe's variant -/

namespace BlockArnoldi

variable {A : E →ₗ[𝕜] E} {p : ℕ} {v : Fin p → E} {u : ℕ → E}

open scoped ComplexOrder in
/-- [saad2003iterative], §6.12: Algorithms 6.23 (a block orthogonalization followed by a QR
factorization of the block) and 6.24 (Ruhe's variant) are mathematically equivalent. Under the
Gram–Schmidt sign convention `⟪u_k, f_k⟫ > 0` — the convention Gram–Schmidt QR itself satisfies —
the vectors coincide exactly; for any other QR they agree up to unimodular scalars, which is
`IsBlockArnoldiBasis.exists_norm_eq_one_smul_vec`. -/
theorem blockVec_eq_vec (hu : IsBlockArnoldiBasis A v u) {k : ℕ}
    (hpos : 0 < inner 𝕜 (u k) (blockSeq A v k)) : u k = vec A v k :=
  eq_gramSchmidtNormed_of_re_inner_pos hu.orthonormal hu.span_eq k hpos

end BlockArnoldi

namespace IsBlockArnoldiBasis

variable {A : E →ₗ[𝕜] E} {p : ℕ} {v : Fin p → E} {u : ℕ → E} (hu : IsBlockArnoldiBasis A v u)
include hu

/-- [saad2003iterative], §6.12: whatever QR factorization the blockwise algorithm uses, its vectors
are those of Ruhe's variant up to unimodular scalars. -/
theorem exists_norm_eq_one_smul_vec (k : ℕ) :
    ∃ ε : 𝕜, ‖ε‖ = 1 ∧ u k = ε • BlockArnoldi.vec A v k :=
  exists_norm_eq_one_smul_gramSchmidtNormed hu.orthonormal hu.span_eq k

/-- The flag condition at every index, not only at the block boundaries. -/
theorem span_eq_Iio (n : ℕ) :
    Submodule.span 𝕜 (u '' Set.Iio n) = Submodule.span 𝕜 (blockSeq A v '' Set.Iio n) := by
  cases n with
  | zero => simp
  | succ k =>
    rw [show Set.Iio (k + 1) = Set.Iic k from Set.ext fun _ => Nat.lt_succ_iff]
    exact hu.span_eq k

/-- Whatever the QR convention, the space built after `m` blocks is the `m`-th block Krylov
subspace. -/
theorem span_eq_blockSubspace (m : ℕ) :
    Submodule.span 𝕜 (u '' Set.Iio (m * p)) = blockSubspace A v m := by
  rw [hu.span_eq_Iio, ← blockSubspace_eq_span_image_Iio]

end IsBlockArnoldiBasis

namespace BlockArnoldi

/-! ### Block FOM and block GMRES in coordinates -/

variable (A : E →ₗ[𝕜] E) {p : ℕ} (v : Fin p → E)

/-- The `(m + p) × m` band Hessenberg matrix `H̄_m` of the block Arnoldi process
([saad2003iterative], (6.129)). -/
noncomputable def hessenberg (m : ℕ) : Matrix (Fin (m + p)) (Fin m) 𝕜 := bandOf (coeff A v) p m

/-- The square `m × m` band Hessenberg matrix `H_m`. -/
noncomputable def hessenbergSq (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜 :=
  hessenbergSqOf (coeff A v) m

/-- The first `n` block Arnoldi vectors as a `Fin n`-indexed family. -/
private theorem image_Iio_eq_range (n : ℕ) :
    vec A v '' Set.Iio n = Set.range fun i : Fin n => vec A v (i : ℕ) := by
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨(j : ℕ), j.isLt, rfl⟩

/-- The space Ruhe's variant has built after `n` steps, in coordinates. -/
theorem mem_span_vec_iff (n : ℕ) (x : E) :
    x ∈ Submodule.span 𝕜 (vec A v '' Set.Iio n) ↔
      ∃ y : Fin n → 𝕜, x = ∑ j, y j • vec A v (j : ℕ) := by
  rw [image_Iio_eq_range, Submodule.mem_span_range_iff_exists_fun]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

/-- A combination of the first `n` block Arnoldi vectors lies in the space they span. -/
theorem sum_smul_vec_mem (n : ℕ) (y : Fin n → 𝕜) :
    ∑ j, y j • vec A v (j : ℕ) ∈ Submodule.span 𝕜 (vec A v '' Set.Iio n) :=
  (mem_span_vec_iff A v n _).2 ⟨y, rfl⟩

/-- The block QR of the starting residuals, `R₀ = V_p R` ([saad2003iterative], (6.135)): every
vector of the first block Krylov subspace is a combination of the first `p` block Arnoldi vectors.
This is the shape of the hypothesis of `BlockArnoldi.residual_eq`. -/
theorem exists_coeffs_of_mem_blockSubspace_one {x : E} (hx : x ∈ blockSubspace A v 1) :
    ∃ g : ℕ → 𝕜, x = ∑ i ∈ Finset.range p, g i • vec A v i := by
  rw [← span_vec_eq_blockSubspace, one_mul] at hx
  obtain ⟨y, hy⟩ := (mem_span_vec_iff A v p x).1 hx
  refine ⟨fun i => if h : i < p then y ⟨i, h⟩ else 0, ?_⟩
  rw [hy, ← Fin.sum_univ_eq_sum_range
    (fun i => (if h : i < p then y ⟨i, h⟩ else 0) • vec A v i) p]
  exact Finset.sum_congr rfl fun j _ => by simp

variable {b x₀ : E} {g : ℕ → 𝕜} {m : ℕ}

/-- [saad2003iterative], (6.135): with the starting residual expanded in the first block, `R₀ = V_p
R`, the residual of `X₀ + V_m Y` is `V_{m+p} (E₁ R - H̄_m Y)`, read one right-hand side at a time.
-/
theorem residual_eq (hr : b - A x₀ = ∑ i ∈ Finset.range p, g i • vec A v i) (y : Fin m → 𝕜) :
    b - A (x₀ + ∑ j, y j • vec A v (j : ℕ)) =
      ∑ i : Fin (m + p), (firstBlockVec g p (m + p) - (hessenberg A v m).mulVec y) i •
        vec A v (i : ℕ) :=
  (hessenbergRelation A v).residual_eq hr m y

/-- [saad2003iterative], (6.136): as long as the process has not broken down, the residual norm of
the `i`-th right-hand side is the Euclidean norm of the small coordinate residual `ḡ - H̄_m y`. -/
theorem norm_residual_eq (hon : Orthonormal 𝕜 fun i : Fin (m + p) => vec A v (i : ℕ))
    (hr : b - A x₀ = ∑ i ∈ Finset.range p, g i • vec A v i) (y : Fin m → 𝕜) :
    ‖b - A (x₀ + ∑ j, y j • vec A v (j : ℕ))‖ =
      ‖(WithLp.toLp 2 (firstBlockVec g p (m + p) - (hessenberg A v m).mulVec y) :
        EuclideanSpace 𝕜 (Fin (m + p)))‖ := by
  rw [residual_eq A v hr y]
  exact norm_sum_smul_eq hon _

/-- Block FOM ([saad2003iterative], §6.12): the Galerkin condition over `x₀ + span {v_0, …,
v_{m-1}}` is the small square band system `H_m y = E₁ g`. -/
theorem isGalerkin_iff_mulVec_eq (hon : Orthonormal 𝕜 fun i : Fin (m + p) => vec A v (i : ℕ))
    (hr : b - A x₀ = ∑ i ∈ Finset.range p, g i • vec A v i) (y : Fin m → 𝕜) :
    IsGalerkin A b x₀ (Submodule.span 𝕜 (vec A v '' Set.Iio m))
        (x₀ + ∑ j, y j • vec A v (j : ℕ)) ↔
      (hessenbergSq A v m).mulVec y = firstBlockVec g p m := by
  set c := firstBlockVec g p (m + p) - (hessenberg A v m).mulVec y with hcdef
  have hres : b - A (x₀ + ∑ j, y j • vec A v (j : ℕ)) =
      ∑ i : Fin (m + p), c i • vec A v (i : ℕ) := residual_eq A v hr y
  have hinner : ∀ j : Fin m, inner 𝕜 (vec A v (j : ℕ))
      (∑ i : Fin (m + p), c i • vec A v (i : ℕ)) =
      c ⟨(j : ℕ), j.isLt.trans_le (Nat.le_add_right m p)⟩ :=
    fun j => hon.inner_right_sum c
      (Finset.mem_univ (⟨(j : ℕ), j.isLt.trans_le (Nat.le_add_right m p)⟩ : Fin (m + p)))
  have hcz : ∀ j : Fin m, c ⟨(j : ℕ), j.isLt.trans_le (Nat.le_add_right m p)⟩ =
      firstBlockVec g p m j - (hessenbergSq A v m).mulVec y j := fun _ => rfl
  constructor
  · intro hx
    funext j
    have hjmem : vec A v (j : ℕ) ∈ Submodule.span 𝕜 (vec A v '' Set.Iio m) :=
      Submodule.subset_span ⟨(j : ℕ), j.isLt, rfl⟩
    have h0 : inner 𝕜 (vec A v (j : ℕ)) (b - A (x₀ + ∑ k, y k • vec A v (k : ℕ))) = (0 : 𝕜) :=
      Submodule.inner_right_of_mem_orthogonal hjmem hx.orth
    rw [hres, hinner j, hcz j, sub_eq_zero] at h0
    exact h0.symm
  · intro hy
    refine ⟨by simpa using sum_smul_vec_mem A v m y, ?_⟩
    rw [hres]
    refine Submodule.mem_orthogonal_span.2 ?_
    rintro _ ⟨j, hj, rfl⟩
    have h1 := hinner ⟨j, hj⟩
    rw [hcz ⟨j, hj⟩, hy, sub_self] at h1
    exact h1

/-- Block GMRES ([saad2003iterative], (6.136)): minimizing the residual over `x₀ + span {v_0, …,
v_{m-1}}` is the small banded least-squares problem `min ‖E₁ g - H̄_m y‖₂`. -/
theorem isMinRes_iff (hon : Orthonormal 𝕜 fun i : Fin (m + p) => vec A v (i : ℕ))
    (hr : b - A x₀ = ∑ i ∈ Finset.range p, g i • vec A v i) (y : Fin m → 𝕜) :
    IsMinRes A b x₀ (Submodule.span 𝕜 (vec A v '' Set.Iio m))
        (x₀ + ∑ j, y j • vec A v (j : ℕ)) ↔
      ∀ z : Fin m → 𝕜,
        ‖(WithLp.toLp 2 (firstBlockVec g p (m + p) - (hessenberg A v m).mulVec y) :
          EuclideanSpace 𝕜 (Fin (m + p)))‖ ≤
          ‖(WithLp.toLp 2 (firstBlockVec g p (m + p) - (hessenberg A v m).mulVec z) :
            EuclideanSpace 𝕜 (Fin (m + p)))‖ := by
  constructor
  · intro hx z
    rw [← norm_residual_eq A v hon hr y, ← norm_residual_eq A v hon hr z]
    exact hx.min _ (by simpa using sum_smul_vec_mem A v m z)
  · intro h
    refine ⟨by simpa using sum_smul_vec_mem A v m y, fun w hw => ?_⟩
    obtain ⟨z, hz⟩ := (mem_span_vec_iff A v m _).1 hw
    have hwe : w = x₀ + ∑ j, z j • vec A v (j : ℕ) := by rw [← hz]; abel
    rw [hwe, norm_residual_eq A v hon hr y, norm_residual_eq A v hon hr z]
    exact h z

/-- Block FOM on the block Krylov subspace itself: `BlockArnoldi.isGalerkin_iff_mulVec_eq` at a
multiple of `p`, where the space Ruhe's variant has built is `Krylov.blockSubspace A v n`. -/
theorem isGalerkin_blockSubspace_iff {n : ℕ}
    (hon : Orthonormal 𝕜 fun i : Fin (n * p + p) => vec A v (i : ℕ))
    (hr : b - A x₀ = ∑ i ∈ Finset.range p, g i • vec A v i) (y : Fin (n * p) → 𝕜) :
    IsGalerkin A b x₀ (blockSubspace A v n) (x₀ + ∑ j, y j • vec A v (j : ℕ)) ↔
      (hessenbergSq A v (n * p)).mulVec y = firstBlockVec g p (n * p) := by
  rw [← span_vec_eq_blockSubspace]
  exact isGalerkin_iff_mulVec_eq A v hon hr y

/-- Block GMRES on the block Krylov subspace itself: `BlockArnoldi.isMinRes_iff` at a multiple of
`p`. -/
theorem isMinRes_blockSubspace_iff {n : ℕ}
    (hon : Orthonormal 𝕜 fun i : Fin (n * p + p) => vec A v (i : ℕ))
    (hr : b - A x₀ = ∑ i ∈ Finset.range p, g i • vec A v i) (y : Fin (n * p) → 𝕜) :
    IsMinRes A b x₀ (blockSubspace A v n) (x₀ + ∑ j, y j • vec A v (j : ℕ)) ↔
      ∀ z : Fin (n * p) → 𝕜,
        ‖(WithLp.toLp 2 (firstBlockVec g p (n * p + p) -
            (hessenberg A v (n * p)).mulVec y) : EuclideanSpace 𝕜 (Fin (n * p + p)))‖ ≤
          ‖(WithLp.toLp 2 (firstBlockVec g p (n * p + p) -
            (hessenberg A v (n * p)).mulVec z) : EuclideanSpace 𝕜 (Fin (n * p + p)))‖ := by
  rw [← span_vec_eq_blockSubspace]
  exact isMinRes_iff A v hon hr y

end BlockArnoldi
