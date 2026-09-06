import Numlib.Krylov.Block
import Numlib.LinearSolve.Projection.Basic
import NumlibSurface.SaadSparse.Chapter06.Section02

/-!
# Saad, §6.12: block Krylov methods

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003, §6.12.

The book's blocks are `n × p` matrices — `V_1` of starting vectors, `B` of right-hand sides, `X_0`
of initial guesses — and the family of their columns is what every statement here takes:
`blockCols` turns a matrix into that family. **Algorithm 6.24** (Ruhe's variant) is `ruhe`, the
Gram–Schmidt orthonormalization of the block Krylov sequence
`v_1, …, v_p, A v_1, …, A v_p, A² v_1, …`, one vector at a time; its coefficients are `ruheCoeff`
and its band Hessenberg matrices `HbarBlock` (`H̄_m` of (6.130), of size `(m + p) × m`) and
`HBlock` (`H_m`).

**Algorithms 6.22 and 6.23** are given by their specification rather than by an implementation,
because the book leaves the QR factorization of a block unspecified: `IsBlockArnoldi A v u` says
that `u` is orthonormal and spans the same flag as the block Krylov sequence, which every choice
of QR achieves. `ruhe_eq_blockArnoldiMGS` is then the book's "mathematical equivalence" of
Algorithms 6.23 and 6.24: such a `u` *is* `ruhe` under the Gram–Schmidt sign convention, and
agrees with it up to unimodular scalars in general; and at every multiple of `p` it spans the
block Krylov subspace `blockKrylov`, which is the sense in which the equivalence holds "when `m`
is a multiple of `p`".

The band relation (6.129)–(6.130) is the backbone's `Krylov.BandRelation`, of bandwidth `p`, and
not `Krylov.HessenbergRelation`, whose bandwidth is `1`. Block FOM and block GMRES are
`IsGalerkin` and `IsMinRes` over `x₀^{(i)} + span {v_1, …, v_m}`, one right-hand side at a time;
(6.135)–(6.136) and the coordinate forms `blockFOM_iff` and `blockGMRES_iff` are the small banded
systems they amount to. The Givens elimination with `p` rotations per column, for which the book
states no result, is not formalized.

Indices are `0`-based as elsewhere in Chapter 6: `ruhe A v j` is the book's `v_{j+1}`, and
`ruheCoeff A v i j` its `h_{i+1,j+1}`.
-/

open scoped ComplexOrder

namespace SaadSparse.Ch06

section Block

variable {n p : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### The block data -/

/-- The columns of one of the book's `n × p` blocks, as a family of vectors. The block Krylov
statements below take such families, which is the same data as the matrix. -/
noncomputable abbrev blockCols (B : Matrix (Fin n) (Fin p) 𝕜) (i : Fin p) : 𝔼 :=
  WithLp.toLp 2 fun j => B j i

/-- §6.12: the block Krylov subspace `𝒦_m(A, V_1) = 𝒦_m(A, v_1) + ⋯ + 𝒦_m(A, v_p)`, the span of
the `A^j v_i` with `j < m`. -/
noncomputable abbrev blockKrylov (A : Matrix (Fin n) (Fin n) 𝕜) (v : Fin p → 𝔼) (m : ℕ) :
    Submodule 𝕜 𝔼 :=
  Krylov.blockSubspace (op A) v m

/-! ### Algorithm 6.24: Ruhe's variant -/

/-- **Algorithm 6.24** (Ruhe's variant of the block Arnoldi process): the vectors
`v_1, v_2, …` obtained by orthonormalizing the block Krylov sequence
`v_1, …, v_p, A v_1, …, A v_p, A² v_1, …` one vector at a time — the `k`-th vector is `A v_{k-p}`
orthogonalized against `v_1, …, v_k` and normalized. `ruhe A v j` is the book's `v_{j+1}`; the
book's "if `‖w‖ = 0` then Stop" is Lean's `x / 0 = 0`, so all later vectors are `0`. -/
noncomputable abbrev ruhe (A : Matrix (Fin n) (Fin n) 𝕜) (v : Fin p → 𝔼) : ℕ → 𝔼 :=
  BlockArnoldi.vec (op A) v

/-- The coefficients `h_{ik} = (A v_k, v_i)` of **Algorithm 6.24**, lines 5 and 9. -/
noncomputable abbrev ruheCoeff (A : Matrix (Fin n) (Fin n) 𝕜) (v : Fin p → 𝔼) (i k : ℕ) : 𝕜 :=
  BlockArnoldi.coeff (op A) v i k

/-- **(6.130)**: the `(m + p) × m` band Hessenberg matrix `H̄_m` of Ruhe's variant. -/
noncomputable abbrev HbarBlock (A : Matrix (Fin n) (Fin n) 𝕜) (v : Fin p → 𝔼) (m : ℕ) :
    Matrix (Fin (m + p)) (Fin m) 𝕜 :=
  BlockArnoldi.hessenberg (op A) v m

/-- The square `m × m` band Hessenberg matrix `H_m` of Ruhe's variant, the first `m` rows of
`H̄_m`. -/
noncomputable abbrev HBlock (A : Matrix (Fin n) (Fin n) 𝕜) (v : Fin p → 𝔼) (m : ℕ) :
    Matrix (Fin m) (Fin m) 𝕜 :=
  BlockArnoldi.hessenbergSq (op A) v m

/-- **Algorithms 6.22 and 6.23**, by their specification: `u` is an orthonormal sequence spanning
the same flag as the block Krylov sequence. The book's block algorithms orthogonalize a block of
`p` vectors at a time and then factor the result, `W_j = V_{j+1} H_{j+1,j}`; the QR factorization
is left unspecified, and every choice of it produces exactly such a `u`. -/
def IsBlockArnoldi (A : Matrix (Fin n) (Fin n) 𝕜) (v : Fin p → 𝔼) (u : ℕ → 𝔼) : Prop :=
  IsBlockArnoldiBasis (op A) v u

/-- **(6.129)**: the vectors of Algorithms 6.22–6.23 are orthonormal — each block `V_i` is
orthonormal and the blocks are mutually orthogonal — and satisfy the band Hessenberg relation
`A U_m = U_m H_m + V_{m+1} H_{m+1,m} E_mᵀ`, which vector by vector is
`A u_k = ∑_{i ≤ k+p} h_{ik} u_i` and in coordinates is `A U_m = U_{m+p} H̄_m`.

The hypothesis `hpos` is the Gram–Schmidt sign convention on the block QR, the convention
Algorithm 6.23 (modified Gram–Schmidt) itself satisfies; without it the same conclusion holds
after the unimodular rescaling of `ruhe_eq_blockArnoldiMGS`. -/
theorem equation_6_129 {A : Matrix (Fin n) (Fin n) 𝕜} {v : Fin p → 𝔼} {u : ℕ → 𝔼}
    (hu : IsBlockArnoldi A v u)
    (hpos : ∀ k, 0 < inner 𝕜 (u k) (Krylov.blockSeq (op A) v k)) :
    Orthonormal 𝕜 u ∧
      (∀ k, op A (u k) = ∑ i ∈ Finset.range (k + p + 1), ruheCoeff A v i k • u i) ∧
      (∀ i k, k + p < i → ruheCoeff A v i k = 0) ∧
      ∀ (m : ℕ) (y : Fin m → 𝕜),
        op A (∑ j, y j • u (j : ℕ)) =
          ∑ i : Fin (m + p), (HbarBlock A v m).mulVec y i • u (i : ℕ) := by
  have hue : u = ruhe A v := funext fun k => BlockArnoldi.blockVec_eq_vec hu (hpos k)
  subst hue
  exact ⟨hu.orthonormal, BlockArnoldi.apply_vec (op A) v,
    fun _ _ h => BlockArnoldi.coeff_eq_zero_of_lt (op A) v h,
    fun m y => (BlockArnoldi.hessenbergRelation (op A) v).apply_sum m y⟩

/-- **§6.12**: Algorithms 6.23 and 6.24 are mathematically equivalent. Whatever QR factorization
the blockwise algorithm uses, its vectors are those of Ruhe's variant up to unimodular scalars,
and they coincide exactly under the Gram–Schmidt sign convention; when `m` is a multiple of `p`
the two therefore build the same space, the block Krylov subspace `𝒦_{m/p}(A, V_1)`. -/
theorem ruhe_eq_blockArnoldiMGS {A : Matrix (Fin n) (Fin n) 𝕜} {v : Fin p → 𝔼} {u : ℕ → 𝔼}
    (hu : IsBlockArnoldi A v u) :
    (∀ k, 0 < inner 𝕜 (u k) (Krylov.blockSeq (op A) v k) → u k = ruhe A v k) ∧
      (∀ k, ∃ ε : 𝕜, ‖ε‖ = 1 ∧ u k = ε • ruhe A v k) ∧
      ∀ m : ℕ, Submodule.span 𝕜 (u '' Set.Iio (m * p)) = blockKrylov A v m :=
  ⟨fun _ hpos => BlockArnoldi.blockVec_eq_vec hu hpos,
    hu.exists_norm_eq_one_smul_vec, hu.span_eq_blockSubspace⟩

/-- **(6.130)**: for Ruhe's variant, `A v_k = ∑_{i=1}^{k+p} h_{ik} v_i` with `h_{ik} = 0` for
`i > k + p`, that is `A V_m = V_{m+p} H̄_m`. -/
theorem equation_6_130 (A : Matrix (Fin n) (Fin n) 𝕜) (v : Fin p → 𝔼) :
    (∀ k, op A (ruhe A v k) =
        ∑ i ∈ Finset.range (k + p + 1), ruheCoeff A v i k • ruhe A v i) ∧
      (∀ i k, k + p < i → ruheCoeff A v i k = 0) ∧
      ∀ (m : ℕ) (y : Fin m → 𝕜),
        op A (∑ j, y j • ruhe A v (j : ℕ)) =
          ∑ i : Fin (m + p), (HbarBlock A v m).mulVec y i • ruhe A v (i : ℕ) :=
  ⟨BlockArnoldi.apply_vec (op A) v, fun _ _ h => BlockArnoldi.coeff_eq_zero_of_lt (op A) v h,
    fun m y => (BlockArnoldi.hessenbergRelation (op A) v).apply_sum m y⟩

/-- **§6.12**: the first `m p` vectors of Ruhe's variant span the `m`-th block Krylov subspace, so
Algorithm 6.24 reaches the spaces of Algorithm 6.22 exactly at the multiples of `p`. -/
theorem span_ruhe_eq_blockKrylov (A : Matrix (Fin n) (Fin n) 𝕜) (v : Fin p → 𝔼) (m : ℕ) :
    Submodule.span 𝕜 (ruhe A v '' Set.Iio (m * p)) = blockKrylov A v m :=
  BlockArnoldi.span_vec_eq_blockSubspace (op A) v m

/-! ### Block FOM and block GMRES -/

/-- **§6.12**: the block GMRES approximation to the `i`-th right-hand side, the minimal-residual
approximation over `x_0^{(i)} + span {v_1, …, v_m}`. At `m = k p` the search space is the block
Krylov subspace `𝒦_k(A, V_1)` (`span_ruhe_eq_blockKrylov`). -/
def IsBlockGMRES (A : Matrix (Fin n) (Fin n) 𝕜) (B X₀ v : Fin p → 𝔼) (m : ℕ) (i : Fin p)
    (x : 𝔼) : Prop :=
  IsMinRes (op A) (B i) (X₀ i) (Submodule.span 𝕜 (ruhe A v '' Set.Iio m)) x

/-- **§6.12**: the block FOM approximation to the `i`-th right-hand side, the Galerkin
approximation over `x_0^{(i)} + span {v_1, …, v_m}`. -/
def IsBlockFOM (A : Matrix (Fin n) (Fin n) 𝕜) (B X₀ v : Fin p → 𝔼) (m : ℕ) (i : Fin p)
    (x : 𝔼) : Prop :=
  IsGalerkin (op A) (B i) (X₀ i) (Submodule.span 𝕜 (ruhe A v '' Set.Iio m)) x

variable {A : Matrix (Fin n) (Fin n) 𝕜} {B X₀ v : Fin p → EuclideanSpace 𝕜 (Fin n)}
  {g : ℕ → 𝕜} {m : ℕ} {i : Fin p}

/-- **§6.12**: the block QR of the initial residual block, `R_0 = V_p R` — every column of `R_0`
lies in `𝒦_1(A, V_1)`, hence is a combination of the first `p` vectors of Ruhe's variant. This is
the shape of the hypothesis `hr` of (6.135)–(6.136). -/
theorem exists_initial_residual_coeffs (hr : B i - op A (X₀ i) ∈ blockKrylov A v 1) :
    ∃ g : ℕ → 𝕜, B i - op A (X₀ i) = ∑ k ∈ Finset.range p, g k • ruhe A v k :=
  BlockArnoldi.exists_coeffs_of_mem_blockSubspace_one (op A) v hr

/-- **(6.135)–(6.136)**: with the initial residual block expanded as `R_0 = V_p R`, the residual
of `X = X_0 + V_m Y` is `B - A X = V_{m+p}(E_1 R - H̄_m Y)`; and as long as the process has not
broken down, `‖b^{(i)} - A x^{(i)}‖₂ = ‖ḡ^{(i)} - H̄_m y^{(i)}‖₂`. Here `ḡ^{(i)} = E_1 R e_i` is
`Krylov.firstBlockVec g p (m + p)`. -/
theorem equation_6_136 (hon : Orthonormal 𝕜 fun k : Fin (m + p) => ruhe A v (k : ℕ))
    (hr : B i - op A (X₀ i) = ∑ k ∈ Finset.range p, g k • ruhe A v k) (y : Fin m → 𝕜) :
    (B i - op A (X₀ i + ∑ j, y j • ruhe A v (j : ℕ)) =
        ∑ k : Fin (m + p),
          ((Krylov.firstBlockVec g p (m + p) - (HbarBlock A v m).mulVec y :
            Fin (m + p) → 𝕜)) k • ruhe A v (k : ℕ)) ∧
      ‖B i - op A (X₀ i + ∑ j, y j • ruhe A v (j : ℕ))‖ =
        ‖(WithLp.toLp 2 (Krylov.firstBlockVec g p (m + p) - (HbarBlock A v m).mulVec y) :
          EuclideanSpace 𝕜 (Fin (m + p)))‖ :=
  ⟨BlockArnoldi.residual_eq (op A) v hr y, BlockArnoldi.norm_residual_eq (op A) v hon hr y⟩

/-- **§6.12**: block FOM in coordinates — the Galerkin condition over
`x_0^{(i)} + span {v_1, …, v_m}` is the small square band system `H_m y = ḡ^{(i)}`. -/
theorem blockFOM_iff (hon : Orthonormal 𝕜 fun k : Fin (m + p) => ruhe A v (k : ℕ))
    (hr : B i - op A (X₀ i) = ∑ k ∈ Finset.range p, g k • ruhe A v k) (y : Fin m → 𝕜) :
    IsBlockFOM A B X₀ v m i (X₀ i + ∑ j, y j • ruhe A v (j : ℕ)) ↔
      (HBlock A v m).mulVec y = Krylov.firstBlockVec g p m :=
  BlockArnoldi.isGalerkin_iff_mulVec_eq (op A) v hon hr y

/-- **(6.136)**: block GMRES in coordinates — minimizing the residual over
`x_0^{(i)} + span {v_1, …, v_m}` is the small banded least-squares problem
`min_y ‖ḡ^{(i)} - H̄_m y‖₂`. -/
theorem blockGMRES_iff (hon : Orthonormal 𝕜 fun k : Fin (m + p) => ruhe A v (k : ℕ))
    (hr : B i - op A (X₀ i) = ∑ k ∈ Finset.range p, g k • ruhe A v k) (y : Fin m → 𝕜) :
    IsBlockGMRES A B X₀ v m i (X₀ i + ∑ j, y j • ruhe A v (j : ℕ)) ↔
      ∀ z : Fin m → 𝕜,
        ‖(WithLp.toLp 2 (Krylov.firstBlockVec g p (m + p) - (HbarBlock A v m).mulVec y) :
          EuclideanSpace 𝕜 (Fin (m + p)))‖ ≤
          ‖(WithLp.toLp 2 (Krylov.firstBlockVec g p (m + p) - (HbarBlock A v m).mulVec z) :
            EuclideanSpace 𝕜 (Fin (m + p)))‖ :=
  BlockArnoldi.isMinRes_iff (op A) v hon hr y

end Block

end SaadSparse.Ch06
