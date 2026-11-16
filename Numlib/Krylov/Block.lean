/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.GramSchmidt
import Numlib.Analysis.InnerProductSpace.Orthonormal
import Numlib.Krylov.Hessenberg

/-!
# Block Krylov subspaces and the block Arnoldi process

Let $A$ be a linear operator on a module $M$, and let $v_0, \dots, v_{p-1} \in M$ be a family of $p$
starting vectors. The $m$-th **block Krylov subspace** is
$$\mathcal{K}_m(A, \{v_i\}) = \mathcal{K}_m(A, v_0) + \cdots + \mathcal{K}_m(A, v_{p-1}) =
  \operatorname{span}\{A^j v_i : j < m, \ i < p\}.$$
Enumerate its generators in the order $(j, i)$, as the **block Krylov sequence**
$f_{jp + i} = A^j v_i$, so that each block of $p$ consecutive indices carries one more power of $A$.
In an inner product space, the Gram–Schmidt orthonormalization $q_0, q_1, \dots$ of this sequence is
Ruhe's variant of the block Arnoldi process ([saad2003iterative], §6.12, Algorithm 6.24). The block
methods of [saad2011numerical], Ch. 6 use the same vectors.

Since $A f_k = f_{k+p}$, the vectors satisfy a band Hessenberg relation of bandwidth $p$,
$A q_k = \sum_{i \le k + p} h_{ik} q_i$, that is $A Q_m = Q_{m+p} \bar H_m$ ([saad2003iterative],
(6.129)–(6.130)). The residual formula $b - A(x_0 + Q_m y) = Q_{m+p}(E_1 g - \bar H_m y)$ of (6.135)
follows, and with it block FOM and block GMRES reduce to a small square band system and a small band
least-squares problem (6.136). For symmetric $A$ the process is block Lanczos, and $H_m$ is a
Hermitian band matrix of bandwidth $p$, the block tridiagonal matrix $T_m$ of [golub2013matrix],
(10.3.7). For $p = 1$ everything reduces to the Arnoldi process of `Numlib.Krylov.Arnoldi`.

## Main definitions

* `Krylov.blockSeq`: the block Krylov sequence $f_{jp+i} = A^j v_i$.
* `Krylov.blockSubspace`: the block Krylov subspace $\mathcal{K}_m(A, v_0) + \cdots +
  \mathcal{K}_m(A, v_{p-1})$.
* `Krylov.BandRelation`: a sequence $(q_j)$ satisfies $A q_j = \sum_{i \le j + p} h_{ij} q_i$ with
  $h_{ij} = 0$ for $i > j + p$.
* `Krylov.bandOf`, `Krylov.firstBlockVec`: the $(m + p) \times m$ band Hessenberg matrix of a
  coefficient array, and the vector $E_1 g$.
* `IsBlockArnoldiBasis`: the specification of a blockwise block Arnoldi algorithm, an orthonormal
  sequence with the same flag of spans as the block Krylov sequence.
* `BlockArnoldi.vec`, `BlockArnoldi.coeff`: the vectors $q_k$ of Ruhe's variant and the coefficients
  $h_{ik} = \langle q_i, A q_k \rangle$.
* `BlockArnoldi.hessenberg`, `BlockArnoldi.hessenbergSq`: the band Hessenberg matrices $\bar H_m$
  and $H_m$.

## Main results

* `Krylov.blockSubspace_eq_span`: the block Krylov subspace is spanned by the $A^j v_i$ with
  $j < m$.
* `BlockArnoldi.span_vec_eq_blockSubspace`: the first $mp$ vectors $q_k$ span
  $\mathcal{K}_m(A, \{v_i\})$.
* `BlockArnoldi.hessenbergRelation`: the vectors $q_k$ satisfy the band relation of bandwidth $p$.
* `BlockArnoldi.blockVec_eq_vec`, `IsBlockArnoldiBasis.exists_norm_eq_one_smul_vec`: a blockwise
  algorithm produces the vectors of Ruhe's variant, exactly under the Gram–Schmidt sign convention
  and up to unimodular scalars in general.
* `BlockArnoldi.residual_eq`, `BlockArnoldi.norm_residual_eq`: the residual formula (6.135) and its
  norm (6.136).
* `BlockArnoldi.isGalerkin_iff_mulVec_eq`, `BlockArnoldi.isMinResidual_iff`: block FOM is the system
  $H_m y = E_1 g$, and block GMRES is the minimization of $\|E_1 g - \bar H_m y\|_2$.
* `BlockArnoldi.isHermitian_hessenbergSq_of_isSymmetric`,
  `BlockArnoldi.hasBandwidth_hessenbergSq_of_isSymmetric`: for symmetric $A$, $H_m$ is Hermitian
  with upper and lower bandwidth $p$.

## Implementation notes

* The enumeration in the order $(j, i)$ turns the block process into an ordinary Gram–Schmidt
  orthonormalization of one sequence. `BlockArnoldi.vec` is `InnerProductSpace.gramSchmidtNormed` of
  `Krylov.blockSeq`, so $q_k = 0$ exactly when $f_k$ is a linear combination of
  $f_0, \dots, f_{k-1}$. Unlike for `Arnoldi.vec`, a later vector can be nonzero again: for $p = 2$,
  $v_0 = 0$ and $v_1 \neq 0$, the vector $q_0$ is $0$ but $q_1$ is not.
* Ruhe's variant makes sense at every step, and the space that it builds equals a block Krylov
  subspace exactly at the multiples of $p$.
* The blockwise algorithms ([saad2003iterative], Algorithms 6.22–6.23: a block orthogonalization
  followed by a QR factorization of the new block) are described by their specification
  `IsBlockArnoldiBasis`, which any QR convention satisfies, and not by an implementation. Their
  equivalence with Ruhe's variant is the uniqueness of an orthonormal basis of a flag, from
  `Numlib.Analysis.InnerProductSpace.GramSchmidt`.
* Block FOM and block GMRES are stated one right-hand side at a time, as `IsGalerkin` and
  `IsMinResidual` on the space built by the process.
* At $p = 1$, `Krylov.BandRelation` is `Krylov.HessenbergRelation` (`Krylov.bandRelation_one_iff`),
  and the block process is the Arnoldi process (`BlockArnoldi.vec_one`,
  `BlockArnoldi.hessenbergRelation_one`).
-/

open InnerProductSpace

namespace Krylov

/-! ### The block Krylov sequence and the block Krylov subspaces -/

section BlockSequence

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A finite family $v_0, \dots, v_{p-1}$ read as a sequence indexed by $\mathbb{N}$: the $i$-th
term is $v_i$ for $i < p$ and $0$ for $i \ge p$. -/
def blockPad {p : ℕ} (v : Fin p → M) (i : ℕ) : M := if h : i < p then v ⟨i, h⟩ else 0

/-- On the indices $i < p$, the padded sequence takes the value $v_i$. -/
@[simp]
theorem blockPad_coe {p : ℕ} (v : Fin p → M) (i : Fin p) : blockPad v (i : ℕ) = v i := by
  simp [blockPad]

/-- The **block Krylov sequence** of a family $v_0, \dots, v_{p-1}$ under an operator $A$,
enumerated in the order $(j, i)$: for $k = jp + i$ with $i < p$, the term of index $k$ is
$$f_{jp + i} = A^j v_i.$$
Each consecutive block of $p$ indices carries one more power of $A$. For $p = 0$ the sequence is
$0$.

The definition is $f_k = A^{\lfloor k / p \rfloor} v_{k \bmod p}$, with `Krylov.blockPad` giving
the value $0$ in the degenerate case $p = 0$. -/
def blockSeq (A : Module.End R M) {p : ℕ} (v : Fin p → M) (k : ℕ) : M :=
  (A ^ (k / p)) (blockPad v (k % p))

variable (A : Module.End R M) {p : ℕ} (v : Fin p → M)

/-- The enumeration of the block Krylov sequence: for every $j \ge 0$ and $i < p$,
$$f_{jp + i} = A^j v_i.$$
-/
theorem blockSeq_mul_add (j : ℕ) (i : Fin p) : blockSeq A v (j * p + (i : ℕ)) = (A ^ j) (v i) := by
  have hmod : (j * p + (i : ℕ)) % p = (i : ℕ) := by
    rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt]
  have hdiv : (j * p + (i : ℕ)) / p = j := by
    rw [mul_comm, Nat.mul_add_div i.pos, Nat.div_eq_of_lt i.isLt, Nat.add_zero]
  rw [blockSeq, hmod, hdiv, blockPad_coe]

/-- For an empty family ($p = 0$), every term of the block Krylov sequence is $0$. -/
theorem blockSeq_of_p_eq_zero (v : Fin 0 → M) (k : ℕ) : blockSeq A v k = 0 := by
  simp [blockSeq, blockPad]

/-- One power of $A$ shifts the block Krylov sequence by exactly one block: $A f_k = f_{k+p}$ for
every $k$.

This identity gives the block Arnoldi vectors their band Hessenberg structure of bandwidth $p$. -/
theorem apply_blockSeq (k : ℕ) : A (blockSeq A v k) = blockSeq A v (k + p) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · rw [blockSeq_of_p_eq_zero, blockSeq_of_p_eq_zero, map_zero]
  · rw [blockSeq, blockSeq, Nat.add_mod_right, Nat.add_div_right k hp, pow_succ']
    rfl

/-- For a single starting vector ($p = 1$), the block Krylov sequence is the Krylov sequence:
$f_k = A^k v_0$. -/
theorem blockSeq_one (v : Fin 1 → M) (k : ℕ) : blockSeq A v k = (A ^ k) (v 0) := by
  rw [blockSeq, Nat.div_one, Nat.mod_one]
  rfl

/-- The $m$-th **block Krylov subspace** of a family $v_0, \dots, v_{p-1}$ under an operator $A$:
$$\mathcal{K}_m(A, \{v_i\}) = \mathcal{K}_m(A, v_0) + \cdots + \mathcal{K}_m(A, v_{p-1}).$$
This is the block Krylov subspace of [saad2003iterative], §6.12.

The sum is the supremum `⨆ i, Krylov.subspace A (v i) m` of submodules. -/
def blockSubspace (A : Module.End R M) {p : ℕ} (v : Fin p → M) (m : ℕ) : Submodule R M :=
  ⨆ i, subspace A (v i) m

/-- Each Krylov subspace of the family lies in the block Krylov subspace: $\mathcal{K}_m(A, v_i)
\subseteq \mathcal{K}_m(A, \{v_i\})$ for every $i < p$ and every $m$. -/
theorem subspace_le_blockSubspace (i : Fin p) (m : ℕ) :
    subspace A (v i) m ≤ blockSubspace A v m := le_iSup (fun i => subspace A (v i) m) i

/-- The block Krylov subspaces grow with the number of steps: $\mathcal{K}_m(A, \{v_i\}) \subseteq
\mathcal{K}_{m'}(A, \{v_i\})$ for $m \le m'$. -/
theorem blockSubspace_mono : Monotone (blockSubspace A v) :=
  fun _ _ h => iSup_mono fun i => subspace_mono A (v i) h

/-- The operator $A$ maps the $m$-th block Krylov subspace into the next one:
$$A\, \mathcal{K}_m(A, \{v_i\}) \subseteq \mathcal{K}_{m+1}(A, \{v_i\}).$$
-/
theorem map_blockSubspace_le (m : ℕ) :
    (blockSubspace A v m).map A ≤ blockSubspace A v (m + 1) := by
  rw [blockSubspace, Submodule.map_iSup]
  exact iSup_mono fun i => map_subspace_le A (v i) m

/-- The block Krylov subspace after zero steps is the zero subspace. -/
@[simp]
theorem blockSubspace_zero : blockSubspace A v 0 = ⊥ := by
  simp [blockSubspace]

/-- For a single starting vector ($p = 1$), the block Krylov subspace is the Krylov subspace:
$\mathcal{K}_m(A, \{v_0\}) = \mathcal{K}_m(A, v_0)$. -/
theorem blockSubspace_one (v : Fin 1 → M) (m : ℕ) :
    blockSubspace A v m = subspace A (v 0) m := iSup_unique _

/-- The generators $A^j v_i$ with $j < m$ and $i < p$ of the block Krylov subspace are the first
$mp$ terms of the block Krylov sequence. -/
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

/-- The block Krylov subspace is spanned by the vectors $A^j v_i$ with $j < m$:
$$\mathcal{K}_m(A, \{v_i\}) = \operatorname{span}\{A^j v_i : j < m, \ i < p\}.$$
This is the description of the block Krylov subspace in [saad2003iterative], §6.12. -/
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

/-- The block Krylov subspace is spanned by the first $mp$ terms of the block Krylov sequence:
$$\mathcal{K}_m(A, \{v_i\}) = \operatorname{span}\{f_0, \dots, f_{mp - 1}\}.$$

This is the form in which the block Krylov subspace matches the spans of a Gram–Schmidt process. -/
theorem blockSubspace_eq_span_image_Iio (m : ℕ) :
    blockSubspace A v m = Submodule.span R (blockSeq A v '' Set.Iio (m * p)) := by
  rw [blockSubspace_eq_span, range_eq_blockSeq_image]

end BlockSequence

/-!
### Band relations

The Hessenberg relation `Krylov.HessenbergRelation` has bandwidth $1$. The block Arnoldi vectors
satisfy the same kind of relation with bandwidth $p$, and the residual formula has the same proof.
-/

section BandMatrix

variable {𝕜 : Type*}

/-- The $(m + p) \times m$ **band Hessenberg matrix** $\bar H_m$ of a coefficient array $(h_{ij})$:
its entry at $(i, j)$ is $h_{ij}$, for $i < m + p$ and $j < m$. This is the matrix $\bar H_m$ of
[saad2003iterative], (6.129)–(6.130). -/
def bandOf (h : ℕ → ℕ → 𝕜) (p m : ℕ) : Matrix (Fin (m + p)) (Fin m) 𝕜 :=
  Matrix.of fun i j => h i j

/-- For bandwidth $p = 1$, the band Hessenberg matrix is the rectangular $(m + 1) \times m$
Hessenberg matrix `Krylov.hessenbergOf`. -/
theorem bandOf_one (h : ℕ → ℕ → 𝕜) (m : ℕ) : bandOf h 1 m = hessenbergOf h m := rfl

end BandMatrix

section Band

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A **band relation** of bandwidth $p$ for an operator $A$, a sequence $(v_j)$ and a coefficient
array $(h_{ij})$:
$$A v_j = \sum_{i \le j + p} h_{ij} v_i \quad \text{for every } j, \qquad h_{ij} = 0 \quad
  \text{for } i > j + p.$$
This is the relation (6.129)–(6.130) of [saad2003iterative], without orthogonality of the $v_j$.

The case $p = 1$ is `Krylov.HessenbergRelation` (`Krylov.bandRelation_one_iff`). -/
structure BandRelation (A : E →ₗ[𝕜] E) (v : ℕ → E) (h : ℕ → ℕ → 𝕜) (p : ℕ) : Prop where
  /-- The expansion $A v_j = \sum_{i \le j + p} h_{ij} v_i$. -/
  apply_eq : ∀ j, A (v j) = ∑ i ∈ Finset.range (j + p + 1), h i j • v i
  /-- The coefficients vanish more than $p$ places below the diagonal: $h_{ij} = 0$ for $i > j + p$.
  -/
  eq_zero_of_lt : ∀ i j, j + p < i → h i j = 0

/-- The vector $E_1 g \in \mathbb{K}^n$ of a sequence $(g_i)$: its first $p$ entries are
$g_0, \dots, g_{p-1}$, and its other entries are $0$. If $n < p$, only the first $n$ of the
$g_i$ appear.

It is the coordinate vector of a right-hand side that is expanded in the first block of Arnoldi
vectors, as in [saad2003iterative], (6.135). -/
def firstBlockVec (g : ℕ → 𝕜) (p n : ℕ) : Fin n → 𝕜 := fun i => if (i : ℕ) < p then g i else 0

/-- For a single right-hand side ($p = 1$) with the constant sequence $g_i = \beta$, the vector
$E_1 g$ is $\beta e_1$. -/
theorem firstBlockVec_one (β : 𝕜) (n : ℕ) :
    firstBlockVec (fun _ => β) 1 n = firstVec β n := by
  funext i
  simp [firstBlockVec, firstVec]

/-- A band relation of bandwidth $1$ is the same as a Hessenberg relation:
`Krylov.BandRelation A v h 1` holds if and only if `Krylov.HessenbergRelation A v h` holds.

So `Arnoldi.hessenbergRelation` is the case $p = 1$ of `BlockArnoldi.hessenbergRelation`
(`BlockArnoldi.hessenbergRelation_one`). -/
theorem bandRelation_one_iff {A : E →ₗ[𝕜] E} {v : ℕ → E} {h : ℕ → ℕ → 𝕜} :
    BandRelation A v h 1 ↔ HessenbergRelation A v h :=
  ⟨fun hv => ⟨hv.apply_eq, hv.eq_zero_of_lt⟩, fun hv => ⟨hv.apply_eq, hv.eq_zero_of_lt⟩⟩

namespace BandRelation

variable {A : E →ₗ[𝕜] E} {v : ℕ → E} {h : ℕ → ℕ → 𝕜} {p : ℕ} (hv : BandRelation A v h p)
include hv

/-- In a band relation, the expansion of $A v_j$ can be taken over any index range
$\{0, \dots, n - 1\}$ with $n \ge j + p + 1$. -/
private theorem apply_eq_range (j n : ℕ) (hj : j + p + 1 ≤ n) :
    A (v j) = ∑ i ∈ Finset.range n, h i j • v i := by
  rw [hv.apply_eq j]
  refine Finset.sum_subset (by simpa using hj) fun i _ hi' => ?_
  rw [Finset.mem_range] at hi'
  rw [hv.eq_zero_of_lt i j (by omega), zero_smul]

/-- Let $(v_j)$ satisfy a band relation of bandwidth $p$ with coefficients $(h_{ij})$. Then for
every $m$ and $y \in \mathbb{K}^m$,
$$A \sum_{j < m} y_j v_j = \sum_{i < m + p} (\bar H_m y)_i \, v_i,$$
which is the matrix relation $A V_m = V_{m+p} \bar H_m$ of [saad2003iterative], (6.129), in
coordinates. -/
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

/-- The **block residual formula**. Let $(v_j)$ satisfy a band relation of bandwidth $p$ with
coefficients $(h_{ij})$, and let $b, x_0 \in E$ and a sequence $(g_i)$ satisfy
$b - A x_0 = \sum_{i < p} g_i v_i$. Then for every $m$ and $y \in \mathbb{K}^m$,
$$b - A\Bigl(x_0 + \sum_{j < m} y_j v_j\Bigr) = \sum_{i < m + p} (E_1 g - \bar H_m y)_i \,
  v_i.$$
This is [saad2003iterative], (6.135), read one right-hand side at a time. -/
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

/-- The specification of a blockwise block Arnoldi algorithm ([saad2003iterative], Algorithms
6.22–6.23). Let $A$ be an operator on an inner product space and let $v_0, \dots, v_{p-1}$ be
starting vectors with block Krylov sequence $(f_k)$. A sequence $(u_k)_{k \ge 0}$ is a **block
Arnoldi basis** if it is orthonormal and
$$\operatorname{span}\{u_0, \dots, u_k\} = \operatorname{span}\{f_0, \dots, f_k\} \quad
  \text{for every } k.$$
Every choice of QR factorization inside a block produces such a sequence, and
`BlockArnoldi.blockVec_eq_vec` identifies it with the vectors of Ruhe's variant.

The whole sequence is orthonormal, so the specification assumes that the process never breaks
down. In particular, it can hold only in an infinite-dimensional space. -/
structure IsBlockArnoldiBasis (A : E →ₗ[𝕜] E) {p : ℕ} (v : Fin p → E) (u : ℕ → E) : Prop where
  /-- The vectors $u_k$ are orthonormal. -/
  orthonormal : Orthonormal 𝕜 u
  /-- For every $k$, the vectors $u_0, \dots, u_k$ span the same subspace as $f_0, \dots, f_k$. -/
  span_eq : ∀ k, Submodule.span 𝕜 (u '' Set.Iic k) =
    Submodule.span 𝕜 (blockSeq A v '' Set.Iic k)

namespace BlockArnoldi

/-!
### Gram–Schmidt with breakdown

The block Arnoldi vectors are the normalized Gram–Schmidt vectors of the block Krylov sequence, so
$q_k = 0$ exactly when $f_k$ is a linear combination of $f_0, \dots, f_{k-1}$. The facts about
`InnerProductSpace.gramSchmidtNormed` that hold without a hypothesis of linear independence are
`InnerProductSpace.inner_gramSchmidtNormed_eq_zero` and its companions in
`Numlib.Analysis.InnerProductSpace.GramSchmidt`. The two auxiliary lemmas below are stated for an
arbitrary sequence, because they use nothing about the Krylov structure.
-/

section GramSchmidtAux

/-- If $x$ is orthogonal to every element of a set $s$, then $\langle x, y \rangle = 0$ for every
$y \in \operatorname{span} s$. -/
private theorem inner_eq_zero_of_mem_span {s : Set E} {x y : E}
    (hx : ∀ u ∈ s, inner 𝕜 u x = (0 : 𝕜)) (hy : y ∈ Submodule.span 𝕜 s) :
    inner 𝕜 x y = 0 :=
  Submodule.inner_left_of_mem_orthogonal hy (Submodule.mem_orthogonal_span.2 hx)

variable (f : ℕ → E)

/-- For every $n$, the first $n$ normalized Gram–Schmidt vectors of a sequence $(f_k)$ span the same
subspace as $f_0, \dots, f_{n-1}$. -/
private theorem span_gsn_Iio (n : ℕ) :
    Submodule.span 𝕜 (gramSchmidtNormed 𝕜 f '' Set.Iio n) =
      Submodule.span 𝕜 (f '' Set.Iio n) :=
  (span_gramSchmidtNormed f (Set.Iio n)).trans (span_gramSchmidt_Iio 𝕜 f n)

end GramSchmidtAux

/-! ### The block Arnoldi vectors -/

/-- The **block Arnoldi vectors** $q_0, q_1, \dots$ of Ruhe's variant ([saad2003iterative],
Algorithm 6.24): the normalized Gram–Schmidt orthonormalization of the block Krylov sequence
$(f_k)$, one vector at a time. As for `Arnoldi.vec`, the vectors are $0$ after breakdown, that
is $q_k = 0$ when $f_k \in \operatorname{span}\{f_0, \dots, f_{k-1}\}$.

The definition is `InnerProductSpace.gramSchmidtNormed 𝕜 (Krylov.blockSeq A v)`. -/
noncomputable def vec (A : E →ₗ[𝕜] E) {p : ℕ} (v : Fin p → E) : ℕ → E :=
  gramSchmidtNormed 𝕜 (blockSeq A v)

/-- The **band Hessenberg coefficients** of the block Arnoldi process:
$$h_{ik} = \langle q_i, A q_k \rangle,$$
as in [saad2003iterative], (6.130). -/
noncomputable def coeff (A : E →ₗ[𝕜] E) {p : ℕ} (v : Fin p → E) (i k : ℕ) : 𝕜 :=
  inner 𝕜 (vec A v i) (A (vec A v k))

variable (A : E →ₗ[𝕜] E) {p : ℕ} (v : Fin p → E)

/-- The block Arnoldi vectors are the normalized Gram–Schmidt vectors of the block Krylov sequence.
-/
theorem vec_eq_gramSchmidtNormed : vec A v = gramSchmidtNormed 𝕜 (blockSeq A v) := rfl

/-- The band Hessenberg coefficients are the inner products $h_{ik} = \langle q_i, A q_k \rangle$.
-/
theorem coeff_apply (i k : ℕ) : coeff A v i k = inner 𝕜 (vec A v i) (A (vec A v k)) := rfl

/-- A block Arnoldi vector that is not $0$ is a unit vector: if $q_k \neq 0$, then $\|q_k\| = 1$. -/
theorem norm_vec_eq_one_of_ne_zero {k : ℕ} (h : vec A v k ≠ 0) : ‖vec A v k‖ = 1 :=
  gramSchmidtNormed_unit_length' h

/-- Distinct block Arnoldi vectors are orthogonal: $\langle q_i, q_j \rangle = 0$ for all
$i \neq j$, with no hypothesis, because past breakdown the vectors are $0$. -/
theorem inner_vec_eq_zero {i j : ℕ} (h : i ≠ j) : inner 𝕜 (vec A v i) (vec A v j) = 0 :=
  inner_gramSchmidtNormed_eq_zero _ h

/-- Let $n \ge 0$. If $q_k \neq 0$ for every $k < n$, then $q_0, \dots, q_{n-1}$ are orthonormal.
This is the orthonormality of the block Arnoldi vectors in [saad2003iterative], §6.12. -/
theorem orthonormal_vec {n : ℕ} (h : ∀ k < n, vec A v k ≠ 0) :
    Orthonormal 𝕜 fun i : Fin n => vec A v (i : ℕ) :=
  ⟨fun i => norm_vec_eq_one_of_ne_zero A v (h i i.isLt),
    fun _ _ hij => inner_vec_eq_zero A v fun hc => hij (Fin.val_injective hc)⟩

/-- The block Arnoldi vectors span the same flag of subspaces as the block Krylov sequence: for
every $n$,
$$\operatorname{span}\{q_0, \dots, q_{n-1}\} = \operatorname{span}\{f_0, \dots, f_{n-1}\}.$$
-/
theorem span_vec (n : ℕ) :
    Submodule.span 𝕜 (vec A v '' Set.Iio n) = Submodule.span 𝕜 (blockSeq A v '' Set.Iio n) :=
  span_gsn_Iio _ n

/-- For every $m$, the first $mp$ block Arnoldi vectors span the $m$-th block Krylov subspace:
$$\operatorname{span}\{q_0, \dots, q_{mp - 1}\} = \mathcal{K}_m(A, \{v_i\}).$$
This is [saad2003iterative], §6.12. Ruhe's variant reaches the block Krylov subspaces exactly at
the multiples of $p$. -/
theorem span_vec_eq_blockSubspace (m : ℕ) :
    Submodule.span 𝕜 (vec A v '' Set.Iio (m * p)) = blockSubspace A v m := by
  rw [span_vec, blockSubspace_eq_span_image_Iio]

/-- Each block Arnoldi vector is a combination of the first block Krylov vectors:
$q_k \in \operatorname{span}\{f_0, \dots, f_k\}$. -/
theorem vec_mem_span (k : ℕ) :
    vec A v k ∈ Submodule.span 𝕜 (blockSeq A v '' Set.Iio (k + 1)) := by
  rw [← span_vec]
  exact Submodule.subset_span ⟨k, Nat.lt_succ_self k, rfl⟩

/-- The operator $A$ advances the flag of the block Krylov sequence by one block: $A
\operatorname{span}\{f_0, \dots, f_{n-1}\} \subseteq \operatorname{span}\{f_0, \dots,
f_{n+p-1}\}$. -/
private theorem map_span_blockSeq_le (n : ℕ) :
    (Submodule.span 𝕜 (blockSeq A v '' Set.Iio n)).map A ≤
      Submodule.span 𝕜 (blockSeq A v '' Set.Iio (n + p)) := by
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, apply_blockSeq]
  exact Submodule.subset_span ⟨k + p, Nat.add_lt_add_right hk p, rfl⟩

/-- The image of a block Arnoldi vector lies in the span of the first $k + p + 1$ of them: $A q_k
\in \operatorname{span}\{q_0, \dots, q_{k+p}\}$. This is the source of the band structure of
bandwidth $p$. -/
theorem apply_vec_mem (k : ℕ) :
    A (vec A v k) ∈ Submodule.span 𝕜 (vec A v '' Set.Iio (k + p + 1)) := by
  rw [span_vec]
  have h := map_span_blockSeq_le A v (k + 1) ⟨_, vec_mem_span A v k, rfl⟩
  rwa [show k + 1 + p = k + p + 1 by omega] at h

/-- **Band structure** of the coefficients: $h_{ik} = 0$ for $i > k + p$. This is
[saad2003iterative], (6.130). -/
theorem coeff_eq_zero_of_lt {i k : ℕ} (h : k + p < i) : coeff A v i k = 0 := by
  rw [coeff_apply]
  refine inner_eq_zero_of_mem_span (s := vec A v '' Set.Iio i) ?_ ?_
  · rintro _ ⟨j, hj, rfl⟩
    exact inner_vec_eq_zero A v (Nat.ne_of_lt hj)
  · exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (by omega)))
      (apply_vec_mem A v k)

/-- The band expansion of the image of a block Arnoldi vector, [saad2003iterative], (6.129):
$$A q_k = \sum_{i \le k + p} h_{ik} q_i.$$
-/
theorem apply_vec (k : ℕ) :
    A (vec A v k) = ∑ i ∈ Finset.range (k + p + 1), coeff A v i k • vec A v i :=
  eq_sum_inner_smul_gramSchmidtNormed (blockSeq A v) (apply_vec_mem A v k)

/-- The block Arnoldi vectors satisfy the band relation of bandwidth $p$ with the coefficients
$h_{ik} = \langle q_i, A q_k \rangle$:
$$A q_k = \sum_{i \le k + p} h_{ik} q_i, \qquad h_{ik} = 0 \text{ for } i > k + p.$$
In matrix form this is $A Q_m = Q_{m+p} \bar H_m$, the relation (6.129)–(6.130) of
[saad2003iterative]. -/
theorem hessenbergRelation : BandRelation A (vec A v) (coeff A v) p :=
  ⟨apply_vec A v, fun _ _ h => coeff_eq_zero_of_lt A v h⟩

/-! ### Symmetric $A$: block Lanczos -/

section Symmetric

variable {A} (hA : A.IsSymmetric)
include hA

/-- For a symmetric operator $A$, the coefficient array of the block Arnoldi process is Hermitian:
$$h_{ik} = \overline{h_{ki}} \quad \text{for all } i, k.$$
-/
theorem coeff_conj_of_isSymmetric (i k : ℕ) :
    coeff A v i k = starRingEnd 𝕜 (coeff A v k i) := by
  rw [coeff_apply, coeff_apply, inner_conj_symm, hA]

/-- For a symmetric operator $A$, the band coefficients also vanish more than $p$ places above the
diagonal:
$$h_{ik} = 0 \quad \text{for } k > i + p.$$

So the coefficient matrix of block Lanczos is block tridiagonal, a Hermitian band matrix of
bandwidth $p$, as in [golub2013matrix], (10.3.7). -/
theorem coeff_eq_zero_of_isSymmetric {i k : ℕ} (h : i + p < k) : coeff A v i k = 0 := by
  rw [coeff_conj_of_isSymmetric v hA, coeff_eq_zero_of_lt A v h, map_zero]

end Symmetric

/-! ### The case of one starting vector -/

/-- For a single starting vector ($p = 1$), the block Arnoldi vectors of Ruhe's variant are the
Arnoldi vectors of $A$ from $v_0$. -/
theorem vec_one (A : E →ₗ[𝕜] E) (v : Fin 1 → E) : vec A v = Arnoldi.vec A (v 0) := by
  have h : blockSeq A v = fun k : ℕ => (A ^ k) (v 0) := funext (blockSeq_one A v)
  rw [vec_eq_gramSchmidtNormed, h]
  rfl

/-- For a single starting vector ($p = 1$), the band Hessenberg coefficients are the Arnoldi
coefficients of $A$ from $v_0$. -/
theorem coeff_one (A : E →ₗ[𝕜] E) (v : Fin 1 → E) : coeff A v = Arnoldi.coeff A (v 0) := by
  funext i k
  rw [coeff_apply, vec_one]
  rfl

/-- The Hessenberg relation of the Arnoldi process from $v_0$, obtained as the case $p = 1$ of the
band relation `BlockArnoldi.hessenbergRelation`: the Arnoldi vectors of $A$ from $v_0$ satisfy
`Krylov.HessenbergRelation` with the Arnoldi coefficients. -/
theorem hessenbergRelation_one (A : E →ₗ[𝕜] E) (v : Fin 1 → E) :
    HessenbergRelation A (Arnoldi.vec A (v 0)) (Arnoldi.coeff A (v 0)) :=
  Arnoldi.hessenbergRelation A (v 0)

end BlockArnoldi

/-! ### Equivalence of the blockwise algorithms with Ruhe's variant -/

namespace BlockArnoldi

variable {A : E →ₗ[𝕜] E} {p : ℕ} {v : Fin p → E} {u : ℕ → E}

open scoped ComplexOrder in
/-- **Mathematical equivalence of the blockwise algorithm and Ruhe's variant** ([saad2003iterative],
§6.12). Let $(u_k)$ be a block Arnoldi basis (`IsBlockArnoldiBasis`) for $A$ and
$v_0, \dots, v_{p-1}$, and let $k \ge 0$. If $\langle u_k, f_k \rangle$ is real and positive,
then
$$u_k = q_k.$$

The source states that Algorithms 6.23 (a block orthogonalization followed by a QR factorization
of the new block) and 6.24 (Ruhe's variant) are mathematically equivalent. The condition
$\langle u_k, f_k \rangle > 0$ is the sign convention of Gram–Schmidt, which Gram–Schmidt QR
satisfies. For any other QR factorization the vectors agree up to unimodular scalars, by
`IsBlockArnoldiBasis.exists_norm_eq_one_smul_vec`. The inequality $0 < \langle u_k, f_k \rangle$
is in the partial order of `ComplexOrder`, in which $0 < z$ means that $z$ is real and positive. -/
theorem blockVec_eq_vec (hu : IsBlockArnoldiBasis A v u) {k : ℕ}
    (hpos : 0 < inner 𝕜 (u k) (blockSeq A v k)) : u k = vec A v k :=
  eq_gramSchmidtNormed_of_re_inner_pos hu.orthonormal hu.span_eq k hpos

end BlockArnoldi

namespace IsBlockArnoldiBasis

variable {A : E →ₗ[𝕜] E} {p : ℕ} {v : Fin p → E} {u : ℕ → E} (hu : IsBlockArnoldiBasis A v u)
include hu

/-- Let $(u_k)$ be a block Arnoldi basis for $A$ and $v_0, \dots, v_{p-1}$. Then for every $k$ there
is a scalar $\varepsilon$ with $|\varepsilon| = 1$ and
$$u_k = \varepsilon \, q_k.$$
So whatever QR factorization the blockwise algorithm uses, its vectors are those of Ruhe's
variant up to unimodular scalars ([saad2003iterative], §6.12). -/
theorem exists_norm_eq_one_smul_vec (k : ℕ) :
    ∃ ε : 𝕜, ‖ε‖ = 1 ∧ u k = ε • BlockArnoldi.vec A v k :=
  exists_norm_eq_one_smul_gramSchmidtNormed hu.orthonormal hu.span_eq k

/-- For a block Arnoldi basis $(u_k)$ and every $n$, $\operatorname{span}\{u_0, \dots, u_{n-1}\} =
\operatorname{span}\{f_0, \dots, f_{n-1}\}$; for $n = 0$ both sides are $0$. -/
theorem span_eq_Iio (n : ℕ) :
    Submodule.span 𝕜 (u '' Set.Iio n) = Submodule.span 𝕜 (blockSeq A v '' Set.Iio n) := by
  cases n with
  | zero => simp
  | succ k =>
    rw [show Set.Iio (k + 1) = Set.Iic k from Set.ext fun _ => Nat.lt_succ_iff]
    exact hu.span_eq k

/-- Let $(u_k)$ be a block Arnoldi basis for $A$ and $v_0, \dots, v_{p-1}$. Then for every $m$,
$$\operatorname{span}\{u_0, \dots, u_{mp - 1}\} = \mathcal{K}_m(A, \{v_i\}).$$
So whatever QR convention the blockwise algorithm uses, the space built after $m$ blocks is the
$m$-th block Krylov subspace. -/
theorem span_eq_blockSubspace (m : ℕ) :
    Submodule.span 𝕜 (u '' Set.Iio (m * p)) = blockSubspace A v m := by
  rw [hu.span_eq_Iio, ← blockSubspace_eq_span_image_Iio]

end IsBlockArnoldiBasis

namespace BlockArnoldi

/-! ### Block FOM and block GMRES in coordinates -/

variable (A : E →ₗ[𝕜] E) {p : ℕ} (v : Fin p → E)

/-- The $(m + p) \times m$ **band Hessenberg matrix** $\bar H_m$ of the block Arnoldi process, with
entries $h_{ik} = \langle q_i, A q_k \rangle$. This is the matrix $\bar H_m$ of
[saad2003iterative], (6.129)–(6.130). -/
noncomputable def hessenberg (m : ℕ) : Matrix (Fin (m + p)) (Fin m) 𝕜 := bandOf (coeff A v) p m

/-- The square $m \times m$ **band Hessenberg matrix** $H_m$ of the block Arnoldi process, with
entries $h_{ik} = \langle q_i, A q_k \rangle$ for $i, k < m$. -/
noncomputable def hessenbergSq (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜 :=
  hessenbergSqOf (coeff A v) m

/-- For a symmetric operator $A$, the square block Lanczos matrix $T_m = H_m$ is Hermitian. -/
theorem isHermitian_hessenbergSq_of_isSymmetric {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (m : ℕ) :
    (hessenbergSq A v m).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i k => ?_
  change starRingEnd 𝕜 (coeff A v k i) = coeff A v i k
  rw [coeff_conj_of_isSymmetric v hA (i : ℕ) (k : ℕ)]

/-- For a symmetric operator $A$, the square block Lanczos matrix $T_m = H_m$ has upper and lower
bandwidth $p$: its entry at $(i, k)$ is $0$ when $|i - k| > p$. So it is block tridiagonal, as
in [golub2013matrix], (10.3.7). -/
theorem hasBandwidth_hessenbergSq_of_isSymmetric {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (m : ℕ) :
    (hessenbergSq A v m).HasUpperBandwidth p ∧ (hessenbergSq A v m).HasLowerBandwidth p :=
  ⟨Matrix.hasUpperBandwidthRect_iff.1 fun _ _ h => coeff_eq_zero_of_isSymmetric v hA h,
    Matrix.hasLowerBandwidthRect_iff.1 fun _ _ h => coeff_eq_zero_of_lt A v h⟩

/-- The first $n$ block Arnoldi vectors, as a set, are the range of the family $(q_i)_{i < n}$. -/
private theorem image_Iio_eq_range (n : ℕ) :
    vec A v '' Set.Iio n = Set.range fun i : Fin n => vec A v (i : ℕ) := by
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨(j : ℕ), j.isLt, rfl⟩

/-- The space built by Ruhe's variant after $n$ steps, in coordinates: $x \in
\operatorname{span}\{q_0, \dots, q_{n-1}\}$ if and only if $x = \sum_{j < n} y_j q_j$ for some
$y \in \mathbb{K}^n$. -/
theorem mem_span_vec_iff (n : ℕ) (x : E) :
    x ∈ Submodule.span 𝕜 (vec A v '' Set.Iio n) ↔
      ∃ y : Fin n → 𝕜, x = ∑ j, y j • vec A v (j : ℕ) := by
  rw [image_Iio_eq_range, Submodule.mem_span_range_iff_exists_fun]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

/-- For every $y \in \mathbb{K}^n$, the combination $\sum_{j < n} y_j q_j$ lies in
$\operatorname{span}\{q_0, \dots, q_{n-1}\}$. -/
theorem sum_smul_vec_mem (n : ℕ) (y : Fin n → 𝕜) :
    ∑ j, y j • vec A v (j : ℕ) ∈ Submodule.span 𝕜 (vec A v '' Set.Iio n) :=
  (mem_span_vec_iff A v n _).2 ⟨y, rfl⟩

/-- The block QR factorization of the starting residuals, $R_0 = V_p R$ of [saad2003iterative],
(6.135): every vector $x$ of the first block Krylov subspace $\mathcal{K}_1(A, \{v_i\}) =
\operatorname{span}\{v_0, \dots, v_{p-1}\}$ is a combination $x = \sum_{i < p} g_i q_i$ of the
first $p$ block Arnoldi vectors.

This gives the hypothesis of `BlockArnoldi.residual_eq` when $b - A x_0$ lies in the first block
Krylov subspace. -/
theorem exists_coeffs_of_mem_blockSubspace_one {x : E} (hx : x ∈ blockSubspace A v 1) :
    ∃ g : ℕ → 𝕜, x = ∑ i ∈ Finset.range p, g i • vec A v i := by
  rw [← span_vec_eq_blockSubspace, one_mul] at hx
  obtain ⟨y, hy⟩ := (mem_span_vec_iff A v p x).1 hx
  refine ⟨fun i => if h : i < p then y ⟨i, h⟩ else 0, ?_⟩
  rw [hy, ← Fin.sum_univ_eq_sum_range
    (fun i => (if h : i < p then y ⟨i, h⟩ else 0) • vec A v i) p]
  exact Finset.sum_congr rfl fun j _ => by simp

variable {b x₀ : E} {g : ℕ → 𝕜} {m : ℕ}

/-- **The block residual formula** ([saad2003iterative], (6.135)). Let $b, x_0 \in E$ and a sequence
$(g_i)$ satisfy $b - A x_0 = \sum_{i < p} g_i q_i$. Then for every $y \in \mathbb{K}^m$,
$$b - A\Bigl(x_0 + \sum_{j < m} y_j q_j\Bigr) = \sum_{i < m + p} (E_1 g - \bar H_m y)_i \,
  q_i.$$
This is the formula $R = V_{m+p}(E_1 R_0 - \bar H_m Y)$ for the residual of $X_0 + V_m Y$, read
one right-hand side at a time. -/
theorem residual_eq (hr : b - A x₀ = ∑ i ∈ Finset.range p, g i • vec A v i) (y : Fin m → 𝕜) :
    b - A (x₀ + ∑ j, y j • vec A v (j : ℕ)) =
      ∑ i : Fin (m + p), (firstBlockVec g p (m + p) - (hessenberg A v m).mulVec y) i •
        vec A v (i : ℕ) :=
  (hessenbergRelation A v).residual_eq hr m y

/-- **The block residual norm** ([saad2003iterative], (6.136)). Suppose that $q_0, \dots, q_{m+p-1}$
are orthonormal, so that the process has not broken down. Let $b, x_0 \in E$ and a sequence
$(g_i)$ satisfy $b - A x_0 = \sum_{i < p} g_i q_i$. Then for every $y \in \mathbb{K}^m$,
$$\Bigl\|b - A\Bigl(x_0 + \sum_{j < m} y_j q_j\Bigr)\Bigr\| = \|E_1 g - \bar H_m y\|_2,$$
where the right-hand side is the Euclidean norm in $\mathbb{K}^{m+p}$. -/
theorem norm_residual_eq (hon : Orthonormal 𝕜 fun i : Fin (m + p) => vec A v (i : ℕ))
    (hr : b - A x₀ = ∑ i ∈ Finset.range p, g i • vec A v i) (y : Fin m → 𝕜) :
    ‖b - A (x₀ + ∑ j, y j • vec A v (j : ℕ))‖ =
      ‖(WithLp.toLp 2 (firstBlockVec g p (m + p) - (hessenberg A v m).mulVec y) :
        EuclideanSpace 𝕜 (Fin (m + p)))‖ := by
  rw [residual_eq A v hr y]
  exact hon.norm_sum_smul_eq_norm_toLp _

/-- **Block FOM in coordinates** ([saad2003iterative], §6.12). Suppose that $q_0, \dots, q_{m+p-1}$
are orthonormal, and let $b, x_0 \in E$ and a sequence $(g_i)$ satisfy
$b - A x_0 = \sum_{i < p} g_i q_i$. Then for every $y \in \mathbb{K}^m$, the vector
$x = x_0 + \sum_{j < m} y_j q_j$ satisfies the Galerkin condition
$$b - A x \perp \operatorname{span}\{q_0, \dots, q_{m-1}\}$$
if and only if $y$ solves the square band system
$$H_m y = E_1 g.$$

The Galerkin condition is `IsGalerkin` on the subspace
$\operatorname{span}\{q_0, \dots, q_{m-1}\}$, and $E_1 g$ is `Krylov.firstBlockVec g p m`. -/
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

/-- **Block GMRES in coordinates** ([saad2003iterative], (6.136)). Suppose that
$q_0, \dots, q_{m+p-1}$ are orthonormal, and let $b, x_0 \in E$ and a sequence $(g_i)$ satisfy
$b - A x_0 = \sum_{i < p} g_i q_i$. Then for every $y \in \mathbb{K}^m$, the vector
$x = x_0 + \sum_{j < m} y_j q_j$ minimizes $\|b - A x\|$ over $x_0 + \operatorname{span}\{q_0,
\dots, q_{m-1}\}$ if and only if $y$ solves the band least-squares problem
$$\|E_1 g - \bar H_m y\|_2 \le \|E_1 g - \bar H_m z\|_2 \quad \text{for every } z \in
  \mathbb{K}^m.$$

The minimization is `IsMinResidual` on the subspace
$\operatorname{span}\{q_0, \dots, q_{m-1}\}$. -/
theorem isMinResidual_iff (hon : Orthonormal 𝕜 fun i : Fin (m + p) => vec A v (i : ℕ))
    (hr : b - A x₀ = ∑ i ∈ Finset.range p, g i • vec A v i) (y : Fin m → 𝕜) :
    IsMinResidual A b x₀ (Submodule.span 𝕜 (vec A v '' Set.Iio m))
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

/-- **Block FOM on the block Krylov subspace.** Let $n \ge 0$, and suppose that
$q_0, \dots, q_{np + p - 1}$ are orthonormal. Let $b, x_0 \in E$ and a sequence $(g_i)$ satisfy
$b - A x_0 = \sum_{i < p} g_i q_i$. Then for every $y \in \mathbb{K}^{np}$, the vector
$x = x_0 + \sum_{j < np} y_j q_j$ satisfies the Galerkin condition
$b - A x \perp \mathcal{K}_n(A, \{v_i\})$ if and only if
$$H_{np} \, y = E_1 g.$$

This is `BlockArnoldi.isGalerkin_iff_mulVec_eq` at $m = np$, where the space built by Ruhe's
variant is the block Krylov subspace `Krylov.blockSubspace A v n`. -/
theorem isGalerkin_blockSubspace_iff {n : ℕ}
    (hon : Orthonormal 𝕜 fun i : Fin (n * p + p) => vec A v (i : ℕ))
    (hr : b - A x₀ = ∑ i ∈ Finset.range p, g i • vec A v i) (y : Fin (n * p) → 𝕜) :
    IsGalerkin A b x₀ (blockSubspace A v n) (x₀ + ∑ j, y j • vec A v (j : ℕ)) ↔
      (hessenbergSq A v (n * p)).mulVec y = firstBlockVec g p (n * p) := by
  rw [← span_vec_eq_blockSubspace]
  exact isGalerkin_iff_mulVec_eq A v hon hr y

/-- **Block GMRES on the block Krylov subspace.** Let $n \ge 0$, and suppose that
$q_0, \dots, q_{np + p - 1}$ are orthonormal. Let $b, x_0 \in E$ and a sequence $(g_i)$ satisfy
$b - A x_0 = \sum_{i < p} g_i q_i$. Then for every $y \in \mathbb{K}^{np}$, the vector
$x = x_0 + \sum_{j < np} y_j q_j$ minimizes $\|b - A x\|$ over $x_0 + \mathcal{K}_n(A, \{v_i\})$
if and only if
$$\|E_1 g - \bar H_{np} y\|_2 \le \|E_1 g - \bar H_{np} z\|_2 \quad \text{for every } z \in
  \mathbb{K}^{np}.$$

This is `BlockArnoldi.isMinResidual_iff` at $m = np$. -/
theorem isMinResidual_blockSubspace_iff {n : ℕ}
    (hon : Orthonormal 𝕜 fun i : Fin (n * p + p) => vec A v (i : ℕ))
    (hr : b - A x₀ = ∑ i ∈ Finset.range p, g i • vec A v i) (y : Fin (n * p) → 𝕜) :
    IsMinResidual A b x₀ (blockSubspace A v n) (x₀ + ∑ j, y j • vec A v (j : ℕ)) ↔
      ∀ z : Fin (n * p) → 𝕜,
        ‖(WithLp.toLp 2 (firstBlockVec g p (n * p + p) -
            (hessenberg A v (n * p)).mulVec y) : EuclideanSpace 𝕜 (Fin (n * p + p)))‖ ≤
          ‖(WithLp.toLp 2 (firstBlockVec g p (n * p + p) -
            (hessenberg A v (n * p)).mulVec z) : EuclideanSpace 𝕜 (Fin (n * p + p)))‖ := by
  rw [← span_vec_eq_blockSubspace]
  exact isMinResidual_iff A v hon hr y

end BlockArnoldi
