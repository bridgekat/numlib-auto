import NumlibSurface.SaadSparse.Chapter04.Section02
import NumlibSurface.SaadSparse.Chapter05.Section03
import NumlibSurface.SaadSparse.Chapter05.Section04
import NumlibSurface.SaadSparse.Chapter08.Section01

/-!
# Saad §8.2: row projection methods

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §8.2, with P-8.2 and P-8.8.

The section introduces no new method: every algorithm in it is a projection process of §5.3–5.4
over the coordinate subspaces `K_i = span {e_i}`, run on one of the two normal-equations systems.
This file says so declaration by declaration.

* `neSorStep` is **Algorithm 8.1** (NE-SOR, Kaczmarz), one relaxation `x := x + δ_i Aᵀ e_i`;
  `neSorStep_isPetrovGalerkin` is (8.12)–(8.15), the identification with the one-dimensional
  Petrov–Galerkin step onto `span {Aᵀ e_i}` orthogonally to `span {e_i}`, after which the `i`-th
  component of the residual vanishes.
* `nrSorStep` is **Algorithm 8.2** (NR-SOR), `x := x + δ_i e_i`; `nrSorStep_isGalerkin` is
  (8.17)–(8.18), the Galerkin step for `AᵀA x = Aᵀ b` on `span {e_i}`, after which the `i`-th
  component of the normal-equations residual vanishes.
* `sorSweep_eq_multiplicativeSweep` and `neSorSweep_eq_multiplicativeStep` put the two sweeps in
  the multiplicative projection process of §5.4 over the coordinate family — the NR-SOR sweep in
  the Galerkin form `SaadSparse.Chapter05.multiplicativeSweep`, the NE-SOR sweep in the backbone's
  Petrov–Galerkin `Projection.multiplicativeStep`, since its test spaces differ from its trial
  spaces; `cimmino_eq_additiveStep` puts **Algorithm 8.3** in the
  additive one, which is Saad's own remark that each instance of Cimmino's method is an
  orthogonal projection step for `AᵀA x = Aᵀ b` with `K = span {e_i}`.
* `equation_8_24` is the projector `P_i r = ((r, A e_i)/‖A e_i‖²) A e_i` onto the `i`-th column
  of `A`, the least-squares instance `L_i = A K_i` of (5.22), and `equation_8_25` the residual
  identity `r_new = (1 - ω ∑ P_i) r` together with **P-8.8**.
* `cimmino_eq_richardson` is **P-8.2**: with unit columns Cimmino's method is Richardson's
  iteration on the normal equations, so (8.22) — its convergence interval and optimal
  parameter — is Example 4.1 applied to `AᵀA` (`equation_8_22`). Without the normalization,
  `cimmino_eq_richardson_diag` is P-8.2 (a)–(b): the same iteration preconditioned by the diagonal
  `D = diag(‖A e_i‖₂²)` of `AᵀA`.
* `cimminoNE` is **P-8.3**, Cimmino's original *row* method — Jacobi for `A Aᵀ u = b` read through
  `x = Aᵀ u` (`cimminoNE_eq_jacobi`) — and `cimminoNE_eq_additiveStep` puts it in the additive
  Petrov–Galerkin process over the pairs `(span {Aᵀ e_i}, span {e_i})`, the pairs Kaczmarz's
  method uses multiplicatively.
* `blockCimmino` is (8.26)–(8.27), the same statement with `dim K_i > 1` and a least-squares
  subproblem in place of the scalar division.

* `nrSorSweep_eq_sorStep` makes §8.2.1's back-reference to Chapter 4 good: a whole NR-SOR sweep is
  one SOR step (4.12) for the normal equations `AᵀA x = Aᵀ b`, and `sorSweep_tendsto` is then
  Theorem 4.10 applied to `AᵀA` — symmetric positive definite whenever `A` is nonsingular — so the
  sweep converges to the solution for every `0 < ω < 2`.

Not formalized: P-8.2 (c), the convergence interval `0 < ω < 2/λ_max(D^{-1/2} AᵀA D^{-1/2})` of the
unnormalized iteration, which needs the symmetric square root of `D` and the transport of
`Chapter04.example_4_1_tendsto_iff` through that change of variables — `equation_8_22` is the
normalized case. See `plans/saadsparse-ch7-9.md` §4.

As in Chapter 5, everything is over `ℝ`, which is where §5.3–5.4 live.
-/

open Matrix Filter Topology

open scoped Matrix SaadSparse

namespace SaadSparse.Chapter08

variable {n : ℕ}

local notation "E" n => EuclideanSpace ℝ (Fin n)

/-! ### The coordinate family -/

/-- The `i`-th coordinate vector `e_i` of `ℝⁿ`. -/
noncomputable def coordVec (i : Fin n) : E n := EuclideanSpace.single i 1

/-- The `i`-th coordinate axis as a one-column matrix, the shape
`SaadSparse.Chapter05.ProjFamily` takes. -/
def coordCol (i : Fin n) : Matrix (Fin n) (Fin 1) ℝ :=
  Matrix.of fun p _ => (Pi.single i (1 : ℝ) : Fin n → ℝ) p

/-- The family of the `n` coordinate axes: the projection family over which every method of
§8.2 is a §5.4 projection process. -/
noncomputable def coordFamily (n : ℕ) : Chapter05.ProjFamily n where
  p := n
  size _ := 1
  V := coordCol

/-- The coordinate family has one subspace per coordinate. -/
@[simp] theorem coordFamily_p : (coordFamily n).p = n := rfl

/-- The `i`-th block of the coordinate family is the `i`-th coordinate axis. -/
@[simp] theorem coordFamily_V (i : Fin n) : (coordFamily n).V i = coordCol i := rfl

/-- The single column of `coordCol i` is the coordinate vector `e_i`. -/
theorem coordCol_cols (i : Fin n) (j : Fin 1) : (coordCol i).cols j = coordVec i := by
  refine WithLp.ofLp_injective 2 ?_
  funext p
  rw [Matrix.ofLp_cols_apply, coordCol, Matrix.of_apply, coordVec]
  simp [Pi.single_apply]

/-- The `i`-th subspace of the coordinate family is the `i`-th coordinate axis. -/
theorem coordFamily_subspace (i : Fin n) : (coordFamily n).subspace i = ℝ ∙ coordVec i := by
  have hsub : (coordFamily n).subspace i
      = Submodule.span ℝ (Set.range (coordCol i).cols) := rfl
  rw [hsub, show (coordCol i).cols = fun _ : Fin 1 => coordVec i from funext (coordCol_cols i),
    Set.range_const]

/-- `Aᵀ` acts as the adjoint of `A` in the real inner product. -/
theorem inner_transpose (M : Matrix (Fin n) (Fin n) ℝ) (u v : E n) :
    inner ℝ (Mᵀ ⬝ u) v = inner ℝ u (M ⬝ v) := by
  have h := inner_conjTranspose M u v
  rwa [Chapter05.conjTranspose_eq_transpose] at h

/-- `(u, Aᵀ v) = (A u, v)`, the companion of `SaadSparse.Chapter08.inner_transpose`. -/
theorem inner_transpose' (M : Matrix (Fin n) (Fin n) ℝ) (u v : E n) :
    inner ℝ u (Mᵀ ⬝ v) = inner ℝ (M ⬝ u) v := by
  rw [real_inner_comm, inner_transpose, real_inner_comm]

/-- The quadratic form of the normal-equations matrix on a coordinate axis is the squared norm
of the corresponding column of `A`. -/
theorem inner_normal_coordVec (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    inner ℝ (coordVec i) ((Aᵀ * A) ⬝ coordVec i) = ‖A ⬝ coordVec i‖ ^ 2 := by
  rw [Chapter05.toEuclideanLin_mul_apply, inner_transpose', real_inner_self_eq_norm_sq]

/-- The quadratic form of `A Aᵀ` on a coordinate axis is the squared norm of the corresponding
row of `A`. -/
theorem inner_normal'_coordVec (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    inner ℝ (coordVec i) (A ⬝ (Aᵀ ⬝ coordVec i)) = ‖Aᵀ ⬝ coordVec i‖ ^ 2 := by
  rw [← inner_transpose, real_inner_self_eq_norm_sq]

/-- The normal-equations residual is `Aᵀ` of the residual. -/
theorem normal_residual (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) :
    (Aᵀ ⬝ b) - ((Aᵀ * A) ⬝ x) = (Aᵀ ⬝ (b - (A ⬝ x))) := by
  rw [Chapter05.toEuclideanLin_mul_apply, ← map_sub]

/-! ### One-dimensional Petrov–Galerkin pairs -/

/-- A one-dimensional Petrov–Galerkin pair is nondegenerate exactly when `(A v, w) ≠ 0`, which
is Saad's Proposition 5.1 in dimension one. -/
theorem isNondegeneratePair_span_singleton {M : (E n) →ₗ[ℝ] (E n)} {v w : E n}
    (h : inner ℝ w (M v) ≠ 0) : Projection.IsNondegeneratePair M (ℝ ∙ v) (ℝ ∙ w) where
  finrank_eq := by
    have hv : v ≠ 0 := fun hc => h (by rw [hc, map_zero, inner_zero_right])
    have hw : w ≠ 0 := fun hc => h (by rw [hc, inner_zero_left])
    rw [finrank_span_singleton hv, finrank_span_singleton hw]
  eq_zero_of_mem_orthogonal z hz hzo := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have h0 : inner ℝ w (M (c • v)) = (0 : ℝ) :=
      (Submodule.mem_orthogonal _ _).1 hzo w (Submodule.mem_span_singleton_self w)
    rw [map_smul, inner_smul_right] at h0
    rcases mul_eq_zero.1 h0 with hc | hcon
    · rw [hc, zero_smul]
    · exact absurd hcon h

/-- The Petrov–Galerkin step of a one-dimensional pair is the elementary step (5.12): this is
what makes every method of §8.2 a §5.4 projection process. -/
theorem pairStep_eq_step1 {M : (E n) →ₗ[ℝ] (E n)} {c : E n} {K L : Submodule ℝ (E n)}
    [FiniteDimensional ℝ K] [FiniteDimensional ℝ L]
    (h : Projection.IsNondegeneratePair M K L) {v w : E n} (hK : K = ℝ ∙ v) (hL : L = ℝ ∙ w)
    (hvw : inner ℝ w (M v) ≠ 0) (x : E n) :
    Projection.pairStep M c K L h x = Projection.step1 M c v w x := by
  subst hK
  subst hL
  exact (Projection.pairStep_isPetrovGalerkin (b := c) h x).eq_of_forall
    (Projection.step1_isPetrovGalerkin v w x hvw) h.eq_zero_of_mem_orthogonal

/-- The nondegeneracy hypothesis §5.4 takes, for the coordinate family and a matrix whose
quadratic form does not vanish on any coordinate axis. -/
theorem isUnit_coordCol {M : Matrix (Fin n) (Fin n) ℝ} {i : Fin n}
    (h : inner ℝ (coordVec i) (M ⬝ coordVec i) ≠ 0) :
    IsUnit ((coordCol i)ᵀ * M * coordCol i) := by
  rw [← Chapter05.crossGram_matrix M (coordCol i) (coordCol i), Matrix.isUnit_iff_isUnit_det,
    Matrix.det_fin_one, Matrix.of_apply, coordCol_cols, isUnit_iff_ne_zero]
  exact h

/-! ### Algorithm 8.1: the NE-SOR relaxation -/

variable (A : Matrix (Fin n) (Fin n) ℝ) (b : E n) (ω : ℝ)

/-- **Algorithm 8.1**, one relaxation (Kaczmarz's row projection, (8.11)–(8.15)):
`x := x + δ_i Aᵀ e_i` with `δ_i = ω (β_i - (x, Aᵀ e_i))/‖Aᵀ e_i‖₂²`, where `Aᵀ e_i` is the `i`-th
row of `A` and `β_i` the `i`-th component of `b`. -/
noncomputable def neSorStep (i : Fin n) (x : E n) : E n :=
  x + (ω * inner ℝ (coordVec i) (b - (A ⬝ x)) / ‖Aᵀ ⬝ coordVec i‖ ^ 2) • (Aᵀ ⬝ coordVec i)

/-- **Algorithm 8.1**: one forward NE-SOR sweep `i = 1, …, n`. -/
noncomputable def neSorSweep (x : E n) : E n :=
  (List.finRange n).foldl (fun y i => neSorStep A b ω i y) x

/-- **Algorithm 8.2**, one relaxation ((8.16)–(8.18)): `x := x + δ_i e_i` with
`δ_i = ω (r, A e_i)/‖A e_i‖₂²`, where `A e_i` is the `i`-th column of `A`. -/
noncomputable def nrSorStep (i : Fin n) (x : E n) : E n :=
  x + (ω * inner ℝ (A ⬝ coordVec i) (b - (A ⬝ x)) / ‖A ⬝ coordVec i‖ ^ 2) • coordVec i

/-- **Algorithm 8.2**: one forward NR-SOR sweep `i = 1, …, n`. -/
noncomputable def nrSorSweep (x : E n) : E n :=
  (List.finRange n).foldl (fun y i => nrSorStep A b ω i y) x

variable {A b ω}

/-- The unrelaxed NE-SOR relaxation is the elementary step (5.12) with `v = Aᵀ e_i`,
`w = e_i`. -/
theorem neSorStep_eq_step1 (i : Fin n) (x : E n) :
    neSorStep A b 1 i x = Chapter05.step1 A b (Aᵀ ⬝ coordVec i) (coordVec i) x := by
  rw [neSorStep, Chapter05.step1, inner_normal'_coordVec, one_mul]

/-- The unrelaxed NR-SOR relaxation is the elementary step (5.12) for the normal equations
`AᵀA x = Aᵀ b` with `v = w = e_i`. -/
theorem nrSorStep_eq_step1 (i : Fin n) (x : E n) :
    nrSorStep A b 1 i x = Chapter05.step1 (Aᵀ * A) (Aᵀ ⬝ b) (coordVec i) (coordVec i) x := by
  rw [nrSorStep, Chapter05.step1, inner_normal_coordVec, normal_residual, inner_transpose', one_mul]

/-- **Saad (8.12)–(8.15)**: the unrelaxed NE-SOR relaxation is the Petrov–Galerkin step onto
`K = span {Aᵀ e_i}` orthogonally to `L = span {e_i}`, and the `i`-th component of the new
residual therefore vanishes. -/
theorem neSorStep_isPetrovGalerkin (hi : (Aᵀ ⬝ coordVec i) ≠ 0) (x : E n) :
    IsPetrovGalerkin (Matrix.toEuclideanLin A) b x (ℝ ∙ (Aᵀ ⬝ coordVec i)) (ℝ ∙ coordVec i)
        (neSorStep A b 1 i x) ∧
      inner ℝ (coordVec i) (b - (A ⬝ neSorStep A b 1 i x)) = 0 := by
  have hne : inner ℝ (coordVec i) (A ⬝ (Aᵀ ⬝ coordVec i)) ≠ 0 := by
    rw [inner_normal'_coordVec]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 hi)
  have hpg := Chapter05.isProjectionApprox_iff.1
    (Chapter05.step1_isProjectionApprox (A := A) (b := b) (x := x) (Aᵀ ⬝ coordVec i)
      (coordVec i) hne)
  rw [← neSorStep_eq_step1] at hpg
  exact ⟨hpg, (Submodule.mem_orthogonal_singleton_iff_inner_right).1 hpg.orth⟩

/-- **Saad (8.17)–(8.18)**: the unrelaxed NR-SOR relaxation is the Galerkin step for
`AᵀA x = Aᵀ b` on `span {e_i}`, and the `i`-th component of the new normal-equations residual
therefore vanishes. -/
theorem nrSorStep_isGalerkin (hi : (A ⬝ coordVec i) ≠ 0) (x : E n) :
    IsGalerkin (Matrix.toEuclideanLin (Aᵀ * A)) (Aᵀ ⬝ b) x (ℝ ∙ coordVec i)
        (nrSorStep A b 1 i x) ∧
      inner ℝ (A ⬝ coordVec i) (b - (A ⬝ nrSorStep A b 1 i x)) = 0 := by
  have hne : inner ℝ (coordVec i) ((Aᵀ * A) ⬝ coordVec i) ≠ 0 := by
    rw [inner_normal_coordVec]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 hi)
  have hpg := Chapter05.isProjectionApprox_iff.1
    (Chapter05.step1_isProjectionApprox (A := Aᵀ * A) (b := (Aᵀ ⬝ b)) (x := x) (coordVec i)
      (coordVec i) hne)
  rw [← nrSorStep_eq_step1] at hpg
  refine ⟨hpg, ?_⟩
  have h0 := (Submodule.mem_orthogonal_singleton_iff_inner_right).1 hpg.orth
  rwa [show (Matrix.toEuclideanLin (Aᵀ * A)) (nrSorStep A b 1 i x)
    = ((Aᵀ * A) ⬝ nrSorStep A b 1 i x) from rfl, normal_residual, inner_transpose'] at h0

/-! ### The sweeps as multiplicative projection processes -/

/-- **Saad §8.2**: the unrelaxed NR-SOR sweep is the multiplicative projection process of §5.4
for the normal equations `AᵀA x = Aᵀ b` over the coordinate family — block Gauss–Seidel with
`K_i = span {e_i}`. The NE-SOR sweep is `neSorSweep_eq_multiplicativeStep`. -/
theorem sorSweep_eq_multiplicativeSweep (h : ∀ i : Fin n, (A ⬝ coordVec i) ≠ 0) (x : E n) :
    nrSorSweep A b 1 x = Chapter05.multiplicativeSweep (coordFamily n) (Aᵀ * A) (Aᵀ ⬝ b) x := by
  have hne : ∀ i : Fin n, inner ℝ (coordVec i) ((Aᵀ * A) ⬝ coordVec i) ≠ 0 := fun i => by
    rw [inner_normal_coordVec]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 (h i))
  have hunit : ∀ i : Fin (coordFamily n).p,
      IsUnit (((coordFamily n).V i)ᵀ * (Aᵀ * A) * (coordFamily n).V i) :=
    fun i => isUnit_coordCol (hne i)
  have hrhs : Chapter05.multiplicativeSweep (coordFamily n) (Aᵀ * A) (Aᵀ ⬝ b) x
      = (List.finRange n).foldl (fun y i => Projection.pairStep
          (Matrix.toEuclideanLin (Aᵀ * A)) (Aᵀ ⬝ b) ((coordFamily n).subspace i)
          ((coordFamily n).subspace i) (Chapter05.isNondegeneratePair_subspace hunit i) y) x := by
    rw [Chapter05.multiplicativeSweep_eq hunit]
    rfl
  have hfun : (fun (y : E n) (i : Fin n) => nrSorStep A b 1 i y)
      = fun (y : E n) (i : Fin n) => Projection.pairStep
          (Matrix.toEuclideanLin (Aᵀ * A)) (Aᵀ ⬝ b) ((coordFamily n).subspace i)
          ((coordFamily n).subspace i) (Chapter05.isNondegeneratePair_subspace hunit i) y :=
    funext fun y => funext fun i => by
      rw [pairStep_eq_step1 _ (coordFamily_subspace i) (coordFamily_subspace i) (hne i),
        nrSorStep_eq_step1]
      rfl
  rw [nrSorSweep, hrhs, hfun]
  rfl

/-- **Saad §8.2**: the unrelaxed NE-SOR sweep is the multiplicative *Petrov–Galerkin* process
over the pairs `(span {Aᵀ e_i}, span {e_i})` — the same block Gauss–Seidel pattern of §5.4, in
the backbone's form. It is not `SaadSparse.Chapter05.multiplicativeSweep`, whose test space is its
trial space; the two coincide only for NR-SOR. -/
theorem neSorSweep_eq_multiplicativeStep
    (hne : ∀ i : Fin n, inner ℝ (coordVec i) (A ⬝ (Aᵀ ⬝ coordVec i)) ≠ 0) (x : E n) :
    neSorSweep A b 1 x
      = Projection.multiplicativeStep (Matrix.toEuclideanLin A) b
          (fun i => ℝ ∙ (Aᵀ ⬝ coordVec i)) (fun i => ℝ ∙ coordVec i)
          (fun i => isNondegeneratePair_span_singleton (hne i)) (List.finRange n) x := by
  have hrhs : Projection.multiplicativeStep (Matrix.toEuclideanLin A) b
        (fun i => ℝ ∙ (Aᵀ ⬝ coordVec i)) (fun i => ℝ ∙ coordVec i)
        (fun i => isNondegeneratePair_span_singleton (hne i)) (List.finRange n) x
      = (List.finRange n).foldl (fun y i => Projection.pairStep (Matrix.toEuclideanLin A) b
          (ℝ ∙ (Aᵀ ⬝ coordVec i)) (ℝ ∙ coordVec i)
          (isNondegeneratePair_span_singleton (hne i)) y) x := rfl
  have hfun : (fun (y : E n) (i : Fin n) => neSorStep A b 1 i y)
      = fun (y : E n) (i : Fin n) => Projection.pairStep (Matrix.toEuclideanLin A) b
          (ℝ ∙ (Aᵀ ⬝ coordVec i)) (ℝ ∙ coordVec i)
          (isNondegeneratePair_span_singleton (hne i)) y :=
    funext fun y => funext fun i => by
      rw [pairStep_eq_step1 _ rfl rfl (hne i), neSorStep_eq_step1]
      rfl
  rw [neSorSweep, hrhs, hfun]

/-! ### Algorithm 8.3: Cimmino's method -/

variable (A b ω)

/-- **Algorithm 8.3** (Cimmino-NR, (8.19)–(8.21)): every `δ_i = ω (r, A e_i)/‖A e_i‖₂²` is
computed from the *same* residual, and the corrections are added at once,
`x := x + ∑_i δ_i e_i`. -/
noncomputable def cimmino (x : E n) : E n :=
  x + ∑ i, (ω * inner ℝ (A ⬝ coordVec i) (b - (A ⬝ x)) / ‖A ⬝ coordVec i‖ ^ 2) • coordVec i

variable {A b ω}

/-- **Saad §8.2**: Cimmino's method is the additive projection process of §5.4 for the normal
equations `AᵀA x = Aᵀ b` over the coordinate family — Saad's own remark that "each instance is
mathematically equivalent to an orthogonal projection step for `AᵀA x = Aᵀ b` with
`K = span {e_i}`". -/
theorem cimmino_eq_additiveStep (h : ∀ i : Fin n, (A ⬝ coordVec i) ≠ 0) (x : E n) :
    cimmino A b ω x
      = Chapter05.additiveStep (coordFamily n) (Aᵀ * A) (fun _ => ω) (Aᵀ ⬝ b) x := by
  have hne : ∀ i : Fin n, inner ℝ (coordVec i) ((Aᵀ * A) ⬝ coordVec i) ≠ 0 := fun i => by
    rw [inner_normal_coordVec]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 (h i))
  have hunit : ∀ i : Fin (coordFamily n).p,
      IsUnit (((coordFamily n).V i)ᵀ * (Aᵀ * A) * (coordFamily n).V i) :=
    fun i => isUnit_coordCol (hne i)
  have hrhs : Chapter05.additiveStep (coordFamily n) (Aᵀ * A) (fun _ => ω) (Aᵀ ⬝ b) x
      = x + ∑ i, ω • (Projection.pairStep (Matrix.toEuclideanLin (Aᵀ * A)) (Aᵀ ⬝ b)
          ((coordFamily n).subspace i) ((coordFamily n).subspace i)
          (Chapter05.isNondegeneratePair_subspace hunit i) x - x) := by
    rw [Chapter05.additiveStep_eq hunit]
    rfl
  rw [cimmino, hrhs]
  refine congrArg (fun z : E n => x + z) (Finset.sum_congr rfl fun i _ => ?_)
  rw [pairStep_eq_step1 _ (coordFamily_subspace i) (coordFamily_subspace i) (hne i),
    show Projection.step1 (Matrix.toEuclideanLin (Aᵀ * A)) (Aᵀ ⬝ b) (coordVec i) (coordVec i) x
      = nrSorStep A b 1 i x from (nrSorStep_eq_step1 i x).symm, nrSorStep, add_sub_cancel_left,
    smul_smul, one_mul, mul_div_assoc]

/-! ### (8.23)–(8.25): the projectors and the residual identity -/

/-- The image of a coordinate axis under `A` is the span of the corresponding column. -/
theorem map_coordVec (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (ℝ ∙ coordVec i).map (Matrix.toEuclideanLin A) = ℝ ∙ (A ⬝ coordVec i) := by
  rw [Submodule.map_span, Set.image_singleton]

/-- **Saad (8.24)**: the least-squares projector `P_i` of (5.22) with `L_i = A K_i` is the
orthogonal projector onto the span of the `i`-th column of `A`, and
`P_i r = ((r, A e_i)/‖A e_i‖₂²) A e_i`. -/
theorem equation_8_24 {i : Fin n} (h : (A ⬝ coordVec i) ≠ 0) (r : E n) :
    Matrix.toEuclideanLin (Matrix.obliqueProj (A * coordCol i) (A * coordCol i))
        = ((ℝ ∙ (A ⬝ coordVec i)).starProjection : (E n) →ₗ[ℝ] (E n)) ∧
      (ℝ ∙ (A ⬝ coordVec i)).starProjection r
        = (inner ℝ (A ⬝ coordVec i) r / ‖A ⬝ coordVec i‖ ^ 2) • (A ⬝ coordVec i) := by
  have hgram : ((A * coordCol i)ᵀ * (A * coordCol i))
      = (coordCol i)ᵀ * (Aᵀ * A) * (coordCol i) := by
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  have hunit : IsUnit ((A * coordCol i)ᵀ * (A * coordCol i)) := by
    rw [hgram]
    refine isUnit_coordCol ?_
    rw [inner_normal_coordVec]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 h)
  refine ⟨?_, ?_⟩
  · have hls := Chapter05.leastSquares_P_i_eq_starProjection (𝒲 := coordFamily n) (A := A) (i := i)
      hunit
    rw [coordFamily_subspace] at hls
    simp only [map_coordVec] at hls
    exact hls
  · rw [Submodule.starProjection_singleton ℝ r]
    norm_num

/-- **Saad (8.23)–(8.25)**: the Cimmino residual is `r_new = (1 - ω ∑_i P_i) r`; and **P-8.8**,
`x_new = x + ω A⁻¹ (∑_i P_i) r` when `A` is nonsingular. -/
theorem equation_8_25 (h : ∀ i : Fin n, (A ⬝ coordVec i) ≠ 0) (x : E n) :
    b - (A ⬝ cimmino A b ω x)
        = (b - (A ⬝ x))
          - ω • ∑ i, (ℝ ∙ (A ⬝ coordVec i)).starProjection (b - (A ⬝ x)) ∧
      (IsUnit A → cimmino A b ω x
        = x + ω • (A⁻¹ ⬝ ∑ i, (ℝ ∙ (A ⬝ coordVec i)).starProjection (b - (A ⬝ x)))) := by
  have hstep : (A ⬝ cimmino A b ω x)
      = (A ⬝ x) + ω • ∑ i, (ℝ ∙ (A ⬝ coordVec i)).starProjection (b - (A ⬝ x)) := by
    rw [cimmino, map_add, map_sum, Finset.smul_sum]
    refine congrArg (fun z : E n => (A ⬝ x) + z) (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_smul, (equation_8_24 (h i) (b - (A ⬝ x))).2, smul_smul, div_eq_mul_inv,
      div_eq_mul_inv]
    ring_nf
  refine ⟨by rw [hstep]; abel, fun hA => ?_⟩
  have hAx : (A ⬝ cimmino A b ω x) - (A ⬝ x)
      = ω • ∑ i, (ℝ ∙ (A ⬝ coordVec i)).starProjection (b - (A ⬝ x)) := by
    rw [hstep]; abel
  have hinv : (A⁻¹ ⬝ (A ⬝ (cimmino A b ω x - x))) = cimmino A b ω x - x := by
    rw [← Chapter05.toEuclideanLin_mul_apply,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det A).1 hA), Matrix.toEuclideanLin_one]
    rfl
  have hd : (A⁻¹ ⬝ (A ⬝ (cimmino A b ω x - x)))
      = (A⁻¹ ⬝ (ω • ∑ i, (ℝ ∙ (A ⬝ coordVec i)).starProjection (b - (A ⬝ x)))) := by
    rw [map_sub, hAx]
  rw [hd, map_smul] at hinv
  rw [hinv]
  abel

/-! ### P-8.2 and (8.22): Cimmino with normalized columns -/

/-- **P-8.2**: if the columns of `A` have unit Euclidean norm then Cimmino's step is
`x_new = x + ω (Aᵀ b - Aᵀ A x)`, Richardson's iteration for the normal equations. In general it
is Richardson preconditioned by the diagonal of `AᵀA`, whose `i`-th entry is `‖A e_i‖₂²`.

The normalization is of the *columns* `A e_i`, as in Algorithm 8.3 and in the text of §8.2.2
("if the columns are not normalized by their 2-norms"); P-8.2 writes `‖Aᵀ e_i‖₂ = 1`, the
rows, which is not the hypothesis that makes the step Richardson's. -/
theorem cimmino_eq_richardson (h : ∀ i : Fin n, ‖A ⬝ coordVec i‖ = 1) (x : E n) :
    cimmino A b ω x = x + ω • ((Aᵀ ⬝ b) - ((Aᵀ * A) ⬝ x)) ∧
      WithLp.ofLp (cimmino A b ω x)
        = Chapter04.richardsonStep (Aᵀ * A) ω (Aᵀ *ᵥ WithLp.ofLp b) (WithLp.ofLp x) := by
  have hsum : ∑ i, (ω * inner ℝ (A ⬝ coordVec i) (b - (A ⬝ x)) / ‖A ⬝ coordVec i‖ ^ 2)
      • coordVec i = ω • (Aᵀ ⬝ (b - (A ⬝ x))) := by
    have hb := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr' (Aᵀ ⬝ (b - (A ⬝ x)))
    rw [← hb, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h i, EuclideanSpace.basisFun_apply, smul_smul,
      show EuclideanSpace.single i (1 : ℝ) = coordVec i from rfl, inner_transpose']
    norm_num
  have h1 : cimmino A b ω x = x + ω • ((Aᵀ ⬝ b) - ((Aᵀ * A) ⬝ x)) := by
    rw [cimmino, hsum, normal_residual]
  refine ⟨h1, ?_⟩
  rw [h1, Chapter04.richardsonStep, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_sub]
  rfl

/-- **Saad (8.22)**: with normalized columns, Cimmino's method converges for every right-hand
side and every starting vector exactly when `0 < ω < 2/λ_max(AᵀA)`, and the optimal parameter is
`ω_opt = 2/(λ_min + λ_max)` — Example 4.1 applied to the symmetric positive definite `AᵀA`. The
positivity of `λ_min` is what nonsingularity of `A` provides. -/
theorem equation_8_22 {lmin lmax : ℝ} (hsub : spectrum ℝ (Aᵀ * A) ⊆ Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ (Aᵀ * A)) (hmax : lmax ∈ spectrum ℝ (Aᵀ * A)) (hpos : 0 < lmin)
    (hω : ω ≠ 0) :
    ((∀ c z₀ : Fin n → ℝ, ∃ z,
        Tendsto (fun k => (Chapter04.richardsonStep (Aᵀ * A) ω c)^[k] z₀) atTop (𝓝 z)) ↔
      0 < ω ∧ ω < 2 / lmax) ∧
      IsMinOn (fun ω : ℝ => Matrix.complexSpectralRadius (1 - ω • (Aᵀ * A))) (Set.Ioi 0)
        (2 / (lmin + lmax)) := by
  have hherm : (Aᵀ * A).IsHermitian := by
    have h := Matrix.isHermitian_conjTranspose_mul_self A
    rwa [Chapter05.conjTranspose_eq_transpose] at h
  exact ⟨Chapter04.example_4_1_tendsto_iff hherm hsub hmin hmax hpos hω,
    (Chapter04.example_4_1_opt hherm hsub hmin hmax hpos).1⟩

/-! ### P-8.2 (a), (b): Cimmino with unnormalized columns -/

/-- The `i`-th coordinate of a vector is its inner product with `e_i`. -/
private theorem inner_coordVec (w : E n) (i : Fin n) :
    inner ℝ (coordVec i) w = WithLp.ofLp w i := by
  rw [coordVec, EuclideanSpace.inner_single_left]
  simp

/-- A diagonal matrix acts coordinate by coordinate. -/
private theorem inner_coordVec_diagonal (d : Fin n → ℝ) (w : E n) (i : Fin n) :
    inner ℝ (coordVec i) ((Matrix.diagonal d) ⬝ w) = d i * inner ℝ (coordVec i) w := by
  rw [inner_coordVec, inner_coordVec,
    show WithLp.ofLp ((Matrix.diagonal d) ⬝ w) = Matrix.diagonal d *ᵥ WithLp.ofLp w from rfl,
    Matrix.mulVec_diagonal]

/-- The expansion of `D w` in the coordinate basis, for a diagonal `D`. -/
private theorem diagonal_apply_eq_sum (d : Fin n → ℝ) (w : E n) :
    ((Matrix.diagonal d) ⬝ w) = ∑ i, (d i * inner ℝ (coordVec i) w) • coordVec i := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr' ((Matrix.diagonal d) ⬝ w)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.basisFun_apply, show EuclideanSpace.single i (1 : ℝ) = coordVec i from rfl,
    inner_coordVec_diagonal]

/-- **P-8.2**: the diagonal `D = diag(‖A e_i‖₂²)` of the normal-equations matrix `AᵀA`, which is
the preconditioner Cimmino's method carries when the columns of `A` are not normalized. -/
noncomputable def colNormDiag (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => ‖A ⬝ coordVec i‖ ^ 2

/-- The entrywise inverse `D⁻¹` of `SaadSparse.Chapter08.colNormDiag`. It is written entrywise
rather than as `(colNormDiag A)⁻¹` so that a vanishing column of `A` gives `0` in that place, as
the algorithm's own division by zero does; when no column vanishes the two agree
(`colNormDiag_mul_colNormDiagInv`). -/
noncomputable def colNormDiagInv (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => (‖A ⬝ coordVec i‖ ^ 2)⁻¹

/-- `D D⁻¹ = I` when no column of `A` vanishes. -/
theorem colNormDiag_mul_colNormDiagInv (h : ∀ i : Fin n, (A ⬝ coordVec i) ≠ 0) :
    colNormDiag A * colNormDiagInv A = 1 := by
  rw [colNormDiag, colNormDiagInv, Matrix.diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun i => ?_)
  exact mul_inv_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.2 (h i)))

/-- **P-8.2 (a), (b)**: without the normalization of the columns, Cimmino's step is
`x_new = x + ω D⁻¹ (Aᵀ b - Aᵀ A x)` with `D = diag(‖A e_i‖₂²)` — Richardson's iteration for the
normal equations `AᵀA x = Aᵀ b`, preconditioned by the diagonal of `AᵀA`.

No hypothesis is needed: a vanishing column makes the book's `δ_i` and the corresponding entry of
`D⁻¹` zero alike. `cimmino_eq_richardson` is the special case `D = I` that §8.2.2 states in the
text. -/
theorem cimmino_eq_richardson_diag (x : E n) :
    cimmino A b ω x = x + ω • (colNormDiagInv A ⬝ ((Aᵀ ⬝ b) - ((Aᵀ * A) ⬝ x))) := by
  rw [cimmino, normal_residual, colNormDiagInv, diagonal_apply_eq_sum, Finset.smul_sum]
  refine congrArg (fun z : E n => x + z) (Finset.sum_congr rfl fun i _ => ?_)
  rw [smul_smul, inner_transpose', div_eq_mul_inv]
  ring_nf

/-! ### P-8.3: the row form of Cimmino's method -/

variable (A b ω)

/-- **P-8.3**: Cimmino's method in its original, *row* form — Jacobi for the normal equations of
the second kind `A Aᵀ u = b`, written in `x = Aᵀ u`. Every correction `δ_i Aᵀ e_i` is the
Kaczmarz relaxation `neSorStep` computed from the *same* residual, and they are added at once. -/
noncomputable def cimminoNE (x : E n) : E n :=
  x + ∑ i, (ω * inner ℝ (coordVec i) (b - (A ⬝ x)) / ‖Aᵀ ⬝ coordVec i‖ ^ 2) • (Aᵀ ⬝ coordVec i)

variable {A b ω}

/-- **P-8.3**: the row form of Cimmino's method is the additive *Petrov–Galerkin* process of §5.4
over the pairs `(span {Aᵀ e_i}, span {e_i})`, exactly as `neSorSweep_eq_multiplicativeStep` makes
Kaczmarz's method the multiplicative one over the same pairs. It is not
`SaadSparse.Chapter05.additiveStep`, whose test space is its trial space; only the column form
`cimmino` is of that kind. -/
theorem cimminoNE_eq_additiveStep
    (hne : ∀ i : Fin n, inner ℝ (coordVec i) (A ⬝ (Aᵀ ⬝ coordVec i)) ≠ 0) (x : E n) :
    cimminoNE A b ω x
      = Projection.additiveStep (Matrix.toEuclideanLin A) b
          (fun i => ℝ ∙ (Aᵀ ⬝ coordVec i)) (fun i => ℝ ∙ coordVec i)
          (fun i => isNondegeneratePair_span_singleton (hne i)) (fun _ => ω) x := by
  rw [cimminoNE, Projection.additiveStep]
  refine congrArg (fun z : E n => x + z) (Finset.sum_congr rfl fun i _ => ?_)
  rw [pairStep_eq_step1 _ rfl rfl (hne i),
    show Projection.step1 (Matrix.toEuclideanLin A) b (Aᵀ ⬝ coordVec i) (coordVec i) x
      = neSorStep A b 1 i x from (neSorStep_eq_step1 i x).symm, neSorStep, add_sub_cancel_left,
    smul_smul, one_mul, mul_div_assoc]

/-- **P-8.3**: the row form *is* Jacobi for `A Aᵀ u = b`, read through `x = Aᵀ u`. With
`D' = diag(‖Aᵀ e_i‖₂²)` the diagonal of `A Aᵀ`, one step of the `u`-iteration is
`u_new = u + ω D'⁻¹ (b - A Aᵀ u)`, and applying `Aᵀ` to it gives `cimminoNE`. This is the
derivation the problem asks for: the row version of the column-wise `cimmino_eq_richardson_diag`,
and Cimmino's own method. -/
theorem cimminoNE_eq_jacobi (u : E n) :
    cimminoNE A b ω (Aᵀ ⬝ u)
      = (Aᵀ ⬝ (u + ω • (colNormDiagInv (Aᵀ) ⬝ (b - ((A * Aᵀ) ⬝ u))))) := by
  rw [map_add, map_smul, colNormDiagInv, diagonal_apply_eq_sum, map_sum, Finset.smul_sum,
    cimminoNE]
  refine congrArg (fun z : E n => (Aᵀ ⬝ u) + z) (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_smul, smul_smul, Chapter05.toEuclideanLin_mul_apply, div_eq_mul_inv]
  congr 1
  ring

/-! ### (8.26)–(8.27): the block form -/

variable (A b ω)

/-- **Saad (8.26)–(8.27)**: the block Cimmino step for a partition of the columns into blocks
`V_1, …, V_p`: `x_new = x + ω ∑_i V_i d_i` with `d_i = (A_iᵀ A_i)⁻¹ A_iᵀ r` and `A_i = A V_i`.
The scalar division of Algorithm 8.3 is replaced by the least-squares problem
`min_d ‖r - A_i d‖₂` (`blockCimmino_isMinRes`). -/
noncomputable def blockCimmino (𝒱 : Chapter05.ProjFamily n) (x : E n) : E n :=
  x + ∑ i, ω • ((𝒱.V i * ((A * 𝒱.V i)ᵀ * (A * 𝒱.V i))⁻¹ * (A * 𝒱.V i)ᵀ) ⬝ (b - (A ⬝ x)))

variable {A b ω}

/-- The block form is the additive projection process of §5.4 for the normal equations over the
family, which for one-dimensional blocks is `cimmino_eq_additiveStep`. -/
theorem blockCimmino_eq_additiveStep (𝒱 : Chapter05.ProjFamily n) (x : E n) :
    blockCimmino A b ω 𝒱 x = Chapter05.additiveStep 𝒱 (Aᵀ * A) (fun _ => ω) (Aᵀ ⬝ b) x := by
  rw [blockCimmino, Chapter05.additiveStep]
  refine congrArg (fun z : E n => x + z) (Finset.sum_congr rfl fun i _ => ?_)
  refine congrArg (fun z : E n => ω • z) ?_
  have hmat : 𝒱.V i * ((A * 𝒱.V i)ᵀ * (A * 𝒱.V i))⁻¹ * (A * 𝒱.V i)ᵀ
      = (𝒱.V i * ((𝒱.V i)ᵀ * (Aᵀ * A) * 𝒱.V i)⁻¹ * (𝒱.V i)ᵀ) * Aᵀ := by
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [Chapter05.corrector, normal_residual, ← Chapter05.toEuclideanLin_mul_apply, hmat]

/-- **Saad (8.26)–(8.27)**: the block correction `d_i` solves the least-squares problem
`min_d ‖r - A_i d‖₂`, so each substep reduces the residual as far as the columns of `A_i`
allow. This is §8.1's `equation_8_1` for the matrix `A_i = A V_i`. -/
theorem blockCimmino_isMinRes {𝒱 : Chapter05.ProjFamily n} {i : Fin 𝒱.p}
    (h : IsUnit ((A * 𝒱.V i)ᵀ * (A * 𝒱.V i))) (r : E n) :
    ∀ d : EuclideanSpace ℝ (Fin (𝒱.size i)),
      ‖r - ((A * 𝒱.V i) ⬝ ((((A * 𝒱.V i)ᵀ * (A * 𝒱.V i))⁻¹ * (A * 𝒱.V i)ᵀ) ⬝ r))‖
        ≤ ‖r - ((A * 𝒱.V i) ⬝ d)‖ := by
  have hH : (A * 𝒱.V i)ᴴ = (A * 𝒱.V i)ᵀ := Chapter05.conjTranspose_eq_transpose _
  have hnormal : (((A * 𝒱.V i)ᴴ * (A * 𝒱.V i))
      ⬝ ((((A * 𝒱.V i)ᵀ * (A * 𝒱.V i))⁻¹ * (A * 𝒱.V i)ᵀ) ⬝ r)) = ((A * 𝒱.V i)ᴴ ⬝ r) := by
    rw [hH, ← toEuclideanLin_mul_apply, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 h), Matrix.one_mul]
  exact (equation_8_1 (A * 𝒱.V i) r _).1 hnormal

/-! ### §8.2.1: the sweeps converge for `0 < ω < 2`

The back-reference to Chapter 4 that closes §8.2.1: `AᵀA` is symmetric positive definite when `A`
is nonsingular, so Theorem 4.10 applies to it and the NR-SOR sweep converges for every
`0 < ω < 2`. The bridge is `nrSorSweep_eq_sorStep`: a whole NR-SOR sweep *is* one SOR step for the
normal equations, because relaxation `i` changes only the `i`-th entry and changes it by
`ω (Aᵀ b - AᵀA x)_i / (AᵀA)_ii`, using the entries below `i` already updated and those above `i`
not yet — which is the SOR recursion in the ordering `i = 1, …, n`.
-/

section Convergence

variable {A : Matrix (Fin n) (Fin n) ℝ} {b : E n} {ω : ℝ}

/-- The `i`-th diagonal entry of the normal-equations matrix is the squared norm of the `i`-th
column of `A`. -/
theorem normal_diag (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (Aᵀ * A) i i = ‖A ⬝ coordVec i‖ ^ 2 := by
  rw [← inner_normal_coordVec A i, inner_coordVec]
  simp [coordVec, Matrix.mulVec_single, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- One NR-SOR relaxation changes only the `i`-th entry, and changes it by
`ω (Aᵀ b - AᵀA x)_i / (AᵀA)_ii`. -/
private theorem ofLp_nrSorStep (i : Fin n) (x : E n) :
    WithLp.ofLp (nrSorStep A b ω i x)
      = Function.update (WithLp.ofLp x) i
          (WithLp.ofLp x i + ω * WithLp.ofLp ((Aᵀ ⬝ b) - ((Aᵀ * A) ⬝ x)) i / (Aᵀ * A) i i) := by
  have hnum : inner ℝ (A ⬝ coordVec i) (b - (A ⬝ x))
      = WithLp.ofLp ((Aᵀ ⬝ b) - ((Aᵀ * A) ⬝ x)) i := by
    rw [normal_residual, ← inner_transpose', inner_coordVec]
  rw [nrSorStep, hnum, ← normal_diag]
  funext j
  rw [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases eq_or_ne j i with rfl | hj
  · rw [Function.update_self]
    simp [coordVec]
  · rw [Function.update_of_ne hj]
    simp [coordVec, hj]

/-- The relaxed entry after one NR-SOR relaxation. -/
private theorem ofLp_nrSorStep_self (i : Fin n) (x : E n) :
    WithLp.ofLp (nrSorStep A b ω i x) i
      = WithLp.ofLp x i + ω * WithLp.ofLp ((Aᵀ ⬝ b) - ((Aᵀ * A) ⬝ x)) i / (Aᵀ * A) i i := by
  rw [ofLp_nrSorStep, Function.update_self]

/-- Every other entry is left alone. -/
private theorem ofLp_nrSorStep_of_ne {i j : Fin n} (hj : j ≠ i) (x : E n) :
    WithLp.ofLp (nrSorStep A b ω i x) j = WithLp.ofLp x j := by
  rw [ofLp_nrSorStep, Function.update_of_ne hj]

/-- The first `k` relaxations of an NR-SOR sweep. -/
private noncomputable def partialSweep (A : Matrix (Fin n) (Fin n) ℝ) (b : E n) (ω : ℝ) (k : ℕ)
    (x : E n) : E n :=
  ((List.finRange n).take k).foldl (fun y i => nrSorStep A b ω i y) x

private theorem partialSweep_succ {k : ℕ} (hk : k < n) (x : E n) :
    partialSweep A b ω (k + 1) x = nrSorStep A b ω ⟨k, hk⟩ (partialSweep A b ω k x) := by
  rw [partialSweep, partialSweep, List.take_add_one,
    List.getElem?_eq_getElem (by simpa using hk), List.foldl_append]
  simp

private theorem partialSweep_card (x : E n) : partialSweep A b ω n x = nrSorSweep A b ω x := by
  rw [partialSweep, nrSorSweep, List.take_of_length_le (by simp)]

/-- Entries from `k` on are untouched by the first `k` relaxations. -/
private theorem ofLp_partialSweep_of_le (x : E n) :
    ∀ k : ℕ, k ≤ n → ∀ j : Fin n, k ≤ (j : ℕ) →
      WithLp.ofLp (partialSweep A b ω k x) j = WithLp.ofLp x j := by
  intro k
  induction k with
  | zero => intro _ j _; rfl
  | succ k ih =>
    intro hk j hj
    have hkn : k < n := lt_of_lt_of_le (Nat.lt_succ_self k) hk
    have hne : j ≠ ⟨k, hkn⟩ := by
      simp only [ne_eq, Fin.ext_iff]
      omega
    rw [partialSweep_succ hkn, ofLp_nrSorStep_of_ne hne, ih hkn.le j (by omega)]

/-- Entries below `k` are frozen once the first `k` relaxations are done. -/
private theorem ofLp_partialSweep_stable (x : E n) :
    ∀ l : ℕ, l ≤ n → ∀ k : ℕ, k ≤ l → ∀ j : Fin n, (j : ℕ) < k →
      WithLp.ofLp (partialSweep A b ω l x) j = WithLp.ofLp (partialSweep A b ω k x) j := by
  intro l
  induction l with
  | zero => intro _ k hk j hj; omega
  | succ l ih =>
    intro hl k hk j hj
    rcases eq_or_lt_of_le hk with rfl | hkl
    · rfl
    have hln : l < n := lt_of_lt_of_le (Nat.lt_succ_self l) hl
    have hne : j ≠ ⟨l, hln⟩ := by
      simp only [ne_eq, Fin.ext_iff]
      omega
    rw [partialSweep_succ hln, ofLp_nrSorStep_of_ne hne, ih hln.le k (by omega) j hj]

/-- **Saad §8.2.1**: one NR-SOR sweep is one SOR step for the normal equations `AᵀA x = Aᵀ b`.
Relaxation `i` sets the `i`-th entry from the entries already updated below `i` and the old ones
above it, which is exactly the recursion (4.12) defines. -/
theorem nrSorSweep_eq_sorStep (hd : IsUnit (Matrix.diagPart (Aᵀ * A))) (hω : ω ≠ 0) (x : E n) :
    WithLp.ofLp (nrSorSweep A b ω x)
      = Chapter04.sorStep (Aᵀ * A) ω (WithLp.ofLp ((Aᵀ ⬝ b) : E n)) (WithLp.ofLp x) := by
  have hdiag : ∀ i : Fin n, (Aᵀ * A) i i ≠ 0 := (Matrix.isUnit_diagPart_iff _).1 hd
  have hres : (Chapter04.D (Aᵀ * A) - ω • Chapter04.E (Aᵀ * A)) *ᵥ
      (WithLp.ofLp (nrSorSweep A b ω x) - WithLp.ofLp x)
      = ω • (WithLp.ofLp ((Aᵀ ⬝ b) : E n) - (Aᵀ * A) *ᵥ WithLp.ofLp x) := by
    funext i
    -- the state after the first `i` relaxations agrees with the finished sweep below `i` and
    -- with the starting vector from `i` on
    have hzlt : ∀ j : Fin n, j < i →
        WithLp.ofLp (partialSweep A b ω (i : ℕ) x) j
          = WithLp.ofLp (nrSorSweep A b ω x) j := by
      intro j hj
      rw [← partialSweep_card (A := A) (b := b) (ω := ω) x]
      exact (ofLp_partialSweep_stable x n le_rfl (i : ℕ) i.2.le j hj).symm
    have hzge : ∀ j : Fin n, ¬ j < i →
        WithLp.ofLp (partialSweep A b ω (i : ℕ) x) j = WithLp.ofLp x j := fun j hj =>
      ofLp_partialSweep_of_le x (i : ℕ) i.2.le j (by omega)
    -- the `i`-th entry of the finished sweep is the one relaxation `i` produced
    have hyi : WithLp.ofLp (nrSorSweep A b ω x) i
        = WithLp.ofLp x i
          + ω * WithLp.ofLp ((Aᵀ ⬝ b) - ((Aᵀ * A) ⬝ partialSweep A b ω (i : ℕ) x)) i
            / (Aᵀ * A) i i := by
      have h1 : WithLp.ofLp (nrSorSweep A b ω x) i
          = WithLp.ofLp (partialSweep A b ω ((i : ℕ) + 1) x) i := by
        rw [← partialSweep_card (A := A) (b := b) (ω := ω) x]
        exact ofLp_partialSweep_stable x n le_rfl ((i : ℕ) + 1) i.2 i (Nat.lt_succ_self _)
      have h2 : (⟨(i : ℕ), i.2⟩ : Fin n) = i := rfl
      rw [h1, partialSweep_succ i.2, h2, ofLp_nrSorStep_self,
        ofLp_partialSweep_of_le x (i : ℕ) i.2.le i le_rfl]
    have hmv : ∀ w : E n, WithLp.ofLp ((Aᵀ ⬝ b) - ((Aᵀ * A) ⬝ w)) i
        = WithLp.ofLp ((Aᵀ ⬝ b) : E n) i - ((Aᵀ * A) *ᵥ WithLp.ofLp w) i := fun _ => rfl
    have hkey : (Aᵀ * A) i i * (WithLp.ofLp (nrSorSweep A b ω x) i - WithLp.ofLp x i)
        = ω * (WithLp.ofLp ((Aᵀ ⬝ b) : E n) i
          - ((Aᵀ * A) *ᵥ WithLp.ofLp (partialSweep A b ω (i : ℕ) x)) i) := by
      rw [hyi, add_sub_cancel_left, hmv, mul_div_cancel₀ _ (hdiag i)]
    -- splitting a row sum at `i`
    have hsplit : ∀ w : Fin n → ℝ, ((Aᵀ * A) *ᵥ w) i
        = ∑ j ∈ Finset.univ.filter (· < i), (Aᵀ * A) i j * w j
          + ∑ j ∈ Finset.univ.filter (fun j => ¬ j < i), (Aᵀ * A) i j * w j := by
      intro w
      change ∑ j, (Aᵀ * A) i j * w j = _
      exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hlow : ∑ j ∈ Finset.univ.filter (· < i),
          (Aᵀ * A) i j * (WithLp.ofLp (nrSorSweep A b ω x) j - WithLp.ofLp x j)
        = ((Aᵀ * A) *ᵥ WithLp.ofLp (partialSweep A b ω (i : ℕ) x)) i
          - ((Aᵀ * A) *ᵥ WithLp.ofLp x) i := by
      have hexp : ∑ j ∈ Finset.univ.filter (· < i),
            (Aᵀ * A) i j * (WithLp.ofLp (nrSorSweep A b ω x) j - WithLp.ofLp x j)
          = ∑ j ∈ Finset.univ.filter (· < i),
              (Aᵀ * A) i j * WithLp.ofLp (nrSorSweep A b ω x) j
            - ∑ j ∈ Finset.univ.filter (· < i), (Aᵀ * A) i j * WithLp.ofLp x j := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      have h1 : ∑ j ∈ Finset.univ.filter (· < i),
            (Aᵀ * A) i j * WithLp.ofLp (partialSweep A b ω (i : ℕ) x) j
          = ∑ j ∈ Finset.univ.filter (· < i),
            (Aᵀ * A) i j * WithLp.ofLp (nrSorSweep A b ω x) j :=
        Finset.sum_congr rfl fun j hj => by rw [hzlt j (Finset.mem_filter.1 hj).2]
      have h2 : ∑ j ∈ Finset.univ.filter (fun j => ¬ j < i),
            (Aᵀ * A) i j * WithLp.ofLp (partialSweep A b ω (i : ℕ) x) j
          = ∑ j ∈ Finset.univ.filter (fun j => ¬ j < i),
            (Aᵀ * A) i j * WithLp.ofLp x j :=
        Finset.sum_congr rfl fun j hj => by rw [hzge j (Finset.mem_filter.1 hj).2]
      rw [hexp, hsplit, hsplit, h1, h2]
      ring
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Matrix.sub_mulVec, Chapter04.D_mulVec,
      Matrix.smul_mulVec, Chapter04.E_mulVec]
    rw [hlow, hkey]
    ring
  have hunit := Chapter04.isUnit_D_sub_smul_E hd hω
  have hstep : (Chapter04.D (Aᵀ * A) - ω • Chapter04.E (Aᵀ * A)) *ᵥ
      (WithLp.ofLp (nrSorSweep A b ω x) - WithLp.ofLp x)
      = (Chapter04.D (Aᵀ * A) - ω • Chapter04.E (Aᵀ * A)) *ᵥ
        (Chapter04.sorStep (Aᵀ * A) ω (WithLp.ofLp ((Aᵀ ⬝ b) : E n)) (WithLp.ofLp x)
          - WithLp.ofLp x) := by
    rw [hres, Chapter04.sorStep_sub hd hω]
  exact sub_left_inj.mp (Matrix.mulVec_injective_of_isUnit hunit hstep)

/-- **Saad §8.2.1**: because `AᵀA` is symmetric positive definite whenever `A` is nonsingular,
Theorem 4.10 applies to it, and the NR-SOR sweep converges for every `0 < ω < 2` — from every
starting vector, to the solution of the normal equations `AᵀA x = Aᵀ b`. The book states this as a
back-reference to Chapter 4; `nrSorSweep_eq_sorStep` is what makes the reference legitimate. -/
theorem sorSweep_tendsto (hA : IsUnit A) (hω0 : 0 < ω) (hω2 : ω < 2) (x₀ : E n) :
    Tendsto (fun k => WithLp.ofLp ((nrSorSweep A b ω)^[k] x₀)) atTop
      (𝓝 ((Aᵀ * A)⁻¹ *ᵥ WithLp.ofLp ((Aᵀ ⬝ b) : E n))) := by
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA
  have hinjVec : Function.Injective (Aᵀ * A).mulVec := by
    refine Matrix.mulVec_injective_of_isUnit ?_
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, Matrix.det_transpose]
    exact hAdet.mul hAdet
  have hposdiag : ∀ i : Fin n, 0 < (Aᵀ * A) i i := by
    intro i
    rw [normal_diag]
    have hne : (A ⬝ coordVec i) ≠ 0 := by
      intro h
      have hzero : (Aᵀ * A) *ᵥ WithLp.ofLp (coordVec i) = (Aᵀ * A) *ᵥ 0 := by
        rw [Matrix.mulVec_zero, show ((Aᵀ * A) *ᵥ WithLp.ofLp (coordVec i))
            = WithLp.ofLp ((Aᵀ * A) ⬝ coordVec i) from rfl,
          Chapter05.toEuclideanLin_mul_apply,
          show (Matrix.toEuclideanLin A) (coordVec i) = (A ⬝ coordVec i) from rfl, h, map_zero]
        rfl
      exact absurd (congrFun (hinjVec hzero) i) (by simp [coordVec])
    positivity
  have hd : IsUnit (Matrix.diagPart (Aᵀ * A)) :=
    (Matrix.isUnit_diagPart_iff _).2 fun i => (hposdiag i).ne'
  have hsymm : (Aᵀ * A).IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hposdef : (Aᵀ * A).PosDef := by
    have h := Matrix.PosDef.conjTranspose_mul_self A (Matrix.mulVec_injective_of_isUnit hA)
    rwa [Chapter05.conjTranspose_eq_transpose] at h
  have hρ : Matrix.complexSpectralRadius
      ((Aᵀ * A).sorSplitting hd hω0.ne').iterationOperator < 1 :=
    (Chapter04.theorem_4_10 hsymm hposdiag hd hω0 hω2).2 hposdef
  have hiter : ∀ k : ℕ, WithLp.ofLp ((nrSorSweep A b ω)^[k] x₀)
      = (Chapter04.sorStep (Aᵀ * A) ω (WithLp.ofLp ((Aᵀ ⬝ b) : E n)))^[k] (WithLp.ofLp x₀) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih,
        nrSorSweep_eq_sorStep hd hω0.ne']
  simp only [hiter]
  rw [Chapter04.sorStep_eq hd hω0.ne']
  exact Chapter04.Splitting.tendsto_step _ hρ _ _

end Convergence

end SaadSparse.Chapter08
