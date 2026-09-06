import NumlibSurface.SaadSparse.Chapter04.Section02
import NumlibSurface.SaadSparse.Chapter05.Section03
import NumlibSurface.SaadSparse.Chapter05.Section04
import NumlibSurface.SaadSparse.Chapter08.Section01

/-!
# Saad §8.2: row projection methods

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §8.2 , with P-8.2 and P-8.8.

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
  parameter — is Example 4.1 applied to `AᵀA` (`equation_8_22`).
* `blockCimmino` is (8.26)–(8.27), the same statement with `dim K_i > 1` and a least-squares
  subproblem in place of the scalar division.

The row/column duality of P-8.3 is the exchange of `A` and `Aᵀ` and is not stated separately.
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

@[simp] theorem coordFamily_p : (coordFamily n).p = n := rfl

@[simp] theorem coordFamily_V (i : Fin n) : (coordFamily n).V i = coordCol i := rfl

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
is Richardson preconditioned by the diagonal of `AᵀA`, whose `i`-th entry is `‖A e_i‖₂²`. -/
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

end SaadSparse.Chapter08
