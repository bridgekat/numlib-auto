/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Krylov.Iterate
import Numlib.Krylov.Relations
import Numlib.LinearAlgebra.Matrix.PlaneRotation

/-!
# Hessenberg relations, FOM and GMRES in coordinates, and Givens rotations

Many Krylov methods build vectors $z_j$ and $v_j$ with a **Hessenberg relation**
$A z_j = \sum_{i \le j+1} h_{ij} v_i$, where the coefficients $h_{ij}$ vanish for $i > j + 1$. The
Arnoldi process is the case $z = v$ with orthonormal $v_j$ ([saad2003iterative], (6.6)–(6.7));
flexible GMRES ([saad2003iterative], (9.22), with $z_j = M_j^{-1} v_j$ for a preconditioner that
changes from step to step) and TFQMR ([saad2003iterative], (7.70)) use two different families. For
$r_0 = b - A x_0 = \beta v_0$, the residual of $x_0 + \sum_{j<m} y_j z_j$ is
$\sum_{i \le m} (\beta e_1 - \bar{H}_m y)_i v_i$, where $\bar{H}_m$ is the $(m + 1) \times m$ matrix
of the coefficients. For the Arnoldi basis this reduces FOM and GMRES to small problems in
coordinates ([saad2003iterative], (6.16)–(6.17), (6.28)–(6.30)): for $m$ up to the grade of $r_0$,
the Galerkin iterate is $x_0 + V_m y$ with $H_m y = \beta e_1$, and the minimal-residual iterate is
$x_0 + V_m y$ with $y$ the least-squares solution of $\bar{H}_m y \approx \beta e_1$.

The least-squares problem is solved by Givens rotations ([saad2003iterative], (6.37), (6.44)–(6.47),
(6.80)–(6.81); [choi2006iterative], §2.2.3; [fong2012cg], §4.2). The rotations
$\Omega_0, \dots, \Omega_{m-1}$ triangularize $\bar{H}_m$, and they carry $\beta e_1$ to
$(g_0, \dots, g_{m-1}, \gamma_m)$ with $\gamma_{k+1} = -s_k \gamma_k$. The file proves that the
GMRES residual has norm $\|r^G_m\| = |\gamma_m|$ ([saad2003iterative], (6.42)), that
$|s_m| = \|r^G_{m+1}\| / \|r^G_m\|$, that $|c_m| = \|r^G_{m+1}\| / \|r^F_{m+1}\|$, and that
$H_{m+1}$ is nonsingular if and only if $c_m \neq 0$ ([saad2003iterative], Proposition 6.9, (6.75),
Lemma 6.16). As long as no rotation degenerates, the residual vector itself is $r^G_m = \gamma_m
\sum_i \overline{(Q_m)_{m,i}} \, v_i$, where $Q_m = \Omega_{m-1} \cdots \Omega_0$, and the last row
of $Q_m$ satisfies a simple recurrence in $m$; this gives a recurrence between consecutive residuals
([choi2006iterative], Lemma 2.18; `Lanczos.residual_minRes_succ_eq` in `Numlib.Krylov.Singular`).
Transposed, the same factorization gives the minimum-norm solution of the underdetermined system
$\bar{H}_m^H y = c$ that SYMMLQ needs ([golub2013matrix], §11.4.1).

## Main definitions

* `Krylov.hessenbergOf`, `Krylov.hessenbergSqOf`: the matrices $\bar{H}_m$ and $H_m$ of a
  coefficient function $h$.
* `Krylov.HessenbergRelation₂`, `Krylov.HessenbergRelation`: the Hessenberg relation for two
  families $z$, $v$, and for one family.
* `Krylov.rotated`: the coefficients after the first $k$ Givens rotations.
* `Krylov.givensRho`, `Krylov.givensC`, `Krylov.givensS`, `Krylov.gamma`, `Krylov.gvec`: the
  rotation parameters $\rho_k$, $c_k$, $s_k$ and the rotated right-hand side $\gamma_k$, $g_k$.
* `Krylov.givensMatrix`, `Krylov.givensQ`: the rotation $\Omega_k$ and the product
  $Q_m = \Omega_{m-1} \cdots \Omega_0$.

## Main results

* `Krylov.HessenbergRelation₂.residual_eq`, `Krylov.HessenbergRelation₂.residual_eq_of_mulVec_eq`:
  the residual in the basis $v$, and the Galerkin residual $-(h_{m,m-1} y_{m-1}) v_m$
  ([saad2003iterative], (6.18), (6.27), Proposition 6.7).
* `Krylov.isGalerkinIterate_iff_mulVec_eq`, `Krylov.existsUnique_isGalerkinIterate_iff_isUnit`: FOM
  in coordinates, and its existence if and only if $H_m$ is nonsingular.
* `Krylov.isMinResidualIterate_iff_isMinOn`,
  `Krylov.isMinResidualIterate_of_unitary_mul_hessenberg`: GMRES in coordinates, and through any
  unitary triangularization of $\bar{H}_m$.
* `Krylov.givensQ_mul_hessenbergOf`, `Krylov.givensQ_mem_unitaryGroup`: $Q_m \bar{H}_m = \bar{R}_m$,
  and $Q_m$ is unitary when no rotation degenerates.
* `Krylov.conjTranspose_hessenbergOf_mulVec_givensQ_snoc`: the minimum-norm solution of
  $\bar{H}_m^H y = c$.
* `Krylov.IsMinResidualIterate.norm_residual_eq_norm_gamma`: $\|r^G_m\| = |\gamma_m|$ below the
  grade.
* `Krylov.IsMinResidualIterate.residual_eq_gamma_smul_sum`: $r^G_m = \gamma_m \sum_i
  \overline{(Q_m)_{m,i}} \, v_i$ when no rotation degenerates before step $m$.
* `Krylov.IsMinResidualIterate.norm_residual_succ_eq`,
  `Krylov.isUnit_hessenbergSq_iff_givensC_ne_zero`,
  `Krylov.IsGalerkinIterate.norm_residual_eq_div_norm_givensC`: the meaning of $s_m$ and $c_m$ for
  GMRES and FOM.

## Notation

* $\bar{H}_m$ and $H_m$: the $(m + 1) \times m$ and $m \times m$ matrices $(h_{ij})$. For the
  Arnoldi process they are `Arnoldi.hessenberg` and `Arnoldi.hessenbergSq`.
* $V_m y = \sum_{j<m} y_j v_j$, and $\beta e_1 \in \mathbb{K}^m$ is the vector with first entry
  $\beta$ and all other entries $0$ (`Krylov.firstVec`).
* $R^{(k)}$: the coefficient array after $k$ rotations (`Krylov.rotated h k`). $\bar{R}_m$ and $R_m$
  are the $(m + 1) \times m$ and $m \times m$ matrices of $R^{(m)}$.
* $r^G_m$ and $r^F_m$: the residuals of the minimal-residual (GMRES) iterate and of the Galerkin
  (FOM) iterate over $x_0 + \mathcal{K}_m$.

## Implementation notes

* The Hessenberg relation needs only module structures, and the operator may map between two
  modules, $A : E \to F$ with $z_j \in E$ and $v_j \in F$. The bidiagonalization
  $A v_j = \alpha_j u_j + \beta_{j+1} u_{j+1}$ behind LSQR ([golub2013matrix], §11.4.2) has this
  form. `Krylov.HessenbergRelation` is the case $z = v$, so the residual formulas apply to IOM, DIOM
  and DQGMRES, and to the bi-Lanczos basis of QMR ([saad2003iterative], Chapter 7). The Arnoldi
  process is the instance `Arnoldi.hessenbergRelation`.
* The rotations are indexed by $\mathbb{N}$ and computed from the infinite coefficient function $h$,
  so no casts between `Fin` types occur, and the rotations for $\bar{H}_m$ are the first $m$
  rotations for $\bar{H}_{m'}$ when $m \le m'$.
* At a degenerate rotation, $\rho_k = 0$, Lean's convention for division by zero gives
  $c_k = s_k = 0$. Results that need a genuine rotation assume $\rho_k \neq 0$.
-/

open Krylov Finset

variable {𝕜 : Type*} [RCLike 𝕜]

namespace Krylov

/-- The $(m + 1) \times m$ **Hessenberg matrix** $\bar{H}_m$ of a coefficient function $h :
\mathbb{N} \times \mathbb{N} \to \mathbb{K}$: its entry $(i, j)$ is $h_{ij}$, for $i \le m$ and
$j < m$. -/
def hessenbergOf (h : ℕ → ℕ → 𝕜) (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) 𝕜 :=
  Matrix.of fun i j => h i j

/-- The $m \times m$ **Hessenberg matrix** $H_m$ of a coefficient function $h : \mathbb{N} \times
\mathbb{N} \to \mathbb{K}$: its entry $(i, j)$ is $h_{ij}$, for $i, j < m$. -/
def hessenbergSqOf (h : ℕ → ℕ → 𝕜) (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜 :=
  Matrix.of fun i j => h i j

/-- The vector $\beta e_1 \in \mathbb{K}^m$: its first entry is $\beta$, and all other entries are
$0$. -/
def firstVec (β : 𝕜) (m : ℕ) : Fin m → 𝕜 := fun i => if (i : ℕ) = 0 then β else 0

section Relation

variable {E F : Type*} [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- A **two-family Hessenberg relation** for a linear map $A : E \to F$, sequences $z_j \in E$ and
$v_j \in F$, and coefficients $h_{ij} \in \mathbb{K}$: for every $j$,
$$A z_j = \sum_{i=0}^{j+1} h_{ij} v_i,$$
and $h_{ij} = 0$ whenever $i > j + 1$. The family $z$ is the basis of the iterates and the
family $v$ is the basis of the residuals ([saad2003iterative], (9.22) for FGMRES and (7.70) for
TFQMR). No orthogonality is assumed.

The spaces $E$ and $F$ are modules over $\mathbb{K}$, and nothing more is used. The
bidiagonalization $A v_j = \alpha_j u_j + \beta_{j+1} u_{j+1}$ of Paige and Saunders behind LSQR
([golub2013matrix], §10.4, §11.4.2) is an instance, with lower bidiagonal coefficients.
`Krylov.HessenbergRelation` is the case $z = v$. -/
structure HessenbergRelation₂ (A : E →ₗ[𝕜] F) (z : ℕ → E) (v : ℕ → F) (h : ℕ → ℕ → 𝕜) :
    Prop where
  /-- The expansion $A z_j = \sum_{i \le j+1} h_{ij} v_i$, for every $j$. -/
  apply_eq : ∀ j, A (z j) = ∑ i ∈ range (j + 2), h i j • v i
  /-- The coefficients are upper Hessenberg: $h_{ij} = 0$ whenever $i > j + 1$. -/
  eq_zero_of_lt : ∀ i j, j + 1 < i → h i j = 0

/-- A **Hessenberg relation** for a linear operator $A$ on $E$, a sequence $v_j \in E$ and
coefficients $h_{ij}$: $A v_j = \sum_{i \le j+1} h_{ij} v_i$ for every $j$, and $h_{ij} = 0$
whenever $i > j + 1$ ([saad2003iterative], (6.6)–(6.9), without orthogonality).

This is the case $z = v$ of `Krylov.HessenbergRelation₂`, so every lemma about the two-family
relation applies to it by dot notation. -/
abbrev HessenbergRelation (A : E →ₗ[𝕜] E) (v : ℕ → E) (h : ℕ → ℕ → 𝕜) : Prop :=
  HessenbergRelation₂ A v v h

namespace HessenbergRelation₂

variable {A : E →ₗ[𝕜] F} {z : ℕ → E} {v : ℕ → F} {h : ℕ → ℕ → 𝕜}
  (hv : HessenbergRelation₂ A z v h)
include hv

/-- The coefficients of a two-family Hessenberg relation form an upper Hessenberg array indexed by
$\mathbb{N}$ (`Matrix.IsUpperHessenberg`). -/
theorem isUpperHessenberg : Matrix.IsUpperHessenberg (n := ℕ) h :=
  Matrix.isUpperHessenberg_iff_nat.2 hv.eq_zero_of_lt

/-- For a two-family Hessenberg relation, the matrix $\bar{H}_m$ is upper Hessenberg for every $m$.
-/
theorem hessenbergOf_isUpperHessenbergRect (m : ℕ) : (hessenbergOf h m).IsUpperHessenbergRect :=
  fun i j hij => hv.eq_zero_of_lt i j hij

/-- The Hessenberg expansion of $A z_j$ can be taken over any range $i < N$ with $N \ge j + 2$. -/
private theorem apply_eq_range (j N : ℕ) (hj : j + 2 ≤ N) :
    A (z j) = ∑ i ∈ range N, h i j • v i := by
  rw [hv.apply_eq j]
  refine Finset.sum_subset (by simpa using hj) fun i hi hi' => ?_
  rw [Finset.mem_range] at hi'
  rw [hv.eq_zero_of_lt i j (by omega), zero_smul]

/-- For a two-family Hessenberg relation and every $y \in \mathbb{K}^m$,
$$A \sum_{j<m} y_j z_j = \sum_{i=0}^{m} (\bar{H}_m y)_i \, v_i.$$
This is the coordinate form of $A Z_m = V_{m+1} \bar{H}_m$ ([saad2003iterative], (6.7) and
(9.22)). -/
theorem apply_sum (m : ℕ) (y : Fin m → 𝕜) :
    A (∑ j, y j • z j) = ∑ i : Fin (m + 1), (hessenbergOf h m).mulVec y i • v i := by
  rw [map_sum]
  have hleft : ∀ j : Fin m, A (y j • z j) = ∑ i : Fin (m + 1), (y j * h i j) • v i := by
    intro j
    rw [map_smul, hv.apply_eq_range (j : ℕ) (m + 1) (by omega), Finset.smul_sum,
      ← Fin.sum_univ_eq_sum_range (fun i => y j • h i (j : ℕ) • v i) (m + 1)]
    exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
  rw [Finset.sum_congr rfl fun j _ => hleft j, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hessenbergOf, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]

/-- For a two-family Hessenberg relation, let $b - A x_0 = \beta v_0$. Then for every
$y \in \mathbb{K}^m$
$$b - A \Big( x_0 + \sum_{j<m} y_j z_j \Big) = \sum_{i=0}^{m} (\beta e_1 - \bar{H}_m y)_i \,
  v_i.$$
In the one-family case this is (6.27) of [saad2003iterative] for FOM and GMRES, and (7.16) for
QMR. In the two-family case it is (7.75) for TFQMR and (9.25) for FGMRES. -/
theorem residual_eq {b : F} {x₀ : E} {β : 𝕜} (hr : b - A x₀ = β • v 0) (m : ℕ) (y : Fin m → 𝕜) :
    b - A (x₀ + ∑ j, y j • z j) =
      ∑ i : Fin (m + 1), (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) i • v i := by
  have hfirst : ∑ i : Fin (m + 1), firstVec β (m + 1) i • v i = β • v 0 := by
    rw [Finset.sum_eq_single (⟨0, Nat.succ_pos m⟩ : Fin (m + 1))]
    · rfl
    · intro i _ hi
      have : (i : ℕ) ≠ 0 := fun hc => hi (Fin.ext hc)
      simp [firstVec, this]
    · intro hc; exact absurd (Finset.mem_univ _) hc
  have hAx : A (x₀ + ∑ j, y j • z j) = A x₀ + ∑ i : Fin (m + 1),
      (hessenbergOf h m).mulVec y i • v i := by
    rw [map_add, hv.apply_sum m y]
  have hsplit : ∑ i : Fin (m + 1), (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) i • v i
      = β • v 0 - ∑ i : Fin (m + 1), (hessenbergOf h m).mulVec y i • v i := by
    rw [← hfirst, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply, sub_smul]
  rw [hsplit, hAx, ← hr]
  abel

/-- For a two-family Hessenberg relation, let $b - A x_0 = \beta v_0$, let $m > 0$, and let
$y \in \mathbb{K}^m$ satisfy $H_m y = \beta e_1$. Then
$$b - A \Big( x_0 + \sum_{j<m} y_j z_j \Big) = -(h_{m,m-1} \, y_{m-1}) \, v_m.$$
This is Proposition 6.7 and (6.18) of [saad2003iterative], and (7.76) and (9.23) there. -/
theorem residual_eq_of_mulVec_eq {b : F} {x₀ : E} {β : 𝕜} (hr : b - A x₀ = β • v 0) {m : ℕ}
    (hm : 0 < m) (y : Fin m → 𝕜) (hy : (hessenbergSqOf h m).mulVec y = firstVec β m) :
    b - A (x₀ + ∑ j, y j • z j) = -(h m (m - 1) * y ⟨m - 1, by omega⟩) • v m := by
  rw [hv.residual_eq hr m y]
  have hzero : ∀ i : Fin (m + 1), (i : ℕ) < m →
      (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) i = 0 := by
    intro i hi
    have h1 : (hessenbergOf h m).mulVec y i = (hessenbergSqOf h m).mulVec y ⟨i, hi⟩ := by
      simp [Matrix.mulVec, dotProduct, hessenbergOf, hessenbergSqOf]
    have h2 : firstVec β (m + 1) i = firstVec β m ⟨i, hi⟩ := by simp [firstVec]
    simp only [Pi.sub_apply, h1, h2, hy, sub_self]
  have hlast : (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) ⟨m, Nat.lt_succ_self m⟩ =
      -(h m (m - 1) * y ⟨m - 1, by omega⟩) := by
    have hfv : firstVec β (m + 1) (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) = 0 := by
      simp [firstVec, hm.ne']
    have hmv : (hessenbergOf h m).mulVec y (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) =
        h m (m - 1) * y ⟨m - 1, by omega⟩ := by
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single (⟨m - 1, by omega⟩ : Fin m)]
      · rfl
      · intro j _ hj
        have : (j : ℕ) + 1 < m := by
          have := j.isLt
          have : (j : ℕ) ≠ m - 1 := fun hc => hj (Fin.ext hc)
          omega
        rw [hessenbergOf, Matrix.of_apply, hv.eq_zero_of_lt m j (by omega), zero_mul]
      · intro hc; exact absurd (Finset.mem_univ _) hc
    simp only [Pi.sub_apply, hfv, hmv, zero_sub]
  rw [Finset.sum_eq_single (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))]
  · rw [hlast]
  · intro i _ hi
    have : (i : ℕ) < m := by
      have := i.isLt
      have : (i : ℕ) ≠ m := fun hc => hi (Fin.ext hc)
      omega
    rw [hzero i this, zero_smul]
  · intro hc; exact absurd (Finset.mem_univ _) hc

end HessenbergRelation₂

end Relation

end Krylov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Arnoldi

variable (A : E →ₗ[𝕜] E) (b : E)

/-- The matrix $\bar{H}_m$ of the Arnoldi process is the rectangular Hessenberg matrix of the
Arnoldi coefficients. -/
theorem hessenberg_eq (m : ℕ) : hessenberg A b m = hessenbergOf (coeff A b) m := rfl

/-- The matrix $H_m$ of the Arnoldi process is the square Hessenberg matrix of the Arnoldi
coefficients. -/
theorem hessenbergSq_eq (m : ℕ) : hessenbergSq A b m = hessenbergSqOf (coeff A b) m := rfl

/-- The Arnoldi vectors $v_j$ and coefficients $h_{ij} = \langle v_i, A v_j \rangle$ of $(A, b)$
satisfy the Hessenberg relation $A v_j = \sum_{i \le j+1} h_{ij} v_i$, for every $j$. After a
breakdown both sides vanish. -/
theorem hessenbergRelation : HessenbergRelation A (vec A b) (coeff A b) :=
  ⟨apply_vec A b, fun _ _ hij => coeff_eq_zero_of_lt A b hij⟩

/-- For every $b$, $\|b\| v_0 = b$, where $v_0$ is the first Arnoldi vector. When $b = 0$ both sides
vanish. -/
theorem smul_vec_zero : (‖b‖ : 𝕜) • vec A b 0 = b := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  · have hne : ((‖b‖ : ℝ) : 𝕜) ≠ 0 := by simpa using norm_ne_zero_iff.mpr hb
    rw [vec_zero A b hb, smul_smul, mul_inv_cancel₀ hne, one_smul]

end Arnoldi

namespace Krylov

section ArnoldiCoords

/-!
### Coordinates in the Arnoldi basis

Lemmas that express membership in $\mathcal{K}_m$, orthogonality to $\mathcal{K}_m$ and the norm of
a combination of Arnoldi vectors in terms of the vector of coefficients.
-/

variable (A : E →ₗ[𝕜] E) (r : E)

/-- For every operator $A$, vector $r$ and $m$, the Arnoldi vectors $v_0, \dots, v_{m-1}$ of
$(A, r)$ span the Krylov space $\mathcal{K}_m(A, r)$. -/
theorem span_range_vec (m : ℕ) :
    Submodule.span 𝕜 (Set.range fun j : Fin m => Arnoldi.vec A r (j : ℕ)) = subspace A r m := by
  rw [← Arnoldi.span_vec A r m]
  congr 1
  ext z
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨(j : ℕ), j.isLt, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, rfl⟩

/-- For every operator $A$, vector $r$ and $m$, a vector $z$ lies in $\mathcal{K}_m(A, r)$ if and
only if $z = \sum_{j<m} y_j v_j$ for some $y \in \mathbb{K}^m$. -/
theorem mem_subspace_iff_exists_coeffs (m : ℕ) (z : E) :
    z ∈ subspace A r m ↔ ∃ y : Fin m → 𝕜, z = ∑ j, y j • Arnoldi.vec A r (j : ℕ) := by
  rw [← span_range_vec A r m, Submodule.mem_span_range_iff_exists_fun]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

private theorem sum_smul_vec_mem (m : ℕ) (y : Fin m → 𝕜) :
    ∑ j, y j • Arnoldi.vec A r (j : ℕ) ∈ subspace A r m :=
  (mem_subspace_iff_exists_coeffs A r m _).mpr ⟨y, rfl⟩

variable [FiniteDimensional 𝕜 (fullSubspace A r)]

/-- Below the grade the Arnoldi vectors are orthonormal, so
$\langle v_j, \sum_i c_i v_i \rangle = c_j$ for $j$ less than the grade. -/
private theorem inner_vec_sum_eq {N : ℕ} (c : Fin N → 𝕜) (j : Fin N)
    (hj : (j : ℕ) < grade A r) :
    inner 𝕜 (Arnoldi.vec A r (j : ℕ)) (∑ i, c i • Arnoldi.vec A r (i : ℕ)) = c j := by
  rw [inner_sum, Finset.sum_eq_single j]
  · rw [inner_smul_right, inner_self_eq_norm_sq_to_K,
      Arnoldi.norm_vec_eq_one_of_lt_grade A r hj]
    norm_num
  · intro i _ hij
    rw [inner_smul_right, Arnoldi.inner_vec_eq_zero A r (fun hc => hij (Fin.ext hc.symm)),
      mul_zero]
  · intro hc
    exact absurd (Finset.mem_univ _) hc

/-- Let $r$ have a finite-dimensional Krylov space. If $c \in \mathbb{K}^N$ has $c_i = 0$ for every
$i$ at least the grade of $r$, then
$$\Big\| \sum_{i<N} c_i v_i \Big\| = \|c\|_2,$$
the Euclidean norm of $c$. -/
theorem norm_sum_smul_vec_eq {N : ℕ} (c : Fin N → 𝕜)
    (hc : ∀ i : Fin N, grade A r ≤ (i : ℕ) → c i = 0) :
    ‖∑ i, c i • Arnoldi.vec A r (i : ℕ)‖ =
      ‖(WithLp.toLp 2 c : EuclideanSpace 𝕜 (Fin N))‖ := by
  have hK : ((‖∑ i, c i • Arnoldi.vec A r (i : ℕ)‖ : ℝ) : 𝕜) ^ 2
      = ((∑ i, ‖c i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← inner_self_eq_norm_sq_to_K, sum_inner]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left]
    rcases Nat.lt_or_ge (i : ℕ) (grade A r) with hi | hi
    · rw [inner_vec_sum_eq A r c i hi, RCLike.conj_mul]
    · rw [hc i hi]
      simp
  have hsq : ‖∑ i, c i • Arnoldi.vec A r (i : ℕ)‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
    exact_mod_cast hK
  have hrhs : ‖(WithLp.toLp 2 c : EuclideanSpace 𝕜 (Fin N))‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 :=
    EuclideanSpace.norm_sq_eq _
  rw [← Real.sqrt_sq (norm_nonneg (∑ i, c i • Arnoldi.vec A r (i : ℕ))),
    ← Real.sqrt_sq (norm_nonneg (WithLp.toLp 2 c : EuclideanSpace 𝕜 (Fin N))), hsq, hrhs]

/-- Below the grade the Arnoldi vectors are linearly independent: for $m$ at most the grade,
$\sum_j y_j v_j = \sum_j y'_j v_j$ implies $y = y'$. -/
private theorem sum_smul_vec_inj {m : ℕ} (hm : m ≤ grade A r) {y y' : Fin m → 𝕜}
    (hyy' : ∑ j, y j • Arnoldi.vec A r (j : ℕ) = ∑ j, y' j • Arnoldi.vec A r (j : ℕ)) :
    y = y' := by
  have h0 : ∑ j, (y - y') j • Arnoldi.vec A r (j : ℕ) = 0 := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hyy', sub_self]
  have hn := norm_sum_smul_vec_eq A r (y - y')
    (fun j hj => absurd (lt_of_lt_of_le j.isLt hm) (not_lt.mpr hj))
  rw [h0, norm_zero] at hn
  have hz : (WithLp.toLp 2 (y - y') : EuclideanSpace 𝕜 (Fin m)) = 0 := by
    rw [← norm_eq_zero]
    exact hn.symm
  have hsub : y - y' = 0 := by
    have hof := congrArg WithLp.ofLp hz
    simpa using hof
  exact sub_eq_zero.mp hsub

private theorem sum_smul_vec_mem_orthogonal {m : ℕ} (hm : m ≤ grade A r) (c : Fin (m + 1) → 𝕜)
    (hc : ∀ j : Fin (m + 1), (j : ℕ) < m → c j = 0) :
    (∑ i, c i • Arnoldi.vec A r (i : ℕ)) ∈ (subspace A r m)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  obtain ⟨w, rfl⟩ := (mem_subspace_iff_exists_coeffs A r m u).mp hu
  rw [sum_inner]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hjm : (j : ℕ) < m := j.isLt
  rw [inner_smul_left, inner_vec_sum_eq A r c ⟨(j : ℕ), by omega⟩ (lt_of_lt_of_le hjm hm),
    hc ⟨(j : ℕ), by omega⟩ hjm, mul_zero]

private theorem coeff_eq_zero_of_mem_orthogonal {m : ℕ} (hm : m ≤ grade A r)
    (c : Fin (m + 1) → 𝕜) (h : (∑ i, c i • Arnoldi.vec A r (i : ℕ)) ∈ (subspace A r m)ᗮ)
    (j : Fin (m + 1)) (hj : (j : ℕ) < m) : c j = 0 := by
  have hin := Submodule.inner_right_of_mem_orthogonal (Arnoldi.vec_mem_subspace_of_lt A r hj) h
  rwa [inner_vec_sum_eq A r c j (lt_of_lt_of_le hj hm)] at hin

/-- Let $r$ have a finite-dimensional Krylov space, let $m$ be at most the grade of $r$, and let
$y \in \mathbb{K}^m$. Then every entry $i \le m$ of $\|r\| e_1 - \bar{H}_m y$ with $i$ at least
the grade vanishes. Since $m$ is at most the grade, the only such entry is the last one, at $m$
equal to the grade. -/
theorem residual_coeff_eq_zero {m : ℕ} (hm : m ≤ grade A r) (y : Fin m → 𝕜)
    (i : Fin (m + 1)) (hi : grade A r ≤ (i : ℕ)) :
    (firstVec (‖r‖ : 𝕜) (m + 1) - (Arnoldi.hessenberg A r m).mulVec y) i = 0 := by
  have him : (i : ℕ) = m := by omega
  have hmv : ∀ j : Fin m, Arnoldi.coeff A r (i : ℕ) (j : ℕ) = 0 := by
    intro j
    rw [him]
    rcases Nat.lt_or_ge ((j : ℕ) + 1) m with hj | hj
    · exact Arnoldi.coeff_eq_zero_of_lt A r hj
    · have hjm : (j : ℕ) + 1 = m := by omega
      have h0 := (Arnoldi.coeff_succ_self_eq_zero_iff A r (j : ℕ)).mpr
        (show grade A r ≤ (j : ℕ) + 1 by omega)
      rwa [hjm] at h0
  have hzero : (Arnoldi.hessenberg A r m).mulVec y i = 0 := by
    simp only [Matrix.mulVec, dotProduct, Arnoldi.hessenberg, Matrix.of_apply]
    exact Finset.sum_eq_zero fun j _ => by rw [hmv j, zero_mul]
  have hfv : firstVec (‖r‖ : 𝕜) (m + 1) i = 0 := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · have hv0 : Arnoldi.vec A r 0 = 0 := (Arnoldi.vec_eq_zero_iff A r 0).mpr (by omega)
      have hr0 : r = 0 := by
        have hsv := Arnoldi.smul_vec_zero A r
        rw [hv0, smul_zero] at hsv
        exact hsv.symm
      simp [firstVec, hr0]
    · have hne : (i : ℕ) ≠ 0 := by omega
      simp [firstVec, hne]
  rw [Pi.sub_apply, hfv, hzero, sub_zero]

/-- For $m$ at most the grade, the residual $\sum_i (\|r\| e_1 - \bar{H}_m y)_i v_i$ is orthogonal
to $\mathcal{K}_m$ if and only if $H_m y = \|r\| e_1$. -/
private theorem mem_orthogonal_iff_mulVec_eq {m : ℕ} (hm : m ≤ grade A r) (y : Fin m → 𝕜) :
    (∑ i : Fin (m + 1), (firstVec (‖r‖ : 𝕜) (m + 1) -
        (Arnoldi.hessenberg A r m).mulVec y) i • Arnoldi.vec A r (i : ℕ)) ∈
        (subspace A r m)ᗮ ↔
      (Arnoldi.hessenbergSq A r m).mulVec y = firstVec (‖r‖ : 𝕜) m := by
  have e1 : ∀ (j : Fin m) (hj : (j : ℕ) < m + 1),
      firstVec (‖r‖ : 𝕜) (m + 1) ⟨(j : ℕ), hj⟩ = firstVec (‖r‖ : 𝕜) m j := fun _ _ => rfl
  have e2 : ∀ (j : Fin m) (hj : (j : ℕ) < m + 1),
      (Arnoldi.hessenberg A r m).mulVec y ⟨(j : ℕ), hj⟩ =
        (Arnoldi.hessenbergSq A r m).mulVec y j := fun _ _ => rfl
  constructor
  · intro h
    funext j
    have hz := coeff_eq_zero_of_mem_orthogonal A r hm _ h ⟨(j : ℕ), by omega⟩ j.isLt
    rw [Pi.sub_apply, e1 j, e2 j, sub_eq_zero] at hz
    exact hz.symm
  · intro h
    refine sum_smul_vec_mem_orthogonal A r hm _ fun j hj => ?_
    have hjj : j = (⟨(j : ℕ), by omega⟩ : Fin (m + 1)) := rfl
    rw [hjj, Pi.sub_apply, e1 ⟨(j : ℕ), hj⟩, e2 ⟨(j : ℕ), hj⟩, h, sub_self]

end ArnoldiCoords

section Coordinates

variable {A : E →ₗ[𝕜] E} {b x₀ : E} [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]

/-- Let $r_0 = b - A x_0$ have a finite-dimensional Krylov space, let $m$ be at most the grade of
$r_0$, and let $\beta = \|r_0\|$. For every $y \in \mathbb{K}^m$,
$$\Big\| b - A \Big( x_0 + \sum_{j<m} y_j v_j \Big) \Big\| = \|\beta e_1 - \bar{H}_m y\|_2.$$
This is (6.28) of [saad2003iterative]. -/
theorem norm_residual_eq_norm_firstVec_sub_mulVec {m : ℕ} (hm : m ≤ grade A (b - A x₀))
    (y : Fin m → 𝕜) :
    ‖b - A (x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j)‖ =
      ‖(WithLp.toLp 2 (firstVec (‖b - A x₀‖ : 𝕜) (m + 1) -
        (Arnoldi.hessenberg A (b - A x₀) m).mulVec y) : EuclideanSpace 𝕜 (Fin (m + 1)))‖ := by
  rw [(Arnoldi.hessenbergRelation A (b - A x₀)).residual_eq
    (Arnoldi.smul_vec_zero A (b - A x₀)).symm m y]
  exact norm_sum_smul_vec_eq A (b - A x₀) _ (residual_coeff_eq_zero A (b - A x₀) hm y)

/-- Let $r_0 = b - A x_0$ have a finite-dimensional Krylov space, let $m$ be at most the grade of
$r_0$, and let $\beta = \|r_0\|$. For every $y \in \mathbb{K}^m$, the point
$x_0 + \sum_{j<m} y_j v_j$ is the Galerkin iterate at step $m$ if and only if
$H_m y = \beta e_1$. This is FOM in coordinates, (6.16)–(6.17) of [saad2003iterative]. -/
theorem isGalerkinIterate_iff_mulVec_eq {m : ℕ} (hm : m ≤ grade A (b - A x₀)) (y : Fin m → 𝕜) :
    IsGalerkinIterate A b x₀ m (x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j) ↔
      (Arnoldi.hessenbergSq A (b - A x₀) m).mulVec y = firstVec (‖b - A x₀‖ : 𝕜) m := by
  have hres : b - A (x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j) =
      ∑ i : Fin (m + 1), (firstVec (‖b - A x₀‖ : 𝕜) (m + 1) -
        (Arnoldi.hessenberg A (b - A x₀) m).mulVec y) i • Arnoldi.vec A (b - A x₀) i :=
    (Arnoldi.hessenbergRelation A (b - A x₀)).residual_eq
      (Arnoldi.smul_vec_zero A (b - A x₀)).symm m y
  constructor
  · intro hx
    have horth := hx.orth
    rw [hres] at horth
    exact (mem_orthogonal_iff_mulVec_eq A (b - A x₀) hm y).mp horth
  · intro hy
    refine ⟨by simpa using sum_smul_vec_mem A (b - A x₀) m y, ?_⟩
    rw [hres]
    exact (mem_orthogonal_iff_mulVec_eq A (b - A x₀) hm y).mpr hy

/-- Let $r_0 = b - A x_0$ have a finite-dimensional Krylov space, let $m$ be at most the grade of
$r_0$, and let $\beta = \|r_0\|$. A point $x$ is a Galerkin iterate at step $m$ if and only if
$x = x_0 + \sum_{j<m} y_j v_j$ for some $y \in \mathbb{K}^m$ with $H_m y = \beta e_1$.

The companion `Krylov.isGalerkinIterate_iff_mulVec_eq` starts from a given coordinate vector.
The quantifier over $y$ here lets the solvability of the Hessenberg system be exchanged for the
existence and uniqueness of the iterate (`Krylov.existsUnique_isGalerkinIterate_iff_isUnit`). -/
theorem isGalerkinIterate_iff_exists_mulVec_eq {m : ℕ} (hm : m ≤ grade A (b - A x₀)) (x : E) :
    IsGalerkinIterate A b x₀ m x ↔
      ∃ y : Fin m → 𝕜, (Arnoldi.hessenbergSq A (b - A x₀) m).mulVec y =
        firstVec (‖b - A x₀‖ : 𝕜) m ∧ x = x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (mem_subspace_iff_exists_coeffs A (b - A x₀) m _).mp hx.mem
    have hxe : x = x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j := by
      rw [← hy]
      abel
    rw [hxe] at hx
    exact ⟨y, (isGalerkinIterate_iff_mulVec_eq hm y).mp hx, hxe⟩
  · rintro ⟨y, hy, rfl⟩
    exact (isGalerkinIterate_iff_mulVec_eq hm y).mpr hy

/-- Let $r_0 = b - A x_0$ have a finite-dimensional Krylov space, and let $m$ be at most the grade
of $r_0$. There is exactly one Galerkin iterate at step $m$ if and only if $H_m$ is nonsingular.
Thus FOM is well defined exactly when $H_m$ is nonsingular, which is the hypothesis of
Propositions 6.12–6.17 of [saad2003iterative], §6.4. -/
theorem existsUnique_isGalerkinIterate_iff_isUnit {m : ℕ} (hm : m ≤ grade A (b - A x₀)) :
    (∃! x, IsGalerkinIterate A b x₀ m x) ↔ IsUnit (Arnoldi.hessenbergSq A (b - A x₀) m) := by
  constructor
  · rintro ⟨x, hx, huniq⟩
    obtain ⟨y, hy, hxe⟩ := (isGalerkinIterate_iff_exists_mulVec_eq hm x).mp hx
    have key : ∀ w : Fin m → 𝕜, (Arnoldi.hessenbergSq A (b - A x₀) m).mulVec w =
        firstVec (‖b - A x₀‖ : 𝕜) m → w = y := by
      intro w hw
      have h1 := huniq _ ((isGalerkinIterate_iff_mulVec_eq hm w).mpr hw)
      rw [hxe] at h1
      exact sum_smul_vec_inj A (b - A x₀) hm (add_left_cancel h1)
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro z z' hzz'
    have hd : (Arnoldi.hessenbergSq A (b - A x₀) m).mulVec (y + (z - z')) =
        firstVec (‖b - A x₀‖ : 𝕜) m := by
      rw [Matrix.mulVec_add, Matrix.mulVec_sub, hzz', sub_self, add_zero, hy]
    have h2 : y + (z - z') = y + 0 := by
      rw [add_zero]
      exact key _ hd
    exact sub_eq_zero.mp (add_left_cancel h2)
  · intro hu
    obtain ⟨y, hy⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hu (firstVec (‖b - A x₀‖ : 𝕜) m)
    refine ⟨x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j,
      (isGalerkinIterate_iff_mulVec_eq hm y).mpr hy, ?_⟩
    intro x' hx'
    obtain ⟨y', hy', hx'e⟩ := (isGalerkinIterate_iff_exists_mulVec_eq hm x').mp hx'
    have hyy : y' = y := Matrix.mulVec_injective_iff_isUnit.mpr hu (by rw [hy, hy'])
    rw [hx'e, hyy]

omit [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] in
/-- Let $r_0 = b - A x_0$, $\beta = \|r_0\|$ and $m > 0$. If $y \in \mathbb{K}^m$ satisfies
$H_m y = \beta e_1$, then the residual of $x_0 + \sum_{j<m} y_j v_j$ is
$$-(h_{m,m-1} \, y_{m-1}) \, v_m.$$
This is Proposition 6.7 of [saad2003iterative] for the Arnoldi basis. No finite dimension is
needed. -/
theorem residual_galerkin_eq {m : ℕ} (hm : 0 < m) (y : Fin m → 𝕜)
    (hy : (Arnoldi.hessenbergSq A (b - A x₀) m).mulVec y = firstVec (‖b - A x₀‖ : 𝕜) m) :
    b - A (x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j) =
      -(Arnoldi.coeff A (b - A x₀) m (m - 1) * y ⟨m - 1, by omega⟩) •
        Arnoldi.vec A (b - A x₀) m :=
  (Arnoldi.hessenbergRelation A (b - A x₀)).residual_eq_of_mulVec_eq
    (Arnoldi.smul_vec_zero A (b - A x₀)).symm hm y hy

/-- Let $r_0 = b - A x_0$ have a finite-dimensional Krylov space, let $m$ be at most the grade of
$r_0$, and let $\beta = \|r_0\|$. For every $y \in \mathbb{K}^m$, the point
$x_0 + \sum_{j<m} y_j v_j$ is a minimal-residual iterate at step $m$ if and only if $y$
minimizes $\|\beta e_1 - \bar{H}_m z\|_2$ over $z \in \mathbb{K}^m$. This is GMRES in
coordinates, (6.29)–(6.30) of [saad2003iterative]. -/
theorem isMinResidualIterate_iff_isMinOn {m : ℕ} (hm : m ≤ grade A (b - A x₀)) (y : Fin m → 𝕜) :
    IsMinResidualIterate A b x₀ m (x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j) ↔
      IsMinOn (fun z : Fin m → 𝕜 => ‖(WithLp.toLp 2 (firstVec (‖b - A x₀‖ : 𝕜) (m + 1) -
        (Arnoldi.hessenberg A (b - A x₀) m).mulVec z) : EuclideanSpace 𝕜 (Fin (m + 1)))‖)
        Set.univ y := by
  rw [isMinOn_iff]
  constructor
  · intro hx z _
    change ‖(WithLp.toLp 2 (firstVec (‖b - A x₀‖ : 𝕜) (m + 1) -
        (Arnoldi.hessenberg A (b - A x₀) m).mulVec y) : EuclideanSpace 𝕜 (Fin (m + 1)))‖ ≤
      ‖(WithLp.toLp 2 (firstVec (‖b - A x₀‖ : 𝕜) (m + 1) -
        (Arnoldi.hessenberg A (b - A x₀) m).mulVec z) : EuclideanSpace 𝕜 (Fin (m + 1)))‖
    rw [← norm_residual_eq_norm_firstVec_sub_mulVec hm y,
      ← norm_residual_eq_norm_firstVec_sub_mulVec hm z]
    exact hx.min _ (by simpa using sum_smul_vec_mem A (b - A x₀) m z)
  · intro hz
    refine ⟨by simpa using sum_smul_vec_mem A (b - A x₀) m y, ?_⟩
    intro w hw
    obtain ⟨c, hc⟩ := (mem_subspace_iff_exists_coeffs A (b - A x₀) m _).mp hw
    have hwe : w = x₀ + ∑ j, c j • Arnoldi.vec A (b - A x₀) j := by
      rw [← hc]
      abel
    have h3 : ‖(WithLp.toLp 2 (firstVec (‖b - A x₀‖ : 𝕜) (m + 1) -
        (Arnoldi.hessenberg A (b - A x₀) m).mulVec y) : EuclideanSpace 𝕜 (Fin (m + 1)))‖ ≤
      ‖(WithLp.toLp 2 (firstVec (‖b - A x₀‖ : 𝕜) (m + 1) -
        (Arnoldi.hessenberg A (b - A x₀) m).mulVec c) : EuclideanSpace 𝕜 (Fin (m + 1)))‖ :=
      hz c (Set.mem_univ c)
    rw [hwe, norm_residual_eq_norm_firstVec_sub_mulVec hm y,
      norm_residual_eq_norm_firstVec_sub_mulVec hm c]
    exact h3


/-- **GMRES through any unitary triangularization of $\bar{H}_m$.** Let $r_0 = b - A x_0$ have a
finite-dimensional Krylov space, let $m$ be at most the grade of $r_0$, and let
$\beta = \|r_0\|$. Let $W$ be a unitary $(m + 1) \times (m + 1)$ matrix such that the last row
of $W \bar{H}_m$ is zero, and let $y \in \mathbb{K}^m$ satisfy the first $m$ rows of
$(W \bar{H}_m) y = W (\beta e_1)$. Then $x_0 + \sum_{j<m} y_j v_j$ is a minimal-residual iterate
at step $m$, and its residual norm is $|(W \beta e_1)_m|$. See [saad2003iterative], Proposition
6.5, and [golub2013matrix], §11.4.3.

The rotations need not be those of `Krylov.givensQ`: any sign convention, or a Householder
factorization, works. Since $W$ is an isometry, $\|\beta e_1 - \bar{H}_m z\|^2 = \sum_{i<m} |(W
\beta e_1 - W \bar{H}_m z)_i|^2 + |(W \beta e_1)_m|^2$, and the first part vanishes at $z = y$. -/
theorem isMinResidualIterate_of_unitary_mul_hessenberg {m : ℕ} (hm : m ≤ grade A (b - A x₀))
    {W : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜} (hW : W ∈ Matrix.unitaryGroup (Fin (m + 1)) 𝕜)
    (hlast : ∀ j, (W * Arnoldi.hessenberg A (b - A x₀) m) (Fin.last m) j = 0) {y : Fin m → 𝕜}
    (hy : ∀ i : Fin m, ((W * Arnoldi.hessenberg A (b - A x₀) m).mulVec y) i.castSucc =
      (W.mulVec (firstVec (‖b - A x₀‖ : 𝕜) (m + 1))) i.castSucc) :
    IsMinResidualIterate A b x₀ m (x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j) ∧
      ‖b - A (x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j)‖ =
        ‖(W.mulVec (firstVec (‖b - A x₀‖ : 𝕜) (m + 1))) (Fin.last m)‖ := by
  set g := W.mulVec (firstVec (‖b - A x₀‖ : 𝕜) (m + 1)) with hg
  set R := W * Arnoldi.hessenberg A (b - A x₀) m with hR
  have hRz : ∀ z : Fin m → 𝕜, (R.mulVec z) (Fin.last m) = 0 := fun z => by
    simp only [Matrix.mulVec, dotProduct, hlast, zero_mul, Finset.sum_const_zero]
  have key : ∀ z : Fin m → 𝕜, ‖(WithLp.toLp 2 (firstVec (‖b - A x₀‖ : 𝕜) (m + 1) -
      (Arnoldi.hessenberg A (b - A x₀) m).mulVec z) : EuclideanSpace 𝕜 (Fin (m + 1)))‖ ^ 2 =
      (∑ i : Fin m, ‖g i.castSucc - (R.mulVec z) i.castSucc‖ ^ 2) + ‖g (Fin.last m)‖ ^ 2 := by
    intro z
    rw [← Matrix.norm_toLp_mulVec_of_mem_unitaryGroup hW, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      ← hg, ← hR, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
    simp only [Pi.sub_apply, hRz, sub_zero]
  have hy0 : ∀ i : Fin m, g i.castSucc - (R.mulVec y) i.castSucc = 0 := fun i => by
    rw [hy i, sub_self]
  have hkey : ‖(WithLp.toLp 2 (firstVec (‖b - A x₀‖ : 𝕜) (m + 1) -
      (Arnoldi.hessenberg A (b - A x₀) m).mulVec y) : EuclideanSpace 𝕜 (Fin (m + 1)))‖ ^ 2 =
      ‖g (Fin.last m)‖ ^ 2 := by
    rw [key]
    simp only [hy0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, zero_add]
  refine ⟨(isMinResidualIterate_iff_isMinOn hm y).2 (isMinOn_iff.2 fun z _ => ?_), ?_⟩
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [hkey, key]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => sq_nonneg _)
  · rw [norm_residual_eq_norm_firstVec_sub_mulVec hm y]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hkey

end Coordinates

section Givens

/-!
### Givens rotations, indexed by $\mathbb{N}$

The array $R^{(k)}$ (`Krylov.rotated h k`) is the coefficient array after the first $k$ rotations.
Rotation $k$ acts on rows $k$ and $k + 1$ and annihilates the entry $(k + 1, k)$. With
$a = R^{(k)}_{kk}$, $d = R^{(k)}_{k+1,k}$, $\rho_k = \sqrt{|a|^2 + |d|^2}$, $c_k = a / \rho_k$ and
$s_k = d / \rho_k$, the rotation acts on the two rows by the matrix
$$\begin{bmatrix} \bar{c}_k & \bar{s}_k \\ -s_k & c_k \end{bmatrix}$$
([saad2003iterative], (6.80), for complex $\mathbb{K}$). For the Arnoldi coefficients $s_k$ is real.
-/

/-- The coefficient array $R^{(k)}$ after the first $k$ Givens rotations. $R^{(0)} = h$. With
$a = R^{(k)}_{kk}$, $d = R^{(k)}_{k+1,k}$ and $\rho = \sqrt{|a|^2 + |d|^2}$, the array
$R^{(k+1)}$ has row $k$ equal to $\overline{(a/\rho)} R^{(k)}_{k,\cdot} + \overline{(d/\rho)}
R^{(k)}_{k+1,\cdot}$, row $k + 1$ equal to $-(d/\rho) R^{(k)}_{k,\cdot} + (a/\rho)
R^{(k)}_{k+1,\cdot}$, and all other rows equal to those of $R^{(k)}$.

When $\rho = 0$, Lean's convention for division by zero makes rows $k$ and $k + 1$ of
$R^{(k+1)}$ zero. -/
noncomputable def rotated (h : ℕ → ℕ → 𝕜) : ℕ → ℕ → ℕ → 𝕜
  | 0 => h
  | k + 1 => fun i j =>
      let a := rotated h k k k
      let d := rotated h k (k + 1) k
      let ρ : 𝕜 := (Real.sqrt (‖a‖ ^ 2 + ‖d‖ ^ 2) : 𝕜)
      if i = k then
        starRingEnd 𝕜 (a / ρ) * rotated h k k j + starRingEnd 𝕜 (d / ρ) * rotated h k (k + 1) j
      else if i = k + 1 then -(d / ρ) * rotated h k k j + (a / ρ) * rotated h k (k + 1) j
      else rotated h k i j

variable (h : ℕ → ℕ → 𝕜)

/-- The rotation parameter $\rho_k = \sqrt{|R^{(k)}_{kk}|^2 + |R^{(k)}_{k+1,k}|^2}$. -/
noncomputable def givensRho (k : ℕ) : ℝ :=
  Real.sqrt (‖rotated h k k k‖ ^ 2 + ‖rotated h k (k + 1) k‖ ^ 2)

/-- The rotation parameter $c_k = R^{(k)}_{kk} / \rho_k$, which is $0$ when $\rho_k = 0$. -/
noncomputable def givensC (k : ℕ) : 𝕜 := rotated h k k k / (givensRho h k : 𝕜)

/-- The rotation parameter $s_k = R^{(k)}_{k+1,k} / \rho_k$, which is $0$ when $\rho_k = 0$. -/
noncomputable def givensS (k : ℕ) : 𝕜 := rotated h k (k + 1) k / (givensRho h k : 𝕜)

/-- The last entry of the rotated right-hand side: $\gamma_0 = \beta$ and
$\gamma_{k+1} = -s_k \gamma_k$ ([saad2003iterative], (6.47)). -/
noncomputable def gamma (β : 𝕜) : ℕ → 𝕜
  | 0 => β
  | k + 1 => -givensS h k * gamma β k

/-- The entry $g_k = \bar{c}_k \gamma_k$. For $k < m$ it is the entry $k$ of $Q_m (\beta e_1)$. -/
noncomputable def gvec (β : 𝕜) (k : ℕ) : 𝕜 := starRingEnd 𝕜 (givensC h k) * gamma h β k

/-- The last entry of the rotated right-hand side satisfies $\gamma_{k+1} = -s_k \gamma_k$
([saad2003iterative], (6.47)). This is the second clause of the definition of `Krylov.gamma`, as
an equation for rewriting.

Since $\|r_m\| = |\gamma_m|$ (`Krylov.IsMinResidualIterate.norm_residual_eq_norm_gamma`), this
is the residual recurrence of the minimal-residual method, and the induction step of
$|\gamma_m| = \prod_{k<m} |s_k| \, |\beta|$. -/
theorem gamma_succ (β : 𝕜) (k : ℕ) : gamma h β (k + 1) = -givensS h k * gamma h β k := rfl

/-- The array $R^{(k+1)}$ in terms of $c_k$ and $s_k$: row $k$ is $\bar{c}_k R^{(k)}_{k,\cdot} +
\bar{s}_k R^{(k)}_{k+1,\cdot}$, row $k + 1$ is $-s_k R^{(k)}_{k,\cdot} + c_k
R^{(k)}_{k+1,\cdot}$, and all other rows are those of $R^{(k)}$. -/
theorem rotated_succ_apply (k i j : ℕ) :
    rotated h (k + 1) i j =
      if i = k then
        starRingEnd 𝕜 (givensC h k) * rotated h k k j +
          starRingEnd 𝕜 (givensS h k) * rotated h k (k + 1) j
      else if i = k + 1 then
        -givensS h k * rotated h k k j + givensC h k * rotated h k (k + 1) j
      else rotated h k i j := rfl

/-- The rotation parameter $\rho_k$ is nonnegative. -/
theorem givensRho_nonneg (k : ℕ) : 0 ≤ givensRho h k := Real.sqrt_nonneg _

/-- The rotation parameter satisfies $\rho_k^2 = |R^{(k)}_{kk}|^2 + |R^{(k)}_{k+1,k}|^2$. -/
theorem givensRho_sq (k : ℕ) :
    givensRho h k ^ 2 = ‖rotated h k k k‖ ^ 2 + ‖rotated h k (k + 1) k‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- If $\rho_k = 0$, then both entries that rotation $k$ acts on vanish: $R^{(k)}_{kk} = 0$ and
$R^{(k)}_{k+1,k} = 0$. -/
theorem rotated_eq_zero_of_givensRho_eq_zero {k : ℕ} (hρ : givensRho h k = 0) :
    rotated h k k k = 0 ∧ rotated h k (k + 1) k = 0 := by
  have hsum : ‖rotated h k k k‖ ^ 2 + ‖rotated h k (k + 1) k‖ ^ 2 = 0 := by
    rw [← givensRho_sq, hρ]
    ring
  obtain ⟨h1, h2⟩ := (add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).mp hsum
  exact ⟨norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h1),
    norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h2)⟩

/-- For every $\beta$ and $m$,
$$|\gamma_m| = \Big( \prod_{k<m} |s_k| \Big) |\beta|$$
([saad2003iterative], (6.47)). -/
theorem norm_gamma_eq_prod (β : 𝕜) (m : ℕ) :
    ‖gamma h β m‖ = (∏ k ∈ range m, ‖givensS h k‖) * ‖β‖ := by
  induction m with
  | zero => simp [gamma]
  | succ m ih =>
      rw [gamma_succ, norm_mul, norm_neg, ih, Finset.prod_range_succ]
      ring

/-- If $\rho_k \neq 0$, then $|c_k|^2 + |s_k|^2 = 1$: the parameters of rotation $k$ are those of a
genuine rotation.

The hypothesis $\rho_k \neq 0$ says that the two entries that the rotation mixes are not both
zero. At a breakdown $c_k = s_k = 0 / 0 = 0$, and the identity fails. -/
theorem norm_givensC_sq_add_norm_givensS_sq (k : ℕ) (hρ : givensRho h k ≠ 0) :
    ‖givensC h k‖ ^ 2 + ‖givensS h k‖ ^ 2 = 1 := by
  have habs : ‖((givensRho h k : ℝ) : 𝕜)‖ = givensRho h k := by
    rw [RCLike.norm_ofReal, abs_of_nonneg (givensRho_nonneg h k)]
  rw [givensC, givensS, norm_div, norm_div, habs, div_pow, div_pow, ← add_div,
    ← givensRho_sq h k]
  exact div_self (pow_ne_zero 2 hρ)

/-- Rotation $k$ produces the real diagonal entry $R^{(k+1)}_{kk} = \rho_k$. -/
theorem rotated_succ_self (k : ℕ) : rotated h (k + 1) k k = (givensRho h k : 𝕜) := by
  rw [rotated_succ_apply, ite_eq_left rfl]
  rcases eq_or_ne (givensRho h k) 0 with hρ | hρ
  · obtain ⟨ha, hd⟩ := rotated_eq_zero_of_givensRho_eq_zero h hρ
    simp [ha, hd, hρ]
  · have hρ' : ((givensRho h k : ℝ) : 𝕜) ≠ 0 := by simpa using hρ
    rw [givensC, givensS, map_div₀, map_div₀, RCLike.conj_ofReal,
      div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, RCLike.conj_mul, RCLike.conj_mul,
      div_eq_iff hρ']
    have hcast : ((‖rotated h k k k‖ ^ 2 + ‖rotated h k (k + 1) k‖ ^ 2 : ℝ) : 𝕜)
        = (‖rotated h k k k‖ : 𝕜) ^ 2 + (‖rotated h k (k + 1) k‖ : 𝕜) ^ 2 := by
      push_cast
      ring
    rw [← hcast, ← givensRho_sq h k]
    push_cast
    ring

/-- Rotation $k$ annihilates the subdiagonal entry that it was built for: $R^{(k+1)}_{k+1,k} = 0$.
-/
theorem rotated_succ_succ_self (k : ℕ) : rotated h (k + 1) (k + 1) k = 0 := by
  rw [rotated_succ_apply, ite_eq_right (by omega), ite_eq_left rfl, givensC, givensS]
  ring

/-- The first $k$ rotations do not change the rows $i \ge k + 1$: $R^{(k)}_{ij} = h_{ij}$ for
$i \ge k + 1$. -/
theorem rotated_eq_of_le (k i j : ℕ) (hi : k + 1 ≤ i) : rotated h k i j = h i j := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
      rw [rotated_succ_apply, ite_eq_right (by omega), ite_eq_right (by omega)]
      exact ih i (by omega)

/-- Let $h$ be upper Hessenberg. After $k$ rotations the first $k$ columns are upper triangular:
$R^{(k)}_{ij} = 0$ for $j < k$ and $j < i$. -/
theorem rotated_eq_zero_of_lt (hh : Matrix.IsUpperHessenberg (n := ℕ) h) (k i j : ℕ) (hj : j < k)
    (hij : j < i) : rotated h k i j = 0 := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
      rw [rotated_succ_apply]
      rcases Nat.lt_or_ge j k with hjk | hjk
      · split_ifs
        · rw [ih k hjk (by omega), ih (k + 1) hjk (by omega), mul_zero, mul_zero, add_zero]
        · rw [ih k hjk (by omega), ih (k + 1) hjk (by omega), mul_zero, mul_zero, add_zero]
        · exact ih i hjk hij
      · have hjk' : j = k := by omega
        subst hjk'
        rcases Nat.lt_or_ge i (j + 1) with hi | hi
        · omega
        · rcases eq_or_lt_of_le hi with hi' | hi'
          · rw [ite_eq_right (by omega), ite_eq_left hi'.symm]
            have := rotated_succ_succ_self h j
            rw [rotated_succ_apply, ite_eq_right (by omega), ite_eq_left rfl] at this
            exact this
          · rw [ite_eq_right (by omega), ite_eq_right (by omega),
              rotated_eq_of_le h j i j (by omega)]
            exact hh.eq_zero_of_add_one_lt i j (by omega)

/-- Let $h_{ij} = 0$ for $i < j$, as for a lower bidiagonal array. Then $R^{(k)}_{ij} = 0$ for
$i < j$ and $k < j$: column $j$ stays zero above the diagonal until rotation $j$ reaches it.

Rotation $k$ combines rows $k$ and $k + 1$, and for $k + 1 \le j$ both of these rows are still
zero in column $j$. -/
theorem rotated_eq_zero_of_lt_of_lt_col (hh : ∀ i j, i < j → h i j = 0) (k i j : ℕ) (hk : k < j)
    (hij : i < j) : rotated h k i j = 0 := by
  induction k generalizing i with
  | zero => exact hh i j hij
  | succ k ih =>
      rw [rotated_succ_apply]
      split_ifs
      · rw [ih k (by omega) (by omega), ih (k + 1) (by omega) (by omega), mul_zero, mul_zero,
          add_zero]
      · rw [ih k (by omega) (by omega), ih (k + 1) (by omega) (by omega), mul_zero, mul_zero,
          add_zero]
      · exact ih i (by omega) hij

/-- Let $h_{ij} = 0$ for $i < j$. Then $R^{(k)}_{ij} = 0$ for $i + 1 < j$ and every $k$: no rotation
fills column $j$ two or more rows above the diagonal.

Rotation $j - 1$ is the first one that changes the entry $(j - 1, j)$, and every earlier
rotation combines two rows that are still zero in column $j$. -/
theorem rotated_eq_zero_of_succ_lt_col (hh : ∀ i j, i < j → h i j = 0) (k i j : ℕ)
    (hij : i + 1 < j) : rotated h k i j = 0 := by
  induction k generalizing i with
  | zero => exact hh i j (by omega)
  | succ k ih =>
      rw [rotated_succ_apply]
      split_ifs
      · rw [ih k (by omega), rotated_eq_of_le h k (k + 1) j le_rfl, hh (k + 1) j (by omega),
          mul_zero, mul_zero, add_zero]
      · rw [ih k (by omega), rotated_eq_of_le h k (k + 1) j le_rfl, hh (k + 1) j (by omega),
          mul_zero, mul_zero, add_zero]
      · exact ih i hij

/-- Let $h_{ij} = 0$ for $i + 1 < j$, as for a tridiagonal array; nothing is assumed below the
subdiagonal. Then $R^{(k)}_{ij} = 0$ for $i + 2 < j$ and every $k$: the rotated array has upper
bandwidth $2$.

Rotation $k$ mixes row $k$, which already has upper bandwidth $2$, with the unchanged row
$k + 1$, which has upper bandwidth $1$. This is the banded upper triangular factor of MINRES. -/
theorem rotated_eq_zero_of_add_two_lt (hh : ∀ i j, i + 1 < j → h i j = 0) (k : ℕ) :
    ∀ i j, i + 2 < j → rotated h k i j = 0 := by
  induction k with
  | zero => intro i j hij; exact hh i j (by omega)
  | succ k ih =>
    intro i j hij
    have hrow : ∀ j, k + 2 < j → rotated h k (k + 1) j = 0 := fun j hj => by
      rw [rotated_eq_of_le h k (k + 1) j le_rfl]
      exact hh _ _ (by omega)
    rw [rotated_succ_apply]
    split_ifs with h1 h2
    · subst h1
      rw [ih i j hij, hrow j (by omega), mul_zero, mul_zero, add_zero]
    · subst h2
      rw [ih k j (by omega), hrow j (by omega), mul_zero, mul_zero, add_zero]
    · exact ih i j hij

/-- Let $h$ be upper Hessenberg. Rotation $k$ does not change the columns $j < k$:
$R^{(k+1)}_{ij} = R^{(k)}_{ij}$ for $j < k$. -/
theorem rotated_succ_eq_of_lt
    (hh : Matrix.IsUpperHessenberg (n := ℕ) h) (k j : ℕ) (hj : j < k) (i : ℕ) :
    rotated h (k + 1) i j = rotated h k i j := by
  rw [rotated_succ_apply]
  split_ifs with h1 h2
  · rw [rotated_eq_zero_of_lt h hh k k j hj (by omega),
      rotated_eq_zero_of_lt h hh k (k + 1) j hj (by omega), mul_zero, mul_zero, add_zero,
      h1, rotated_eq_zero_of_lt h hh k k j hj (by omega)]
  · rw [rotated_eq_zero_of_lt h hh k k j hj (by omega),
      rotated_eq_zero_of_lt h hh k (k + 1) j hj (by omega), mul_zero, mul_zero, add_zero,
      h2, rotated_eq_zero_of_lt h hh k (k + 1) j hj (by omega)]
  · rfl

/-- The rotation $\Omega_k$ as an $(m + 1) \times (m + 1)$ matrix: it has the entries $\bar{c}_k$ at
$(k, k)$, $\bar{s}_k$ at $(k, k + 1)$, $-s_k$ at $(k + 1, k)$ and $c_k$ at $(k + 1, k + 1)$, and
agrees with the identity matrix outside rows and columns $k$ and $k + 1$. -/
noncomputable def givensMatrix (k m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜 :=
  Matrix.of fun i j =>
    if (i : ℕ) = k ∧ (j : ℕ) = k then starRingEnd 𝕜 (givensC h k)
    else if (i : ℕ) = k ∧ (j : ℕ) = k + 1 then starRingEnd 𝕜 (givensS h k)
    else if (i : ℕ) = k + 1 ∧ (j : ℕ) = k then -givensS h k
    else if (i : ℕ) = k + 1 ∧ (j : ℕ) = k + 1 then givensC h k
    else if i = j then 1 else 0

/-- For $k < m$, the rotation $\Omega_k$ is the $2 \times 2$ block
$$\begin{bmatrix} \bar{c}_k & \bar{s}_k \\ -s_k & c_k \end{bmatrix}$$
placed in the coordinate plane of the indices $k$ and $k + 1$, that is, `Matrix.planeEmbed` of
`Numlib.LinearAlgebra.Matrix.PlaneRotation` applied to this block.

Its unitarity therefore follows from `Matrix.planeEmbed_mem_unitaryGroup_iff` together with
$|c_k|^2 + |s_k|^2 = 1$. -/
theorem givensMatrix_eq_planeEmbed (k m : ℕ) (hk : k < m) :
    givensMatrix h k m = Matrix.planeEmbed (⟨k, by omega⟩ : Fin (m + 1)) ⟨k + 1, by omega⟩
      !![starRingEnd 𝕜 (givensC h k), starRingEnd 𝕜 (givensS h k); -givensS h k, givensC h k] := by
  ext i j
  rw [Matrix.planeEmbed_apply, givensMatrix, Matrix.of_apply]
  simp only [Fin.ext_iff]
  split_ifs <;> simp_all

/-- If $m < k$, the rotation $\Omega_k$ of size $m + 1$ is the identity matrix: its plane lies
outside the matrix. -/
theorem givensMatrix_eq_one_of_lt (k m : ℕ) (hk : m < k) : givensMatrix h k m = 1 := by
  ext i j
  have hi := i.isLt
  rw [givensMatrix, Matrix.of_apply, Matrix.one_apply]
  simp only [show (i : ℕ) ≠ k by omega, show (i : ℕ) ≠ k + 1 by omega, false_and, ite_false]

/-- The entry $i$ of $\Omega_k z$, for $k < m$: $\bar{c}_k z_k + \bar{s}_k z_{k+1}$ if $i = k$,
$-s_k z_k + c_k z_{k+1}$ if $i = k + 1$, and $z_i$ otherwise. -/
private theorem givensMatrix_row (k m : ℕ) (hk : k < m) (i : Fin (m + 1)) (z : Fin (m + 1) → 𝕜) :
    ∑ l, givensMatrix h k m i l * z l =
      if (i : ℕ) = k then
        starRingEnd 𝕜 (givensC h k) * z ⟨k, by omega⟩ +
          starRingEnd 𝕜 (givensS h k) * z ⟨k + 1, by omega⟩
      else if (i : ℕ) = k + 1 then
        -givensS h k * z ⟨k, by omega⟩ + givensC h k * z ⟨k + 1, by omega⟩
      else z i := by
  have hpq : (⟨k, by omega⟩ : Fin (m + 1)) ≠ ⟨k + 1, by omega⟩ := by simp [Fin.ext_iff]
  split_ifs with h1 h2
  · rw [Fintype.sum_eq_add _ _ hpq ?_]
    · simp [givensMatrix, h1]
    · rintro l ⟨hlp, hlq⟩
      have hl1 : (l : ℕ) ≠ k := fun hc => hlp (Fin.ext hc)
      have hl2 : (l : ℕ) ≠ k + 1 := fun hc => hlq (Fin.ext hc)
      have hil : i ≠ l := fun hc => hl1 (hc ▸ h1)
      simp [givensMatrix, h1, hl1, hl2, hil]
  · rw [Fintype.sum_eq_add _ _ hpq ?_]
    · simp [givensMatrix, h2]
    · rintro l ⟨hlp, hlq⟩
      have hl1 : (l : ℕ) ≠ k := fun hc => hlp (Fin.ext hc)
      have hl2 : (l : ℕ) ≠ k + 1 := fun hc => hlq (Fin.ext hc)
      have hil : i ≠ l := fun hc => hl2 (hc ▸ h2)
      simp [givensMatrix, h2, hl1, hl2, hil]
  · rw [Finset.sum_eq_single i]
    · simp [givensMatrix, h1, h2]
    · intro l _ hli
      simp [givensMatrix, h1, h2, Ne.symm hli]
    · intro hc; exact absurd (Finset.mem_univ _) hc

/-- Column $k$ of $\Omega_k$ has the entries $\bar{c}_k$ at row $k$, $-s_k$ at row $k + 1$, and $0$
elsewhere. -/
private theorem givensMatrix_col (k m : ℕ) (hkm : k < m + 1) (j : Fin (m + 1)) :
    givensMatrix h k m j ⟨k, hkm⟩ =
      if (j : ℕ) = k then starRingEnd 𝕜 (givensC h k)
      else if (j : ℕ) = k + 1 then -givensS h k else 0 := by
  by_cases h1 : (j : ℕ) = k
  · simp [givensMatrix, h1]
  by_cases h2 : (j : ℕ) = k + 1
  · simp [givensMatrix, h2]
  · have hne : j ≠ (⟨k, hkm⟩ : Fin (m + 1)) := fun hc => h1 (by rw [hc])
    simp [givensMatrix, h1, h2, hne]

/-- Column $k + 1$ of $\Omega_k$ has the entries $\bar{s}_k$ at row $k$, $c_k$ at row $k + 1$, and
$0$ elsewhere. -/
private theorem givensMatrix_col' (k m : ℕ) (hk1m : k + 1 < m + 1) (j : Fin (m + 1)) :
    givensMatrix h k m j ⟨k + 1, hk1m⟩ =
      if (j : ℕ) = k then starRingEnd 𝕜 (givensS h k)
      else if (j : ℕ) = k + 1 then givensC h k else 0 := by
  by_cases h1 : (j : ℕ) = k
  · simp [givensMatrix, h1]
  by_cases h2 : (j : ℕ) = k + 1
  · simp [givensMatrix, h2]
  · have hne : j ≠ (⟨k + 1, hk1m⟩ : Fin (m + 1)) := fun hc => h2 (by rw [hc])
    simp [givensMatrix, h1, h2, hne]

/-- Outside the columns $k$ and $k + 1$, the matrix $\Omega_k$ agrees with the identity matrix. -/
private theorem givensMatrix_apply_of_col_ne (k m : ℕ) (p q : Fin (m + 1)) (h1 : (q : ℕ) ≠ k)
    (h2 : (q : ℕ) ≠ k + 1) : givensMatrix h k m p q = if p = q then 1 else 0 := by
  simp [givensMatrix, h1, h2]

/-- For $k < m$ and $\rho_k \neq 0$, the rotation $\Omega_k$ of size $m + 1$ is unitary.

It differs from the identity matrix only in the four entries in rows and columns $k$ and
$k + 1$, and $|c_k|^2 + |s_k|^2 = 1$ makes that $2 \times 2$ block unitary. -/
theorem givensMatrix_mem_unitaryGroup (k m : ℕ) (hk : k < m) (hρ : givensRho h k ≠ 0) :
    givensMatrix h k m ∈ Matrix.unitaryGroup (Fin (m + 1)) 𝕜 := by
  have hkm : k < m + 1 := by omega
  have hk1m : k + 1 < m + 1 := by omega
  have hcast : ((‖givensC h k‖ ^ 2 + ‖givensS h k‖ ^ 2 : ℝ) : 𝕜)
      = (‖givensC h k‖ : 𝕜) ^ 2 + (‖givensS h k‖ : 𝕜) ^ 2 := by
    push_cast
    ring
  have hcs : starRingEnd 𝕜 (givensC h k) * givensC h k +
      starRingEnd 𝕜 (givensS h k) * givensS h k = 1 := by
    rw [RCLike.conj_mul, RCLike.conj_mul, ← hcast, norm_givensC_sq_add_norm_givensS_sq h k hρ,
      RCLike.ofReal_one]
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  rw [Matrix.mul_apply, givensMatrix_row h k m hk i (fun l => (star (givensMatrix h k m)) l j)]
  simp only [Matrix.star_apply, RCLike.star_def, givensMatrix_col h k m hkm j,
    givensMatrix_col' h k m hk1m j]
  rcases eq_or_ne (j : ℕ) k with hj | hj
  · -- column `k`: the entries seen by the row are `conj c` and `conj s`
    simp only [ite_eq_left hj]
    rcases eq_or_ne (i : ℕ) k with hi | hi
    · have hij : i = j := Fin.ext (hi.trans hj.symm)
      rw [ite_eq_left hi, hij, Matrix.one_apply_eq, starRingEnd_self_apply,
        starRingEnd_self_apply]
      exact hcs
    rcases eq_or_ne (i : ℕ) (k + 1) with hi' | hi'
    · have hij : i ≠ j := fun hc => by rw [hc, hj] at hi'; omega
      rw [ite_eq_right hi, ite_eq_left hi', Matrix.one_apply_ne hij, starRingEnd_self_apply,
        starRingEnd_self_apply]
      ring
    · have hij : i ≠ j := fun hc => hi (by rw [hc, hj])
      rw [ite_eq_right hi, ite_eq_right hi', Matrix.one_apply_ne hij,
        givensMatrix_apply_of_col_ne h k m j i hi hi',
        ite_eq_right (fun hc => hij hc.symm), map_zero]
  rcases eq_or_ne (j : ℕ) (k + 1) with hj' | hj'
  · simp only [ite_eq_right hj, ite_eq_left hj']
    rcases eq_or_ne (i : ℕ) k with hi | hi
    · have hij : i ≠ j := fun hc => hj (by rw [← hc, hi])
      rw [ite_eq_left hi, Matrix.one_apply_ne hij, map_neg]
      ring
    rcases eq_or_ne (i : ℕ) (k + 1) with hi' | hi'
    · have hij : i = j := Fin.ext (hi'.trans hj'.symm)
      rw [ite_eq_right hi, ite_eq_left hi', hij, Matrix.one_apply_eq, map_neg, ← hcs]
      ring
    · have hij : i ≠ j := fun hc => hi' (by rw [hc, hj'])
      rw [ite_eq_right hi, ite_eq_right hi', Matrix.one_apply_ne hij,
        givensMatrix_apply_of_col_ne h k m j i hi hi',
        ite_eq_right (fun hc => hij hc.symm), map_zero]
  · simp only [ite_eq_right hj, ite_eq_right hj']
    rcases eq_or_ne (i : ℕ) k with hi | hi
    · have hij : i ≠ j := fun hc => hj (by rw [← hc, hi])
      rw [ite_eq_left hi, Matrix.one_apply_ne hij, map_zero]
      ring
    rcases eq_or_ne (i : ℕ) (k + 1) with hi' | hi'
    · have hij : i ≠ j := fun hc => hj' (by rw [← hc, hi'])
      rw [ite_eq_right hi, ite_eq_left hi', Matrix.one_apply_ne hij, map_zero]
      ring
    · rw [ite_eq_right hi, ite_eq_right hi', givensMatrix_apply_of_col_ne h k m j i hi hi']
      rcases eq_or_ne j i with hji | hji
      · rw [ite_eq_left hji, map_one, hji, Matrix.one_apply_eq]
      · rw [ite_eq_right hji, map_zero, Matrix.one_apply_ne (fun hc => hji hc.symm)]

/-- For $k < m$, $\Omega_k \bar{R}^{(k)}_m = \bar{R}^{(k+1)}_m$, where $\bar{R}^{(k)}_m$ is the
$(m + 1) \times m$ matrix of $R^{(k)}$. -/
theorem givensMatrix_mul_hessenbergOf_rotated (k m : ℕ) (hk : k < m) :
    givensMatrix h k m * hessenbergOf (rotated h k) m = hessenbergOf (rotated h (k + 1)) m := by
  ext i j
  rw [Matrix.mul_apply, givensMatrix_row h k m hk i (fun l => hessenbergOf (rotated h k) m l j)]
  change _ = rotated h (k + 1) (i : ℕ) (j : ℕ)
  rw [rotated_succ_apply]
  split_ifs <;> rfl

/-- The product $Q^{(n)}_m = \Omega_{n-1} \cdots \Omega_0$ of the first $n$ rotations, as an
$(m + 1) \times (m + 1)$ matrix.

Only $n = m$ occurs in the factorization $Q_m \bar{H}_m = \bar{R}_m$, but the partial products
carry the induction and describe the breakdown case, where the last rotation degenerates. -/
noncomputable def givensQAux (n m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜 :=
  (((List.range n).map fun k => givensMatrix h k m).reverse).prod

/-- The accumulated rotation $Q_m = \Omega_{m-1} \cdots \Omega_0$, an $(m + 1) \times (m + 1)$
matrix. -/
noncomputable def givensQ (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜 := givensQAux h m m

/-- The matrix $Q_m$ is the partial product $Q^{(m)}_m$. -/
theorem givensQ_eq_givensQAux (m : ℕ) : givensQ h m = givensQAux h m m := rfl

/-- The product of no rotations is the identity matrix: $Q^{(0)}_m = I$. -/
@[simp]
theorem givensQAux_zero (m : ℕ) : givensQAux h 0 m = 1 := by simp [givensQAux]

/-- One more rotation multiplies on the left: $Q^{(n+1)}_m = \Omega_n Q^{(n)}_m$. -/
theorem givensQAux_succ (n m : ℕ) :
    givensQAux h (n + 1) m = givensMatrix h n m * givensQAux h n m := by
  rw [givensQAux, givensQAux, List.range_succ, List.map_append, List.reverse_append]
  simp

/-- The rotation matrices do not depend on the size: for $i, j \le m$, the entry $(i, j)$ of
$\Omega_k$ of size $m + 2$ equals the entry $(i, j)$ of $\Omega_k$ of size $m + 1$. -/
theorem givensMatrix_castSucc (k m : ℕ) (i j : Fin (m + 1)) :
    givensMatrix h k (m + 1) i.castSucc j.castSucc = givensMatrix h k m i j := by
  simp only [givensMatrix, Matrix.of_apply, Fin.val_castSucc, Fin.castSucc_inj]

/-- The last row of $\Omega_m$ of size $m + 2$ has the entries $-s_m$ at column $m$, $c_m$ at column
$m + 1$, and $0$ elsewhere. -/
theorem givensMatrix_last_row (m : ℕ) (p : Fin (m + 2)) :
    givensMatrix h m (m + 1) (Fin.last (m + 1)) p
      = if (p : ℕ) = m then -givensS h m
        else if (p : ℕ) = m + 1 then givensC h m else 0 := by
  have hi : ((Fin.last (m + 1) : Fin (m + 2)) : ℕ) = m + 1 := rfl
  by_cases h1 : (p : ℕ) = m
  · simp [givensMatrix, h1]
  by_cases h2 : (p : ℕ) = m + 1
  · simp [givensMatrix, h2]
  · have hne : (Fin.last (m + 1) : Fin (m + 2)) ≠ p := fun hc => h2 (by rw [← hc, hi])
    simp [givensMatrix, h1, h2, hne]

/-- The rows $i > n$ of $Q^{(n)}_m$ are rows of the identity matrix. -/
theorem givensQAux_apply_of_row_lt (m : ℕ) (j : Fin (m + 1)) :
    ∀ (n : ℕ) (i : Fin (m + 1)), n < (i : ℕ) →
      givensQAux h n m i j = if i = j then 1 else 0 := by
  intro n
  induction n with
  | zero => intro i _; simp [Matrix.one_apply]
  | succ n ih =>
      intro i hi
      have h1 : (i : ℕ) ≠ n := by omega
      have h2 : (i : ℕ) ≠ n + 1 := by omega
      rw [givensQAux_succ, Matrix.mul_apply]
      have hrow : ∀ p : Fin (m + 1),
          givensMatrix h n m i p = if i = p then 1 else 0 := fun p => by
        simp [givensMatrix, h1, h2]
      simp only [hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      exact ih i (by omega)

/-- For $n \le m$, the leading $(m + 1) \times (m + 1)$ block of $Q^{(n)}_{m+1}$ is $Q^{(n)}_m$. -/
theorem givensQAux_castSucc (m : ℕ) :
    ∀ (n : ℕ), n ≤ m → ∀ (i j : Fin (m + 1)),
      givensQAux h n (m + 1) i.castSucc j.castSucc = givensQAux h n m i j := by
  intro n
  induction n with
  | zero => intro _ i j; simp [Matrix.one_apply, Fin.castSucc_inj]
  | succ n ih =>
      intro hn i j
      rw [givensQAux_succ, givensQAux_succ, Matrix.mul_apply, Matrix.mul_apply,
        Fin.sum_univ_castSucc]
      have hne : (Fin.last (m + 1) : Fin (m + 2)) ≠ j.castSucc := by
        have := j.isLt
        simp only [Ne, Fin.ext_iff, Fin.val_last, Fin.val_castSucc]
        omega
      have hlast : givensQAux h n (m + 1) (Fin.last (m + 1)) j.castSucc = 0 := by
        rw [givensQAux_apply_of_row_lt h (m + 1) j.castSucc n (Fin.last (m + 1))
          (by rw [Fin.val_last]; omega), ite_eq_right hne]
      rw [hlast, mul_zero, add_zero]
      exact Finset.sum_congr rfl fun p _ => by
        rw [givensMatrix_castSucc, ih (by omega) p j]

/-- For $n \le m$, $Q^{(n)}_m \bar{H}_m = \bar{R}^{(n)}_m$, the $(m + 1) \times m$ matrix of
$R^{(n)}$. -/
theorem givensQAux_mul_hessenbergOf {n m : ℕ} (hn : n ≤ m) :
    givensQAux h n m * hessenbergOf h m = hessenbergOf (rotated h n) m := by
  induction n with
  | zero => simp [rotated]
  | succ n ih =>
      rw [givensQAux_succ, Matrix.mul_assoc, ih (by omega),
        givensMatrix_mul_hessenbergOf_rotated h n m (by omega)]

/-- For every coefficient array $h$ and every $m$,
$$Q_m \bar{H}_m = \bar{R}_m,$$
where $\bar{R}_m$ is the $(m + 1) \times m$ matrix of the rotated coefficients $R^{(m)}$
([saad2003iterative], (6.38)–(6.39)). For upper Hessenberg $h$ the matrix $\bar{R}_m$ is upper
triangular with a zero last row (`Krylov.rotated_eq_zero_of_lt`, `Krylov.rotated_last_row`). -/
theorem givensQ_mul_hessenbergOf (m : ℕ) :
    givensQ h m * hessenbergOf h m = hessenbergOf (rotated h m) m :=
  givensQAux_mul_hessenbergOf h le_rfl

/-- For $n \le m$, if $\rho_k \neq 0$ for every $k < n$, then $Q^{(n)}_m$ is unitary. -/
theorem givensQAux_mem_unitaryGroup {n m : ℕ} (hn : n ≤ m) (hρ : ∀ k < n, givensRho h k ≠ 0) :
    givensQAux h n m ∈ Matrix.unitaryGroup (Fin (m + 1)) 𝕜 := by
  refine Submonoid.list_prod_mem _ ?_
  intro M hM
  rw [List.mem_reverse, List.mem_map] at hM
  obtain ⟨k, hk, rfl⟩ := hM
  rw [List.mem_range] at hk
  exact givensMatrix_mem_unitaryGroup h k m (by omega) (hρ k hk)

/-- If $\rho_k \neq 0$ for every $k < m$, then the accumulated rotation
$Q_m = \Omega_{m-1} \cdots \Omega_0$ is unitary.

Then $Q_m$ is an isometry for the Euclidean norm, so the least-squares quantity
$\|\beta e_1 - \bar{H}_m y\|$ can be computed from the triangular factor
$\bar{R}_m = Q_m \bar{H}_m$. This leads to $\|r_m\| = |\gamma_m|$. -/
theorem givensQ_mem_unitaryGroup (m : ℕ) (hρ : ∀ k < m, givensRho h k ≠ 0) :
    givensQ h m ∈ Matrix.unitaryGroup (Fin (m + 1)) 𝕜 :=
  givensQAux_mem_unitaryGroup h le_rfl hρ

/-- The columns $j > n$ of $Q^{(n)}_m$ are columns of the identity matrix: outside its leading
$(n + 1) \times (n + 1)$ block the product of the first $n$ rotations is the identity. -/
theorem givensQAux_apply_of_lt (n m : ℕ) (i j : Fin (m + 1)) (hj : n < (j : ℕ)) :
    givensQAux h n m i j = if i = j then 1 else 0 := by
  have key : ∀ n : ℕ, n < (j : ℕ) → ∀ i : Fin (m + 1),
      givensQAux h n m i j = if i = j then 1 else 0 := by
    intro n
    induction n with
    | zero => intro _ i; simp [Matrix.one_apply]
    | succ n ih =>
        intro hn i
        have hcol := ih (by omega)
        rw [givensQAux_succ, Matrix.mul_apply]
        simp only [hcol]
        rw [Finset.sum_eq_single j]
        · rw [ite_eq_left rfl, mul_one,
            givensMatrix_apply_of_col_ne h n m i j (by omega) (by omega)]
        · intro l _ hl
          rw [ite_eq_right hl, mul_zero]
        · intro hc; exact absurd (Finset.mem_univ _) hc
  exact key n hj i

/-- **The last row of the rotated factor.** For every coefficient array $h$ and every $l \le m + 1$,
$$R^{(m)}_{m,l} = \sum_{i=0}^{m} (Q_m)_{m,i} \, h_{il}.$$

`Krylov.givensQ_mul_hessenbergOf` gives this only for $l < m$, because $\bar{H}_m$ stops at
column $m - 1$. The matrix $\bar{H}_{m+2}$ reaches column $m + 1$, and
`Krylov.givensQAux_castSucc` identifies the leading block of $Q^{(m)}_{m+2}$ with $Q_m$; the
other entries of its row $m$ are those of the identity matrix. The column $l = m + 1$ carries
the subdiagonal entry that survives one application of the operator. -/
theorem rotated_row_eq_sum_givensQ (m l : ℕ) (hl : l ≤ m + 1) :
    rotated h m m l = ∑ i : Fin (m + 1), givensQ h m (Fin.last m) i * h (i : ℕ) l := by
  have hmul := givensQAux_mul_hessenbergOf h (show m ≤ m + 2 by omega)
  have key := congrFun (congrFun hmul (((Fin.last m).castSucc.castSucc : Fin (m + 3))))
    (⟨l, by omega⟩ : Fin (m + 2))
  rw [Matrix.mul_apply] at key
  rw [show rotated h m m l = hessenbergOf (rotated h m) (m + 2)
      ((Fin.last m).castSucc.castSucc) (⟨l, by omega⟩ : Fin (m + 2)) from rfl, ← key,
    Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hrow : (((Fin.last m).castSucc.castSucc : Fin (m + 3)) : ℕ) = m := rfl
  have hz1 : givensQAux h m (m + 2) ((Fin.last m).castSucc.castSucc)
      (Fin.last (m + 2)) = 0 := by
    rw [givensQAux_apply_of_lt h m (m + 2) _ _ (by simp), ite_eq_right]
    simp only [Fin.ext_iff, hrow, Fin.val_last]
    omega
  have hz2 : givensQAux h m (m + 2) ((Fin.last m).castSucc.castSucc)
      (Fin.last (m + 1)).castSucc = 0 := by
    rw [givensQAux_apply_of_lt h m (m + 2) _ _ (by simp), ite_eq_right]
    simp only [Fin.ext_iff, hrow, Fin.val_castSucc, Fin.val_last]
    omega
  rw [hz1, hz2, zero_mul, zero_mul, add_zero, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [givensQAux_castSucc h (m + 1) m (by omega) (Fin.last m).castSucc i.castSucc,
    givensQAux_castSucc h m m le_rfl (Fin.last m) i, givensQ_eq_givensQAux]
  rfl

/-- **The last row of the accumulated rotation, one step further**, off the diagonal: for $j \le m$,
$$(Q_{m+1})_{m+1,j} = -s_m \, (Q_m)_{m,j}.$$
The rotation $\Omega_m$ scales the last row of $Q_m$ by $-s_m$. With
`Krylov.givensQ_last_row_last` this is the whole recurrence that the residual identity of a
minimal-residual method needs. -/
theorem givensQ_last_row_castSucc (m : ℕ) (j : Fin (m + 1)) :
    givensQ h (m + 1) (Fin.last (m + 1)) j.castSucc
      = -givensS h m * givensQ h m (Fin.last m) j := by
  rw [givensQ_eq_givensQAux, givensQAux_succ, Matrix.mul_apply, Fin.sum_univ_castSucc]
  have hlastrow : givensQAux h m (m + 1) (Fin.last (m + 1)) j.castSucc = 0 := by
    rw [givensQAux_apply_of_row_lt h (m + 1) j.castSucc m (Fin.last (m + 1))
      (by rw [Fin.val_last]; omega)]
    refine ite_eq_right fun hc => ?_
    have := j.isLt
    have h1 : ((Fin.last (m + 1) : Fin (m + 2)) : ℕ) = ((j.castSucc : Fin (m + 2)) : ℕ) := by
      rw [hc]
    rw [Fin.val_last, Fin.val_castSucc] at h1
    omega
  rw [hlastrow, mul_zero, add_zero]
  rw [Finset.sum_eq_single (Fin.last m)]
  · rw [givensMatrix_last_row h m ((Fin.last m : Fin (m + 1)).castSucc),
      ite_eq_left (by rw [Fin.val_castSucc, Fin.val_last]),
      givensQAux_castSucc h m m le_rfl (Fin.last m) j, givensQ_eq_givensQAux]
  · intro p _ hp
    have hpm : (p : ℕ) ≠ m := fun hc => hp (Fin.ext (by rw [hc, Fin.val_last]))
    rw [givensMatrix_last_row h m (p.castSucc), Fin.val_castSucc, ite_eq_right hpm,
      ite_eq_right (by have := p.isLt; omega), zero_mul]
  · intro hc
    exact absurd (Finset.mem_univ _) hc

/-- **The last row of the accumulated rotation, one step further**, on the diagonal:
$(Q_{m+1})_{m+1,m+1} = c_m$, because $Q^{(m)}_{m+1}$ does not change the last column. -/
theorem givensQ_last_row_last (m : ℕ) :
    givensQ h (m + 1) (Fin.last (m + 1)) (Fin.last (m + 1)) = givensC h m := by
  rw [givensQ_eq_givensQAux, givensQAux_succ, Matrix.mul_apply,
    Finset.sum_eq_single (Fin.last (m + 1))]
  · rw [givensQAux_apply_of_lt h m (m + 1) (Fin.last (m + 1)) (Fin.last (m + 1))
      (by rw [Fin.val_last]; omega), ite_eq_left rfl, mul_one,
      givensMatrix_last_row h m (Fin.last (m + 1)),
      ite_eq_right (by rw [Fin.val_last]; omega), ite_eq_left (by rw [Fin.val_last])]
  · intro p _ hp
    rw [givensQAux_apply_of_lt h m (m + 1) p (Fin.last (m + 1))
      (by rw [Fin.val_last]; omega), ite_eq_right hp, mul_zero]
  · intro hc
    exact absurd (Finset.mem_univ _) hc

/-- The right-hand side after $n$ rotations: the sequence
$(g_0, \dots, g_{n-1}, \gamma_n, 0, 0, \dots)$. -/
noncomputable def gvecTrunc (β : 𝕜) (n i : ℕ) : 𝕜 :=
  if i < n then gvec h β i else if i = n then gamma h β n else 0

/-- The entry $n$ of the right-hand side after $n$ rotations is $\gamma_n$. -/
theorem gvecTrunc_self (β : 𝕜) (n : ℕ) : gvecTrunc h β n n = gamma h β n := by
  simp [gvecTrunc]

/-- The entry $n + 1$ of the right-hand side after $n$ rotations is $0$. -/
theorem gvecTrunc_succ (β : 𝕜) (n : ℕ) : gvecTrunc h β n (n + 1) = 0 := by
  simp [gvecTrunc]

/-- For $i < n$, the entry $i$ of the right-hand side after $n$ rotations is $g_i$. -/
theorem gvecTrunc_of_lt (β : 𝕜) {n i : ℕ} (hi : i < n) :
    gvecTrunc h β n i = gvec h β i := by simp [gvecTrunc, hi]

/-- For $i > n$, the entry $i$ of the right-hand side after $n$ rotations is $0$. -/
theorem gvecTrunc_of_gt (β : 𝕜) {n i : ℕ} (hi : n < i) : gvecTrunc h β n i = 0 := by
  simp [gvecTrunc, Nat.not_lt.mpr hi.le, hi.ne']

/-- For $n \le m$, the first $n$ rotations carry $\beta e_1 \in \mathbb{K}^{m+1}$ to
$(g_0, \dots, g_{n-1}, \gamma_n, 0, \dots, 0)$ ([saad2003iterative], (6.44)–(6.46)). -/
theorem givensQAux_mulVec_firstVec (β : 𝕜) (m : ℕ) : ∀ n, n ≤ m →
    (givensQAux h n m).mulVec (firstVec β (m + 1)) =
      fun i : Fin (m + 1) => gvecTrunc h β n (i : ℕ) := by
  intro n
  induction n with
  | zero =>
      intro _
      funext i
      simp only [givensQAux_zero, Matrix.one_mulVec, gvecTrunc, firstVec, Nat.not_lt_zero, gamma]
      simp
  | succ n ih =>
      intro hn
      funext i
      have hrow := givensMatrix_row h n m (by omega) i
        (fun l : Fin (m + 1) => gvecTrunc h β n (l : ℕ))
      rw [givensQAux_succ, ← Matrix.mulVec_mulVec, ih (by omega)]
      simp only [Matrix.mulVec, dotProduct]
      rw [hrow]
      change _ = gvecTrunc h β (n + 1) (i : ℕ)
      have e1 : ((⟨n, by omega⟩ : Fin (m + 1)) : ℕ) = n := rfl
      have e2 : ((⟨n + 1, by omega⟩ : Fin (m + 1)) : ℕ) = n + 1 := rfl
      rw [e1, e2, gvecTrunc_self, gvecTrunc_succ]
      by_cases h1 : (i : ℕ) = n
      · rw [ite_eq_left h1, gvecTrunc_of_lt h β (by omega : (i : ℕ) < n + 1), h1, gvec,
          mul_zero, add_zero]
      by_cases h2 : (i : ℕ) = n + 1
      · rw [ite_eq_right h1, ite_eq_left h2, h2, gvecTrunc_self, gamma_succ, mul_zero, add_zero]
      · rw [ite_eq_right h1, ite_eq_right h2]
        rcases Nat.lt_or_ge (i : ℕ) n with hi | hi
        · rw [gvecTrunc_of_lt h β hi, gvecTrunc_of_lt h β (by omega)]
        · rw [gvecTrunc_of_gt h β (by omega), gvecTrunc_of_gt h β (by omega)]

/-- For every $\beta$ and $m$,
$$Q_m (\beta e_1) = (g_0, \dots, g_{m-1}, \gamma_m)$$
([saad2003iterative], (6.40), (6.44)–(6.47)). -/
theorem givensQ_mulVec_firstVec (β : 𝕜) (m : ℕ) :
    (givensQ h m).mulVec (firstVec β (m + 1)) =
      fun i : Fin (m + 1) => if (i : ℕ) < m then gvec h β i else gamma h β m := by
  rw [givensQ_eq_givensQAux, givensQAux_mulVec_firstVec h β m m le_rfl]
  funext i
  by_cases hi : (i : ℕ) < m
  · rw [gvecTrunc_of_lt h β hi, ite_eq_left hi]
  · have : (i : ℕ) = m := by omega
    rw [ite_eq_right hi, this, gvecTrunc_self]

/-- Let $h$ be upper Hessenberg. The last row of $\bar{R}_m$ vanishes: $R^{(m)}_{mj} = 0$ for
$j < m$. -/
theorem rotated_last_row (hh : Matrix.IsUpperHessenberg (n := ℕ) h) (m j : ℕ) (hj : j < m) :
    rotated h m m j = 0 :=
  rotated_eq_zero_of_lt h hh m m j hj hj

/-! ### The triangular factor $R$ -/

/-- The parameter $c_k$ vanishes if and only if the pivot entry $R^{(k)}_{kk}$ vanishes. -/
theorem givensC_eq_zero_iff (k : ℕ) : givensC h k = 0 ↔ rotated h k k k = 0 := by
  rw [givensC, div_eq_zero_iff]
  refine ⟨fun hc => hc.elim id fun h0 => ?_, fun h0 => Or.inl h0⟩
  exact (rotated_eq_zero_of_givensRho_eq_zero h (by simpa using h0)).1

/-- If $R^{(k)}_{kk} \neq 0$, then $\rho_k \neq 0$, so rotation $k$ does not degenerate. -/
theorem givensRho_ne_zero_of_rotated_ne_zero {k : ℕ} (hk : rotated h k k k ≠ 0) :
    givensRho h k ≠ 0 := fun h0 => hk (rotated_eq_zero_of_givensRho_eq_zero h h0).1

/-- Let $h$ be upper Hessenberg. For $j < n$, the diagonal entry $R^{(n)}_{jj}$ is $\rho_j$
([saad2003iterative], (6.37)). -/
theorem rotated_diag (hh : Matrix.IsUpperHessenberg (n := ℕ) h) {n j : ℕ} (hj : j < n) :
    rotated h n j j = (givensRho h j : 𝕜) := by
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge j n with hjn | hjn
      · rw [rotated_succ_eq_of_lt h hh n j hjn j]
        exact ih hjn
      · have hjn' : j = n := by omega
        subst hjn'
        exact rotated_succ_self h j

/-- Let $h$ be upper Hessenberg. For $N \le n + 1$, the $N \times N$ matrix of $R^{(n)}$ is upper
triangular: the first $n$ columns have been triangularized, and column $n$ ends on the diagonal. -/
theorem hessenbergSqOf_rotated_isUpperTriangular
    (hh : Matrix.IsUpperHessenberg (n := ℕ) h) {n N : ℕ}
    (hN : N ≤ n + 1) : (hessenbergSqOf (rotated h n) N).IsUpperTriangular := by
  intro i j hij
  have h1 : (j : ℕ) < (i : ℕ) := hij
  exact rotated_eq_zero_of_lt h hh n i j (by omega) h1

/-- Let $h$ be upper Hessenberg. For $N \le n + 1$, the determinant of the $N \times N$ matrix of
$R^{(n)}$ is the product $\prod_{j<N} R^{(n)}_{jj}$ of its diagonal entries. -/
theorem det_hessenbergSqOf_rotated (hh : Matrix.IsUpperHessenberg (n := ℕ) h) {n N : ℕ}
    (hN : N ≤ n + 1) :
    (hessenbergSqOf (rotated h n) N).det = ∏ j : Fin N, rotated h n (j : ℕ) (j : ℕ) :=
  Matrix.det_of_isUpperTriangular (hessenbergSqOf_rotated_isUpperTriangular h hh hN)

/-- Let $h$ be upper Hessenberg and $N \le n + 1$. If $R^{(n)}_{jj} \neq 0$ for every $j < N$, then
the $N \times N$ matrix of $R^{(n)}$ is nonsingular. -/
theorem isUnit_hessenbergSqOf_rotated (hh : Matrix.IsUpperHessenberg (n := ℕ) h) {n N : ℕ}
    (hN : N ≤ n + 1) (hd : ∀ j < N, rotated h n j j ≠ 0) :
    IsUnit (hessenbergSqOf (rotated h n) N) := by
  rw [Matrix.isUnit_iff_isUnit_det, det_hessenbergSqOf_rotated h hh hN, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr fun j _ => hd (j : ℕ) j.isLt

/-- Let $h$ be upper Hessenberg. If $\rho_k \neq 0$ for every $k < m$, then $R_m$ is nonsingular. -/
theorem isUnit_hessenbergSqOf_rotated_self (hh : Matrix.IsUpperHessenberg (n := ℕ) h) {m : ℕ}
    (hρ : ∀ k < m, givensRho h k ≠ 0) : IsUnit (hessenbergSqOf (rotated h m) m) :=
  isUnit_hessenbergSqOf_rotated h hh (by omega) fun j hj => by
    rw [rotated_diag h hh hj]
    simpa using hρ j hj

/-! ### The least-squares residual in rotated coordinates -/

/-- Let $h$ be upper Hessenberg, and let $\rho_k \neq 0$ for every $k < m$. For every $\beta$ and
$y \in \mathbb{K}^m$,
$$\|\beta e_1 - \bar{H}_m y\|_2^2 = \|g - R_m y\|_2^2 + |\gamma_m|^2, \qquad g = (g_0, \dots,
  g_{m-1}).$$
This is (6.41) of [saad2003iterative]: the rotations are an isometry that carries
$\beta e_1 - \bar{H}_m y$ to $(g - R_m y, \gamma_m)$, so the square of its norm splits into the
part that the triangular system can annihilate and the fixed remainder $|\gamma_m|^2$. -/
theorem norm_sq_firstVec_sub_mulVec_eq (hh : Matrix.IsUpperHessenberg (n := ℕ) h) {m : ℕ}
    (hρ : ∀ k < m, givensRho h k ≠ 0) (β : 𝕜) (y : Fin m → 𝕜) :
    ‖(WithLp.toLp 2 (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) :
        EuclideanSpace 𝕜 (Fin (m + 1)))‖ ^ 2 =
      ‖(WithLp.toLp 2 ((fun i : Fin m => gvec h β (i : ℕ)) -
          (hessenbergSqOf (rotated h m) m).mulVec y) : EuclideanSpace 𝕜 (Fin m))‖ ^ 2 +
        ‖gamma h β m‖ ^ 2 := by
  have hmul : (givensQ h m).mulVec (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) =
      fun i : Fin (m + 1) =>
        (if (i : ℕ) < m then gvec h β (i : ℕ) else gamma h β m) -
          (hessenbergOf (rotated h m) m).mulVec y i := by
    rw [Matrix.mulVec_sub, givensQ_mulVec_firstVec, Matrix.mulVec_mulVec,
      givensQ_mul_hessenbergOf]
    rfl
  have hlast : (hessenbergOf (rotated h m) m).mulVec y (Fin.last m) = 0 := by
    simp only [Matrix.mulVec, dotProduct, hessenbergOf, Matrix.of_apply, Fin.val_last]
    exact Finset.sum_eq_zero fun j _ =>
      by rw [rotated_last_row h hh m (j : ℕ) j.isLt, zero_mul]
  rw [← Matrix.norm_toLp_mulVec_of_mem_unitaryGroup (givensQ_mem_unitaryGroup h m hρ), hmul,
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hi : ((i.castSucc : Fin (m + 1)) : ℕ) < m := i.isLt
    simp only [Pi.sub_apply, ite_eq_left hi]
    rfl
  · simp [hlast]

/-- Let $h$ be upper Hessenberg. If $\rho_m = 0$, then row $m$ of $R^{(m+1)}$ vanishes in the
columns $j \le m$. -/
theorem rotated_succ_row_eq_zero_of_givensRho_eq_zero
    (hh : Matrix.IsUpperHessenberg (n := ℕ) h) {m : ℕ}
    (hρm : givensRho h m = 0) {j : ℕ} (hj : j ≤ m) : rotated h (m + 1) m j = 0 := by
  rcases Nat.lt_or_ge j m with hjm | hjm
  · exact rotated_eq_zero_of_lt h hh (m + 1) m j (by omega) hjm
  · have hjm' : j = m := by omega
    rw [hjm', rotated_succ_self h m, hρm]
    simp

/-- If $\rho_m = 0$, then $c_m = 0$, so $g_m = \bar{c}_m \gamma_m = 0$. -/
theorem gvec_eq_zero_of_givensRho_eq_zero {m : ℕ} (hρm : givensRho h m = 0) (β : 𝕜) :
    gvec h β m = 0 := by
  rw [gvec, (givensC_eq_zero_iff h m).mpr (rotated_eq_zero_of_givensRho_eq_zero h hρm).1,
    map_zero, zero_mul]

/-- If $F \in \mathbb{K}^{N+2}$ has last entry $0$, $G \in \mathbb{K}^{N+1}$, and
$|F_i|^2 = |G_i|^2$ for $i < N$ and $|F_N|^2 = |G_N|^2 + C$, then $\|F\|^2 = \|G\|^2 + C$. -/
private theorem norm_sq_split_aux {N : ℕ} (F : Fin (N + 2) → 𝕜) (G : Fin (N + 1) → 𝕜) (C : ℝ)
    (hlast : F (Fin.last (N + 1)) = 0)
    (hterm : ∀ i : Fin (N + 1),
      ‖F i.castSucc‖ ^ 2 = ‖G i‖ ^ 2 + (if (i : ℕ) = N then C else 0)) :
    ‖(WithLp.toLp 2 F : EuclideanSpace 𝕜 (Fin (N + 2)))‖ ^ 2 =
      ‖(WithLp.toLp 2 G : EuclideanSpace 𝕜 (Fin (N + 1)))‖ ^ 2 + C := by
  have h1 : ∑ i : Fin (N + 2), ‖F i‖ ^ 2 =
      ∑ i : Fin (N + 1), ‖F i.castSucc‖ ^ 2 + ‖F (Fin.last (N + 1))‖ ^ 2 :=
    Fin.sum_univ_castSucc _
  have h2 : ∑ i : Fin (N + 1), ‖F i.castSucc‖ ^ 2 =
      ∑ i : Fin (N + 1), (‖G i‖ ^ 2 + (if (i : ℕ) = N then C else 0)) :=
    Finset.sum_congr rfl fun i _ => hterm i
  have h4 : ∑ i : Fin (N + 1), (if (i : ℕ) = N then C else 0) = C := by
    rw [Finset.sum_eq_single (Fin.last N)]
    · simp
    · intro l _ hl
      have hl' : (l : ℕ) ≠ N := fun hc => hl (Fin.ext (by simpa using hc))
      rw [ite_eq_right hl']
    · intro hc; exact absurd (Finset.mem_univ _) hc
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only
  rw [h1, hlast, norm_zero, h2, Finset.sum_add_distrib, h4]
  ring

/-- Let $h$ be upper Hessenberg, let $\rho_k \neq 0$ for every $k < m$, and let $\rho_m = 0$. For
every $\beta$ and $y \in \mathbb{K}^{m+1}$,
$$\|\beta e_1 - \bar{H}_{m+1} y\|_2^2 = \|g - R_{m+1} y\|_2^2 + |\gamma_m|^2, \qquad g = (g_0,
  \dots, g_m).$$

This is the breakdown counterpart of `Krylov.norm_sq_firstVec_sub_mulVec_eq`. Rotation $m$
degenerates, so both entries that it acts on already vanish. The first $m$ rotations still split
the least-squares residual of step $m + 1$, but the remainder is $|\gamma_m|^2$, not
$|\gamma_{m+1}|^2 = 0$. -/
theorem norm_sq_firstVec_sub_mulVec_eq_of_breakdown
    (hh : Matrix.IsUpperHessenberg (n := ℕ) h) {m : ℕ}
    (hρ : ∀ k < m, givensRho h k ≠ 0) (hρm : givensRho h m = 0) (β : 𝕜) (y : Fin (m + 1) → 𝕜) :
    ‖(WithLp.toLp 2 (firstVec β (m + 2) - (hessenbergOf h (m + 1)).mulVec y) :
        EuclideanSpace 𝕜 (Fin (m + 2)))‖ ^ 2 =
      ‖(WithLp.toLp 2 ((fun i : Fin (m + 1) => gvec h β (i : ℕ)) -
          (hessenbergSqOf (rotated h (m + 1)) (m + 1)).mulVec y) :
            EuclideanSpace 𝕜 (Fin (m + 1)))‖ ^ 2 +
        ‖gamma h β m‖ ^ 2 := by
  obtain ⟨ha, hb⟩ := rotated_eq_zero_of_givensRho_eq_zero h hρm
  have hrowA : ∀ j : Fin (m + 1), rotated h m m (j : ℕ) = 0 := by
    intro j
    rcases Nat.lt_or_ge (j : ℕ) m with hj | hj
    · exact rotated_eq_zero_of_lt h hh m m (j : ℕ) hj hj
    · have hjm : (j : ℕ) = m := by omega
      rw [hjm]; exact ha
  have hrowB : ∀ j : Fin (m + 1), rotated h m (m + 1) (j : ℕ) = 0 := by
    intro j
    rcases Nat.lt_or_ge (j : ℕ) m with hj | hj
    · exact rotated_eq_zero_of_lt h hh m (m + 1) (j : ℕ) hj (by omega)
    · have hjm : (j : ℕ) = m := by omega
      rw [hjm]; exact hb
  have hrowC : ∀ j : Fin (m + 1), rotated h (m + 1) m (j : ℕ) = 0 := fun j =>
    rotated_succ_row_eq_zero_of_givensRho_eq_zero h hh hρm (by omega)
  have hgvecm : gvec h β m = 0 := gvec_eq_zero_of_givensRho_eq_zero h hρm β
  have hsub : ∀ i j : ℕ, i < m → rotated h (m + 1) i j = rotated h m i j := by
    intro i j hi
    rw [rotated_succ_apply, ite_eq_right (by omega), ite_eq_right (by omega)]
  have hQ : (givensQAux h m (m + 1)).mulVec
      (firstVec β (m + 2) - (hessenbergOf h (m + 1)).mulVec y) =
      fun i : Fin (m + 2) => gvecTrunc h β m (i : ℕ) -
        (hessenbergOf (rotated h m) (m + 1)).mulVec y i := by
    rw [Matrix.mulVec_sub, givensQAux_mulVec_firstVec h β (m + 1) m (by omega),
      Matrix.mulVec_mulVec, givensQAux_mul_hessenbergOf h (by omega)]
    rfl
  rw [← Matrix.norm_toLp_mulVec_of_mem_unitaryGroup
      (givensQAux_mem_unitaryGroup h (show m ≤ m + 1 by omega) hρ), hQ]
  refine norm_sq_split_aux _ _ _ ?_ ?_
  · have hz : (hessenbergOf (rotated h m) (m + 1)).mulVec y (Fin.last (m + 1)) = 0 := by
      simp only [Matrix.mulVec, dotProduct, hessenbergOf, Matrix.of_apply, Fin.val_last]
      exact Finset.sum_eq_zero fun j _ => by rw [hrowB j, zero_mul]
    rw [hz, sub_zero, Fin.val_last, gvecTrunc_succ]
  · intro i
    rcases Nat.lt_or_ge (i : ℕ) m with hi | hi
    · have hrot : (hessenbergOf (rotated h m) (m + 1)).mulVec y i.castSucc =
          (hessenbergSqOf (rotated h (m + 1)) (m + 1)).mulVec y i := by
        simp only [Matrix.mulVec, dotProduct, hessenbergOf, hessenbergSqOf, Matrix.of_apply,
          Fin.val_castSucc]
        exact Finset.sum_congr rfl fun j _ => by rw [hsub (i : ℕ) (j : ℕ) hi]
      rw [Fin.val_castSucc, gvecTrunc_of_lt h β hi, hrot, ite_eq_right (by omega), add_zero]
      rfl
    · have him : (i : ℕ) = m := by omega
      have hz1 : (hessenbergOf (rotated h m) (m + 1)).mulVec y i.castSucc = 0 := by
        simp only [Matrix.mulVec, dotProduct, hessenbergOf, Matrix.of_apply]
        exact Finset.sum_eq_zero fun j _ => by
          rw [show ((i.castSucc : Fin (m + 2)) : ℕ) = m from him, hrowA j, zero_mul]
      have hz2 : (hessenbergSqOf (rotated h (m + 1)) (m + 1)).mulVec y i = 0 := by
        simp only [Matrix.mulVec, dotProduct, hessenbergSqOf, Matrix.of_apply]
        exact Finset.sum_eq_zero fun j _ => by rw [him, hrowC j, zero_mul]
      rw [show ((i.castSucc : Fin (m + 2)) : ℕ) = m from him, hz1, gvecTrunc_self, sub_zero,
        ite_eq_left him]
      have hG : ((fun i : Fin (m + 1) => gvec h β (i : ℕ)) -
          (hessenbergSqOf (rotated h (m + 1)) (m + 1)).mulVec y) i = 0 := by
        rw [Pi.sub_apply, hz2, him, hgvecm, sub_zero]
      rw [hG, norm_zero]
      ring

/-! ### The square system $H_{m+1} y = v$ in rotated coordinates -/

/-- Let $v \in \mathbb{K}^{m+2}$ vanish outside the index $m + 1$. Then the entries $i \le m$ of
$Q^{(m)}_{m+1} v$ vanish, because the first $m$ rotations do not change column $m + 1$. -/
theorem givensQAux_mulVec_of_last {m : ℕ} (v : Fin (m + 2) → 𝕜)
    (hv : ∀ l : Fin (m + 2), (l : ℕ) ≠ m + 1 → v l = 0) (i : Fin (m + 1)) :
    (givensQAux h m (m + 1)).mulVec v i.castSucc = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : (l : ℕ) = m + 1
  · have hi := i.isLt
    have hne : i.castSucc ≠ l := by
      intro hc
      have h1 : (i : ℕ) = (l : ℕ) := by rw [← hc]; rfl
      omega
    rw [givensQAux_apply_of_lt h m (m + 1) i.castSucc l (by omega), ite_eq_right hne, zero_mul]
  · rw [hv l hl, mul_zero]

/-- For every $y \in \mathbb{K}^{m+1}$ and $i \le m$, the entry $i$ of $R' y$, where $R'$ is the
$(m + 1) \times (m + 1)$ matrix of $R^{(m)}$, equals the entry $i$ of
$Q^{(m)}_{m+1} \bar{H}_{m+1} y$. Thus the first $m$ rotations carry the square system
$H_{m+1} y$ to $R' y$. -/
theorem hessenbergSqOf_rotated_mulVec {m : ℕ} (y : Fin (m + 1) → 𝕜) (i : Fin (m + 1)) :
    (hessenbergSqOf (rotated h m) (m + 1)).mulVec y i =
      (givensQAux h m (m + 1)).mulVec ((hessenbergOf h (m + 1)).mulVec y) i.castSucc := by
  rw [Matrix.mulVec_mulVec, givensQAux_mul_hessenbergOf h (by omega)]
  rfl

/-- If $H_{m+1} y = 0$, then $R' y = 0$, where $R'$ is the $(m + 1) \times (m + 1)$ matrix of
$R^{(m)}$. The extra row of $\bar{H}_{m+1}$ is invisible to the first $m + 1$ rotated equations. -/
theorem mulVec_rotated_eq_zero_of_mulVec_eq_zero {m : ℕ} {y : Fin (m + 1) → 𝕜}
    (hy : (hessenbergSqOf h (m + 1)).mulVec y = 0) :
    (hessenbergSqOf (rotated h m) (m + 1)).mulVec y = 0 := by
  funext i
  rw [hessenbergSqOf_rotated_mulVec h y i]
  refine givensQAux_mulVec_of_last h _ (fun l hl => ?_) i
  have hlm : (l : ℕ) < m + 1 := by have := l.isLt; omega
  have e : (hessenbergOf h (m + 1)).mulVec y l =
      (hessenbergSqOf h (m + 1)).mulVec y ⟨(l : ℕ), hlm⟩ := rfl
  rw [e, hy]
  rfl

/-- Let $h$ be upper Hessenberg, and let $y \in \mathbb{K}^{m+1}$ satisfy $H_{m+1} y = \beta e_1$.
Then every entry of the rectangular residual $\beta e_1 - \bar{H}_{m+1} y$ is $0$ except the
entry at the index $m + 1$, which is $-h_{m+1,m} \, y_m$. This is Proposition 6.7 of
[saad2003iterative] in coordinates. -/
theorem firstVec_sub_mulVec_apply_of_mulVec_eq (hh : Matrix.IsUpperHessenberg (n := ℕ) h) (β : 𝕜)
    {m : ℕ} {y : Fin (m + 1) → 𝕜}
    (hy : (hessenbergSqOf h (m + 1)).mulVec y = firstVec β (m + 1)) (l : Fin (m + 2)) :
    (firstVec β (m + 2) - (hessenbergOf h (m + 1)).mulVec y) l =
      if (l : ℕ) = m + 1 then -(h (m + 1) m * y ⟨m, Nat.lt_succ_self m⟩) else 0 := by
  by_cases hl : (l : ℕ) = m + 1
  · have hfv : firstVec β (m + 2) l = 0 := by simp [firstVec, hl]
    have hmv : (hessenbergOf h (m + 1)).mulVec y l = h (m + 1) m * y ⟨m, Nat.lt_succ_self m⟩ := by
      simp only [Matrix.mulVec, dotProduct, hessenbergOf, Matrix.of_apply, hl]
      rw [Finset.sum_eq_single (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))]
      · intro j _ hj
        have hjm : (j : ℕ) + 1 < m + 1 := by
          have := j.isLt
          have : (j : ℕ) ≠ m := fun hc => hj (Fin.ext hc)
          omega
        rw [hh.eq_zero_of_add_one_lt (m + 1) (j : ℕ) (by omega), zero_mul]
      · intro hc; exact absurd (Finset.mem_univ _) hc
    rw [Pi.sub_apply, hfv, hmv, ite_eq_left hl, zero_sub]
  · have hlm : (l : ℕ) < m + 1 := by have := l.isLt; omega
    have e1 : firstVec β (m + 2) l = firstVec β (m + 1) ⟨(l : ℕ), hlm⟩ := rfl
    have e2 : (hessenbergOf h (m + 1)).mulVec y l =
        (hessenbergSqOf h (m + 1)).mulVec y ⟨(l : ℕ), hlm⟩ := rfl
    rw [Pi.sub_apply, e1, e2, hy, sub_self, ite_eq_right hl]

/-- Let $h$ be upper Hessenberg, and let $y \in \mathbb{K}^{m+1}$ satisfy $H_{m+1} y = \beta e_1$.
Then
$$\|\beta e_1 - \bar{H}_{m+1} y\|_2 = |h_{m+1,m} \, y_m|.$$
This is the Galerkin residual in coordinates, (6.18) of [saad2003iterative]. -/
theorem norm_firstVec_sub_mulVec_of_mulVec_eq (hh : Matrix.IsUpperHessenberg (n := ℕ) h) (β : 𝕜)
    {m : ℕ} {y : Fin (m + 1) → 𝕜}
    (hy : (hessenbergSqOf h (m + 1)).mulVec y = firstVec β (m + 1)) :
    ‖(WithLp.toLp 2 (firstVec β (m + 2) - (hessenbergOf h (m + 1)).mulVec y) :
        EuclideanSpace 𝕜 (Fin (m + 2)))‖ = ‖h (m + 1) m * y ⟨m, Nat.lt_succ_self m⟩‖ := by
  have hsq : ‖(WithLp.toLp 2 (firstVec β (m + 2) - (hessenbergOf h (m + 1)).mulVec y) :
      EuclideanSpace 𝕜 (Fin (m + 2)))‖ ^ 2 =
      ‖h (m + 1) m * y ⟨m, Nat.lt_succ_self m⟩‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only
    rw [Finset.sum_eq_single (Fin.last (m + 1))]
    · rw [firstVec_sub_mulVec_apply_of_mulVec_eq h hh β hy, ite_eq_left (by simp), norm_neg]
    · intro l _ hl
      have hl' : (l : ℕ) ≠ m + 1 := fun hc => hl (Fin.ext (by simpa using hc))
      rw [firstVec_sub_mulVec_apply_of_mulVec_eq h hh β hy, ite_eq_right hl', norm_zero]
      norm_num
    · intro hc; exact absurd (Finset.mem_univ _) hc
  have hs := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hs

/-- Let $h$ be upper Hessenberg, and let $y \in \mathbb{K}^{m+1}$ satisfy $H_{m+1} y = \beta e_1$.
Then the last rotated equation reads $R^{(m)}_{mm} \, y_m = \gamma_m$ ([saad2003iterative],
(6.43)). -/
theorem rotated_self_mul_eq_gamma (hh : Matrix.IsUpperHessenberg (n := ℕ) h) (β : 𝕜) {m : ℕ}
    {y : Fin (m + 1) → 𝕜}
    (hy : (hessenbergSqOf h (m + 1)).mulVec y = firstVec β (m + 1)) :
    rotated h m m m * y ⟨m, Nat.lt_succ_self m⟩ = gamma h β m := by
  have hd : ∀ l : Fin (m + 2), (l : ℕ) ≠ m + 1 →
      (firstVec β (m + 2) - (hessenbergOf h (m + 1)).mulVec y) l = 0 := fun l hl => by
    rw [firstVec_sub_mulVec_apply_of_mulVec_eq h hh β hy, ite_eq_right hl]
  have hlhs : (hessenbergSqOf (rotated h m) (m + 1)).mulVec y ⟨m, Nat.lt_succ_self m⟩ =
      rotated h m m m * y ⟨m, Nat.lt_succ_self m⟩ := by
    simp only [Matrix.mulVec, dotProduct, hessenbergSqOf, Matrix.of_apply]
    rw [Finset.sum_eq_single (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))]
    · intro j _ hj
      have hjm : (j : ℕ) < m := by
        have := j.isLt
        have : (j : ℕ) ≠ m := fun hc => hj (Fin.ext hc)
        omega
      rw [rotated_last_row h hh m (j : ℕ) hjm, zero_mul]
    · intro hc; exact absurd (Finset.mem_univ _) hc
  have hsub : (hessenbergOf h (m + 1)).mulVec y =
      firstVec β (m + 2) - (firstVec β (m + 2) - (hessenbergOf h (m + 1)).mulVec y) :=
    (sub_sub_cancel _ _).symm
  rw [← hlhs, hessenbergSqOf_rotated_mulVec h y ⟨m, Nat.lt_succ_self m⟩, hsub, Matrix.mulVec_sub,
    Pi.sub_apply, givensQAux_mulVec_firstVec h β (m + 1) m (by omega),
    givensQAux_mulVec_of_last h _ hd ⟨m, Nat.lt_succ_self m⟩, sub_zero]
  exact gvecTrunc_self h β m

/-! ### The transposed system $\bar{H}_m^H y = c$: the minimum-norm solution -/

open scoped Matrix in
/-- Let $h$ be upper Hessenberg. For every $z \in \mathbb{K}^{m+1}$,
$\bar{R}_m^H z = R_m^H (z_0, \dots, z_{m-1})$: the last row of $\bar{R}_m$ vanishes, so
$\bar{R}_m^H z$ does not depend on $z_m$. -/
theorem conjTranspose_hessenbergOf_rotated_mulVec (hh : Matrix.IsUpperHessenberg (n := ℕ) h) (m : ℕ)
    (z : Fin (m + 1) → 𝕜) :
    (hessenbergOf (rotated h m) m)ᴴ *ᵥ z =
      (hessenbergSqOf (rotated h m) m)ᴴ *ᵥ fun i => z i.castSucc := by
  funext j
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Fin.sum_univ_castSucc,
    hessenbergOf, hessenbergSqOf, Matrix.of_apply, Fin.val_last, Fin.val_castSucc]
  rw [rotated_last_row h hh m j j.isLt, star_zero, zero_mul, add_zero]

open scoped Matrix in
/-- **The minimum-norm solution of $\bar{H}_m^H y = c$.** Let $h$ be upper Hessenberg, let
$\rho_l \neq 0$ for every $l < m$, let $c \in \mathbb{K}^m$, and let $w \in \mathbb{K}^m$
satisfy $R_m^H w = c$. Then $y = Q_m^H (w, 0)$ solves the underdetermined system
$\bar{H}_m^H y = c$, and $\|y\|_2 \le \|y'\|_2$ for every solution $y'$. This is the solve of
SYMMLQ ([golub2013matrix], §11.4.1).

The transposed Givens factorization is $\bar{H}_m^H Q_m^H = \bar{R}_m^H = [R_m^H \mid 0]$
(`Krylov.givensQ_mul_hessenbergOf`). Since $R_m^H$ is nonsingular, every solution is
$Q_m^H (w, t)$ for some $t$, and $Q_m$ is unitary. -/
theorem conjTranspose_hessenbergOf_mulVec_givensQ_snoc (hh : Matrix.IsUpperHessenberg (n := ℕ) h)
    {m : ℕ} (hρ : ∀ l < m, givensRho h l ≠ 0) {c w : Fin m → 𝕜}
    (hw : (hessenbergSqOf (rotated h m) m)ᴴ *ᵥ w = c) :
    (hessenbergOf h m)ᴴ *ᵥ ((givensQ h m)ᴴ *ᵥ Fin.snoc w 0) = c ∧
      ∀ y : Fin (m + 1) → 𝕜, (hessenbergOf h m)ᴴ *ᵥ y = c →
        ‖(WithLp.toLp 2 ((givensQ h m)ᴴ *ᵥ Fin.snoc w 0) : EuclideanSpace 𝕜 (Fin (m + 1)))‖ ≤
          ‖(WithLp.toLp 2 y : EuclideanSpace 𝕜 (Fin (m + 1)))‖ := by
  have hQ := givensQ_mem_unitaryGroup h m hρ
  have hQs : (givensQ h m)ᴴ = star (givensQ h m) := (Matrix.star_eq_conjTranspose _).symm
  have hQt : (givensQ h m)ᴴ ∈ Matrix.unitaryGroup (Fin (m + 1)) 𝕜 := hQs ▸ Unitary.star_mem hQ
  have hQQ : (givensQ h m)ᴴ * givensQ h m = 1 := hQs ▸ Matrix.mem_unitaryGroup_iff'.1 hQ
  have hRu : IsUnit (hessenbergSqOf (rotated h m) m)ᴴ :=
    (Matrix.isUnit_conjTranspose _).2 (isUnit_hessenbergSqOf_rotated_self h hh hρ)
  have hkey : ∀ z : Fin (m + 1) → 𝕜, (hessenbergOf h m)ᴴ *ᵥ ((givensQ h m)ᴴ *ᵥ z) =
      (hessenbergSqOf (rotated h m) m)ᴴ *ᵥ fun i => z i.castSucc := fun z => by
    rw [Matrix.mulVec_mulVec, ← Matrix.conjTranspose_mul, givensQ_mul_hessenbergOf,
      conjTranspose_hessenbergOf_rotated_mulVec h hh]
  -- the norm of `z ∈ 𝕜^{m+1}` splits off its last entry
  have hsplit : ∀ z : Fin (m + 1) → 𝕜,
      ‖(WithLp.toLp 2 z : EuclideanSpace 𝕜 (Fin (m + 1)))‖ ^ 2 =
      ‖(WithLp.toLp 2 (fun i : Fin m => z i.castSucc) : EuclideanSpace 𝕜 (Fin m))‖ ^ 2 +
        ‖z (Fin.last m)‖ ^ 2 := fun z => by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  refine ⟨?_, fun y hy => ?_⟩
  · rw [hkey]
    simpa using hw
  · have hyz : y = (givensQ h m)ᴴ *ᵥ (givensQ h m *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, hQQ, Matrix.one_mulVec]
    have hzw : (fun i : Fin m => (givensQ h m *ᵥ y) i.castSucc) = w := by
      refine (Matrix.mulVec_injective_iff_isUnit.2 hRu) ?_
      rw [← hkey, ← hyz, hy, hw]
    rw [hyz, Matrix.norm_toLp_mulVec_of_mem_unitaryGroup hQt,
      Matrix.norm_toLp_mulVec_of_mem_unitaryGroup hQt]
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [hsplit, hsplit (givensQ h m *ᵥ y), hzw]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, norm_zero]
    nlinarith [sq_nonneg ‖(givensQ h m *ᵥ y) (Fin.last m)‖]

end Givens

section GivensArnoldi

/-!
### Identifications for the Arnoldi coefficients

Here the coefficient array is that of the Arnoldi process for $(A, r_0)$ with $r_0 = b - A x_0$, and
$\beta = \|r_0\|$.
-/

variable {A : E →ₗ[𝕜] E} {b x₀ : E} [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]

/-- Let $r_0 = b - A x_0$ have a finite-dimensional Krylov space. If $k + 1$ is less than the grade
of $r_0$, then $\rho_k \neq 0$ for the Arnoldi coefficients, so rotation $k$ is unitary. The
reason is that the subdiagonal Arnoldi coefficient $h_{k+1,k}$ is nonzero there. -/
theorem givensRho_arnoldi_ne_zero {k : ℕ} (hk : k + 1 < grade A (b - A x₀)) :
    givensRho (Arnoldi.coeff A (b - A x₀)) k ≠ 0 := by
  intro h0
  have h1 := (rotated_eq_zero_of_givensRho_eq_zero (Arnoldi.coeff A (b - A x₀)) h0).2
  rw [rotated_eq_of_le (Arnoldi.coeff A (b - A x₀)) k (k + 1) k le_rfl] at h1
  exact absurd ((Arnoldi.coeff_succ_self_eq_zero_iff A (b - A x₀) k).mp h1) (by omega)

/-- Let $r_0 = b - A x_0$ have a finite-dimensional Krylov space and $\beta = \|r_0\|$. If $m$ is
less than the grade of $r_0$, then $\gamma_m \neq 0$ for the Arnoldi coefficients, because every
$s_k$ with $k < m$ and the initial residual are nonzero ([saad2003iterative], (6.47)). -/
theorem gamma_arnoldi_ne_zero {m : ℕ} (hm : m < grade A (b - A x₀)) :
    gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) m ≠ 0 := by
  have hr : b - A x₀ ≠ 0 := by
    intro hc
    rw [hc, grade_zero] at hm
    omega
  rw [← norm_ne_zero_iff, norm_gamma_eq_prod]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k hk => ?_) ?_
  · rw [Finset.mem_range] at hk
    rw [norm_ne_zero_iff, givensS, div_ne_zero_iff]
    refine ⟨?_, ?_⟩
    · rw [rotated_eq_of_le (Arnoldi.coeff A (b - A x₀)) k (k + 1) k le_rfl]
      exact fun hc =>
        absurd ((Arnoldi.coeff_succ_self_eq_zero_iff A (b - A x₀) k).mp hc) (by omega)
    · simpa using givensRho_arnoldi_ne_zero (show k + 1 < grade A (b - A x₀) by omega)
  · simp only [RCLike.norm_ofReal, abs_norm, ne_eq, norm_eq_zero]
    exact hr

/-- If $P^2 = D + G^2$, $Q^2 = G^2$, $P \le Q$ and $P, Q, D, G \ge 0$, then $D = 0$ and $P = G$. -/
private theorem eq_of_min_split {P Q D G : ℝ} (hP2 : P ^ 2 = D + G ^ 2) (hQ2 : Q ^ 2 = G ^ 2)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hD : 0 ≤ D) (hG : 0 ≤ G) (hPQ : P ≤ Q) : D = 0 ∧ P = G := by
  have hD0 : D = 0 := le_antisymm (by nlinarith) hD
  refine ⟨hD0, ?_⟩
  rw [hD0, zero_add] at hP2
  nlinarith

/-- When no rotation degenerates before step $m$, a minimal-residual iterate $x$ has residual norm
$|\gamma_m|$, and $x = x_0 + \sum_j y_j v_j$ with $R_m y = (g_0, \dots, g_{m-1})$
([saad2003iterative], (6.41)–(6.43)). -/
private theorem minres_rotated_of_givensRho_ne_zero {m : ℕ} (hm : m ≤ grade A (b - A x₀))
    (hρ : ∀ k < m, givensRho (Arnoldi.coeff A (b - A x₀)) k ≠ 0) {x : E}
    (hx : IsMinResidualIterate A b x₀ m x) :
    ‖b - A x‖ = ‖gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) m‖ ∧
      ∃ y : Fin m → 𝕜,
        (hessenbergSqOf (rotated (Arnoldi.coeff A (b - A x₀)) m) m).mulVec y =
            (fun i : Fin m => gvec (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) (i : ℕ)) ∧
          x = x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j := by
  have hh := Arnoldi.isUpperHessenberg_coeff A (b - A x₀)
  obtain ⟨y, hy⟩ := (mem_subspace_iff_exists_coeffs A (b - A x₀) m _).mp hx.mem
  have hxe : x = x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j := by rw [← hy]; abel
  rw [hxe] at hx
  have hmin := (isMinResidualIterate_iff_isMinOn hm y).mp hx
  rw [isMinOn_iff] at hmin
  obtain ⟨z, hz⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr
    (isUnit_hessenbergSqOf_rotated_self (Arnoldi.coeff A (b - A x₀)) hh hρ)
    (fun i : Fin m => gvec (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) (i : ℕ))
  have hsplit : ∀ w : Fin m → 𝕜,
      ‖(WithLp.toLp 2 (firstVec (‖b - A x₀‖ : 𝕜) (m + 1) -
          (Arnoldi.hessenberg A (b - A x₀) m).mulVec w) :
            EuclideanSpace 𝕜 (Fin (m + 1)))‖ ^ 2 =
        ‖(WithLp.toLp 2 ((fun i : Fin m => gvec (Arnoldi.coeff A (b - A x₀))
              (‖b - A x₀‖ : 𝕜) (i : ℕ)) -
            (hessenbergSqOf (rotated (Arnoldi.coeff A (b - A x₀)) m) m).mulVec w) :
              EuclideanSpace 𝕜 (Fin m))‖ ^ 2 +
          ‖gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) m‖ ^ 2 := fun w => by
    rw [Arnoldi.hessenberg_eq]
    exact norm_sq_firstVec_sub_mulVec_eq _ hh hρ _ w
  have hz2 : ‖(WithLp.toLp 2 (firstVec (‖b - A x₀‖ : 𝕜) (m + 1) -
        (Arnoldi.hessenberg A (b - A x₀) m).mulVec z) : EuclideanSpace 𝕜 (Fin (m + 1)))‖ ^ 2 =
      ‖gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) m‖ ^ 2 := by
    rw [hsplit z, hz, sub_self]
    simp
  obtain ⟨hD0, hPG⟩ := eq_of_min_split (hsplit y) hz2 (norm_nonneg _) (norm_nonneg _)
    (sq_nonneg _) (norm_nonneg _) (hmin z (Set.mem_univ z))
  have hvz := (pow_eq_zero_iff two_ne_zero).mp hD0
  rw [norm_eq_zero, WithLp.toLp_eq_zero] at hvz
  refine ⟨?_, y, (sub_eq_zero.mp hvz).symm, hxe⟩
  rw [hxe, norm_residual_eq_norm_firstVec_sub_mulVec hm y]
  exact hPG

/-- When some rotation before step $m$ degenerates, a minimal-residual iterate is
$x_0 + \sum_j y_j v_j$ with $R_m y = (g_0, \dots, g_{m-1})$; this is the breakdown case of
`Krylov.IsMinResidualIterate.exists_mulVec_rotated_eq`. -/
private theorem minres_rotated_of_breakdown {m : ℕ} (hm : m ≤ grade A (b - A x₀))
    (hρ : ¬∀ k < m, givensRho (Arnoldi.coeff A (b - A x₀)) k ≠ 0) {x : E}
    (hx : IsMinResidualIterate A b x₀ m x) :
    ∃ y : Fin m → 𝕜, (hessenbergSqOf (rotated (Arnoldi.coeff A (b - A x₀)) m) m).mulVec y =
        (fun i : Fin m => gvec (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) i) ∧
      x = x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j := by
  have hh := Arnoldi.isUpperHessenberg_coeff A (b - A x₀)
  obtain ⟨k, hk, hρk⟩ : ∃ k, k < m ∧ givensRho (Arnoldi.coeff A (b - A x₀)) k = 0 := by
    by_contra hcon
    exact hρ fun k hkm hc => hcon ⟨k, hkm, hc⟩
  -- a degenerate rotation forces `m = k + 1 = grade`
  have hb0 : rotated (Arnoldi.coeff A (b - A x₀)) k (k + 1) k = 0 :=
    (rotated_eq_zero_of_givensRho_eq_zero _ hρk).2
  rw [rotated_eq_of_le (Arnoldi.coeff A (b - A x₀)) k (k + 1) k le_rfl] at hb0
  have hgr : grade A (b - A x₀) ≤ k + 1 :=
    (Arnoldi.coeff_succ_self_eq_zero_iff A (b - A x₀) k).mp hb0
  have hmk : m = k + 1 := by omega
  subst hmk
  have hρlt : ∀ j < k, givensRho (Arnoldi.coeff A (b - A x₀)) j ≠ 0 :=
    fun j hj => givensRho_arnoldi_ne_zero (by omega)
  obtain ⟨y, hy⟩ := (mem_subspace_iff_exists_coeffs A (b - A x₀) (k + 1) _).mp hx.mem
  have hxe : x = x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j := by rw [← hy]; abel
  rw [hxe] at hx
  have hmin := (isMinResidualIterate_iff_isMinOn hm y).mp hx
  rw [isMinOn_iff] at hmin
  -- the leading `k × k` triangular block is nonsingular; pad its solution by a zero
  obtain ⟨y', hy'⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr
    (isUnit_hessenbergSqOf_rotated_self (Arnoldi.coeff A (b - A x₀)) hh hρlt)
    (fun i : Fin k => gvec (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) (i : ℕ))
  obtain ⟨z, hzc, hzl⟩ : ∃ z : Fin (k + 1) → 𝕜,
      (∀ j : Fin k, z j.castSucc = y' j) ∧ z (Fin.last k) = 0 :=
    ⟨Fin.snoc y' 0, fun j => by simp, by simp⟩
  have hzsol : (hessenbergSqOf (rotated (Arnoldi.coeff A (b - A x₀)) (k + 1)) (k + 1)).mulVec z =
      fun i : Fin (k + 1) => gvec (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) (i : ℕ) := by
    funext i
    rcases Nat.lt_or_ge (i : ℕ) k with hi | hi
    · have e1 : ∑ j : Fin (k + 1), rotated (Arnoldi.coeff A (b - A x₀)) (k + 1)
            (i : ℕ) (j : ℕ) * z j =
          ∑ j : Fin (k + 1), rotated (Arnoldi.coeff A (b - A x₀)) k (i : ℕ) (j : ℕ) * z j :=
        Finset.sum_congr rfl fun j _ => by
          rw [rotated_succ_apply, ite_eq_right (by omega), ite_eq_right (by omega)]
      have e2 : ∑ j : Fin (k + 1), rotated (Arnoldi.coeff A (b - A x₀)) k (i : ℕ) (j : ℕ) * z j =
          ∑ j : Fin k, rotated (Arnoldi.coeff A (b - A x₀)) k (i : ℕ) (j : ℕ) * y' j := by
        rw [Fin.sum_univ_castSucc, hzl, mul_zero, add_zero]
        exact Finset.sum_congr rfl fun j _ => by rw [hzc j, Fin.val_castSucc]
      have e3 : ∑ j : Fin k, rotated (Arnoldi.coeff A (b - A x₀)) k (i : ℕ) (j : ℕ) * y' j =
          gvec (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) (i : ℕ) := by
        have h5 := congrFun hy' ⟨(i : ℕ), hi⟩
        simpa [Matrix.mulVec, dotProduct, hessenbergSqOf] using h5
      simp only [Matrix.mulVec, dotProduct, hessenbergSqOf, Matrix.of_apply]
      rw [e1, e2, e3]
    · have hik : (i : ℕ) = k := by omega
      simp only [Matrix.mulVec, dotProduct, hessenbergSqOf, Matrix.of_apply, hik,
        gvec_eq_zero_of_givensRho_eq_zero (Arnoldi.coeff A (b - A x₀)) hρk]
      exact Finset.sum_eq_zero fun j _ => by
        rw [rotated_succ_row_eq_zero_of_givensRho_eq_zero (Arnoldi.coeff A (b - A x₀)) hh hρk
          (by omega), zero_mul]
  have hsplit : ∀ w : Fin (k + 1) → 𝕜,
      ‖(WithLp.toLp 2 (firstVec (‖b - A x₀‖ : 𝕜) (k + 1 + 1) -
          (Arnoldi.hessenberg A (b - A x₀) (k + 1)).mulVec w) :
            EuclideanSpace 𝕜 (Fin (k + 1 + 1)))‖ ^ 2 =
        ‖(WithLp.toLp 2 ((fun i : Fin (k + 1) => gvec (Arnoldi.coeff A (b - A x₀))
              (‖b - A x₀‖ : 𝕜) (i : ℕ)) -
            (hessenbergSqOf (rotated (Arnoldi.coeff A (b - A x₀)) (k + 1)) (k + 1)).mulVec w) :
              EuclideanSpace 𝕜 (Fin (k + 1)))‖ ^ 2 +
          ‖gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) k‖ ^ 2 := fun w => by
    rw [Arnoldi.hessenberg_eq]
    exact norm_sq_firstVec_sub_mulVec_eq_of_breakdown _ hh hρlt hρk _ w
  have hz2 : ‖(WithLp.toLp 2 (firstVec (‖b - A x₀‖ : 𝕜) (k + 1 + 1) -
        (Arnoldi.hessenberg A (b - A x₀) (k + 1)).mulVec z) :
          EuclideanSpace 𝕜 (Fin (k + 1 + 1)))‖ ^ 2 =
      ‖gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) k‖ ^ 2 := by
    rw [hsplit, hzsol, sub_self]
    simp
  obtain ⟨hD0, -⟩ := eq_of_min_split (hsplit y) hz2 (norm_nonneg _) (norm_nonneg _)
    (sq_nonneg _) (norm_nonneg _) (hmin _ (Set.mem_univ _))
  have hvz := (pow_eq_zero_iff two_ne_zero).mp hD0
  rw [norm_eq_zero, WithLp.toLp_eq_zero] at hvz
  exact ⟨y, (sub_eq_zero.mp hvz).symm, hxe⟩

/-- Let $r_0 = b - A x_0$ have a finite-dimensional Krylov space, let $\beta = \|r_0\|$, and let $m$
be less than the grade of $r_0$. If $x$ is a minimal-residual iterate at step $m$, then
$$\|b - Ax\| = |\gamma_m|,$$
where $\gamma_m$ is computed from the Arnoldi coefficients of $(A, r_0)$. This is (6.42) and
Proposition 6.9(3) of [saad2003iterative].

The hypothesis that $m$ is less than the grade cannot be weakened to $m$ at most the grade: at
$m$ equal to the grade the statement is false. Take $\mathbb{K} = E = \mathbb{R}$, $A = 0$,
$b = 1$ and $x_0 = 0$. Then $r_0 = 1$, the full Krylov space is $\mathbb{R}$, so the grade is
$1$, and $m = 1$. Every $x$ is a minimal-residual iterate with $\|b - Ax\| = 1$, while
$h_{00} = \langle v_0, A v_0 \rangle = 0$ and $h_{10} = 0$ give $\rho_0 = 0$, hence
$s_0 = 0 / 0 = 0$ and $\gamma_1 = -s_0 \gamma_0 = 0$. For $m$ less than the grade,
$h_{k+1,k} \neq 0$ and hence $\rho_k \neq 0$ for every $k < m$, which makes $Q_m$ unitary and
$R_m$ nonsingular. The case of $m$ equal to the grade is
`Krylov.IsMinResidualIterate.norm_residual_eq_norm_gamma_of_givensRho_ne_zero`, which assumes
$\rho_k \neq 0$ directly. -/
theorem IsMinResidualIterate.norm_residual_eq_norm_gamma {m : ℕ} (hm : m < grade A (b - A x₀))
    {x : E} (hx : IsMinResidualIterate A b x₀ m x) :
    ‖b - A x‖ = ‖gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) m‖ :=
  (minres_rotated_of_givensRho_ne_zero hm.le
    (fun k hk => givensRho_arnoldi_ne_zero (by omega)) hx).1

/-- Let $r_0 = b - A x_0$ have a finite-dimensional Krylov space, let $\beta = \|r_0\|$, and let $m$
be at most the grade of $r_0$. If $\rho_k \neq 0$ for every $k < m$ and $x$ is a
minimal-residual iterate at step $m$, then $\|b - Ax\| = |\gamma_m|$. This is (6.42) of
[saad2003iterative], including the boundary case of $m$ equal to the grade.

`Krylov.IsMinResidualIterate.norm_residual_eq_norm_gamma` derives the hypothesis on $\rho_k$
from $m$ less than the grade. -/
theorem IsMinResidualIterate.norm_residual_eq_norm_gamma_of_givensRho_ne_zero {m : ℕ}
    (hm : m ≤ grade A (b - A x₀))
    (hρ : ∀ k < m, givensRho (Arnoldi.coeff A (b - A x₀)) k ≠ 0) {x : E}
    (hx : IsMinResidualIterate A b x₀ m x) :
    ‖b - A x‖ = ‖gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) m‖ :=
  (minres_rotated_of_givensRho_ne_zero hm hρ hx).1

/-- Let $r_0 = b - A x_0$ have a finite-dimensional Krylov space, let $\beta = \|r_0\|$, and let $m$
be at most the grade of $r_0$. If $x$ is a minimal-residual iterate at step $m$, then
$x = x_0 + \sum_{j<m} y_j v_j$ for some $y \in \mathbb{K}^m$ with
$$R_m y = (g_0, \dots, g_{m-1}).$$
This is (6.43) and (6.30) of [saad2003iterative].

Unlike `Krylov.IsMinResidualIterate.norm_residual_eq_norm_gamma`, this holds also for $m$ equal
to the grade. There the last rotation may degenerate, $\rho_{m-1} = 0$, and then $R_m$ is
singular. But its last row and the last entry $g_{m-1} = \bar{c}_{m-1} \gamma_{m-1}$ of the
right-hand side both vanish, so the system is still consistent and the coordinates of the
minimal-residual iterate solve it. -/
theorem IsMinResidualIterate.exists_mulVec_rotated_eq {m : ℕ} (hm : m ≤ grade A (b - A x₀)) {x : E}
    (hx : IsMinResidualIterate A b x₀ m x) :
    ∃ y : Fin m → 𝕜, (hessenbergSqOf (rotated (Arnoldi.coeff A (b - A x₀)) m) m).mulVec y =
        (fun i : Fin m => gvec (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) i) ∧
      x = x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j := by
  by_cases hρ : ∀ k < m, givensRho (Arnoldi.coeff A (b - A x₀)) k ≠ 0
  · exact (minres_rotated_of_givensRho_ne_zero hm hρ hx).2
  · exact minres_rotated_of_breakdown hm hρ hx

omit [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] in
/-- Let $r_0 = b - A x_0$ and $\beta = \|r_0\|$. If $y \in \mathbb{K}^m$ solves the triangular
system $R_m y = (g_0, \dots, g_{m-1})$ for the Arnoldi coefficients, then the rotated residual
is carried by its last entry alone:
$$Q_m (\beta e_1 - \bar{H}_m y) = \gamma_m e_{m+1}.$$
The first $m$ entries vanish because $y$ solves the triangular system, and the last one is
$\gamma_m$ because the last row of $\bar{R}_m$ is zero. No finite dimension is needed. -/
theorem givensQ_mulVec_firstVec_sub_mulVec {m : ℕ} {y : Fin m → 𝕜}
    (hy : (hessenbergSqOf (rotated (Arnoldi.coeff A (b - A x₀)) m) m).mulVec y =
      fun i : Fin m => gvec (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) i) :
    (givensQ (Arnoldi.coeff A (b - A x₀)) m).mulVec
        (firstVec (‖b - A x₀‖ : 𝕜) (m + 1) -
          (Arnoldi.hessenberg A (b - A x₀) m).mulVec y) =
      fun i : Fin (m + 1) =>
        if (i : ℕ) = m then gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) m else 0 := by
  set h := Arnoldi.coeff A (b - A x₀) with hh
  set β : 𝕜 := ((‖b - A x₀‖ : ℝ) : 𝕜) with hβ
  have hzero : Matrix.IsUpperHessenberg (n := ℕ) h := Arnoldi.isUpperHessenberg_coeff A (b - A x₀)
  funext i
  rw [Matrix.mulVec_sub, Pi.sub_apply, givensQ_mulVec_firstVec, Arnoldi.hessenberg_eq,
    Matrix.mulVec_mulVec, givensQ_mul_hessenbergOf]
  dsimp only
  by_cases hi : (i : ℕ) < m
  · have hval : (hessenbergOf (rotated h m) m).mulVec y i =
        (hessenbergSqOf (rotated h m) m).mulVec y ⟨(i : ℕ), hi⟩ := rfl
    rw [ite_eq_left hi, hval, hy, ite_eq_right (by omega : ¬(i : ℕ) = m), sub_self]
  · have him : (i : ℕ) = m := by omega
    have hlast : (hessenbergOf (rotated h m) m).mulVec y i = 0 := by
      simp only [Matrix.mulVec, dotProduct, hessenbergOf, Matrix.of_apply, him]
      exact Finset.sum_eq_zero fun j _ => by
        rw [rotated_last_row h hzero m (j : ℕ) j.isLt, zero_mul]
    rw [ite_eq_right hi, hlast, sub_zero, ite_eq_left him]

/-- **The minimal-residual residual in the Arnoldi basis.** Let $r_0 = b - A x_0$ have a
finite-dimensional Krylov space, let $\beta = \|r_0\|$, let $m$ be at most the grade of $r_0$,
and let $\rho_k \neq 0$ for every $k < m$. If $x$ is a minimal-residual iterate at step $m$,
then
$$b - Ax = \sum_{i=0}^{m} \gamma_m \, \overline{(Q_m)_{m,i}} \, v_i.$$
This is (6.40)–(6.47) of [saad2003iterative], read as an identity of vectors.

Only the last row of $Q_m$ enters, because the rotated residual is carried by its last entry
alone (`Krylov.givensQ_mulVec_firstVec_sub_mulVec`) and $Q_m$ is unitary, so undoing it
multiplies that entry by the conjugate of the last row. The hypothesis on $\rho_k$ makes $Q_m$
unitary. It follows from $m$ less than the grade by `Krylov.givensRho_arnoldi_ne_zero`, and at
$m$ equal to the grade it holds exactly when the last rotation does not degenerate;
`Krylov.IsMinResidualIterate.norm_residual_eq_norm_gamma_of_givensRho_ne_zero` has the same
hypothesis. -/
theorem IsMinResidualIterate.residual_eq_gamma_smul_sum {m : ℕ} (hm : m ≤ grade A (b - A x₀))
    (hρ : ∀ k < m, givensRho (Arnoldi.coeff A (b - A x₀)) k ≠ 0) {x : E}
    (hx : IsMinResidualIterate A b x₀ m x) :
    b - A x = ∑ i : Fin (m + 1),
      (gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) m *
          (starRingEnd 𝕜) (givensQ (Arnoldi.coeff A (b - A x₀)) m (Fin.last m) i)) •
        Arnoldi.vec A (b - A x₀) (i : ℕ) := by
  obtain ⟨y, hy, rfl⟩ := hx.exists_mulVec_rotated_eq hm
  have hres := (Arnoldi.hessenbergRelation A (b - A x₀)).residual_eq
    (Arnoldi.smul_vec_zero A (b - A x₀)).symm m y
  rw [hres]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have hQ := givensQ_mem_unitaryGroup (Arnoldi.coeff A (b - A x₀)) m hρ
  rw [Unitary.mem_iff] at hQ
  have hstar : (givensQ (Arnoldi.coeff A (b - A x₀)) m).conjTranspose *
      givensQ (Arnoldi.coeff A (b - A x₀)) m = 1 := hQ.1
  have hkey := givensQ_mulVec_firstVec_sub_mulVec (A := A) (b := b) (x₀ := x₀) hy
  have hinv : (firstVec (‖b - A x₀‖ : 𝕜) (m + 1) -
      (Arnoldi.hessenberg A (b - A x₀) m).mulVec y)
      = ((givensQ (Arnoldi.coeff A (b - A x₀)) m).conjTranspose).mulVec
        (fun l : Fin (m + 1) =>
          if (l : ℕ) = m then gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) m else 0) := by
    rw [← hkey, Matrix.mulVec_mulVec, hstar, Matrix.one_mulVec]
  rw [← Arnoldi.hessenberg_eq A (b - A x₀) m, hinv]
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single (Fin.last m)]
  · rw [ite_eq_left (by simp : ((Fin.last m : Fin (m + 1)) : ℕ) = m), mul_comm,
      starRingEnd_apply]
  · intro l _ hl
    have hlm : (l : ℕ) ≠ m := fun hc => hl (Fin.ext (by simpa using hc))
    rw [ite_eq_right hlm, mul_zero]
  · intro hc
    exact absurd (Finset.mem_univ _) hc

/-- Let $r_0 = b - A x_0$ have a finite-dimensional Krylov space, and let $m + 1$ be less than the
grade of $r_0$. If $x$ and $x'$ are minimal-residual iterates at the steps $m$ and $m + 1$, then
$$\|b - Ax'\| = |s_m| \, \|b - Ax\|.$$
This is (6.47) and Proposition 6.9 of [saad2003iterative].

As for `Krylov.IsMinResidualIterate.norm_residual_eq_norm_gamma`, the strict inequality is
needed. The same counterexample ($\mathbb{K} = E = \mathbb{R}$, $A = 0$, $b = 1$, $x_0 = 0$,
$m = 0$, grade $1$) has $\|b - Ax'\| = 1$ but $|s_0| \, \|b - Ax\| = 0$. -/
theorem IsMinResidualIterate.norm_residual_succ_eq {m : ℕ} (hm : m + 1 < grade A (b - A x₀))
    {x x' : E} (hx : IsMinResidualIterate A b x₀ m x)
    (hx' : IsMinResidualIterate A b x₀ (m + 1) x') :
    ‖b - A x'‖ = ‖givensS (Arnoldi.coeff A (b - A x₀)) m‖ * ‖b - A x‖ := by
  rw [hx'.norm_residual_eq_norm_gamma hm, hx.norm_residual_eq_norm_gamma (by omega),
    gamma_succ, norm_mul, norm_neg]

/-- Let $r_0 = b - A x_0$ have a finite-dimensional Krylov space, and let $m + 1$ be at most the
grade of $r_0$. Then $H_{m+1}$ is nonsingular if and only if $c_m \neq 0$, for the Arnoldi
coefficients. This is Proposition 6.9(1) and Lemma 6.16 of [saad2003iterative]. -/
theorem isUnit_hessenbergSq_iff_givensC_ne_zero {m : ℕ} (hm : m + 1 ≤ grade A (b - A x₀)) :
    IsUnit (Arnoldi.hessenbergSq A (b - A x₀) (m + 1)) ↔
      givensC (Arnoldi.coeff A (b - A x₀)) m ≠ 0 := by
  have hh := Arnoldi.isUpperHessenberg_coeff A (b - A x₀)
  have hρ : ∀ k < m, givensRho (Arnoldi.coeff A (b - A x₀)) k ≠ 0 :=
    fun k hk => givensRho_arnoldi_ne_zero (by omega)
  rw [Arnoldi.hessenbergSq_eq, ne_eq, givensC_eq_zero_iff]
  constructor
  · intro hu h0
    obtain ⟨y, hy⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hu
      (firstVec (‖b - A x₀‖ : 𝕜) (m + 1))
    have hkey := rotated_self_mul_eq_gamma (Arnoldi.coeff A (b - A x₀)) hh
      (‖b - A x₀‖ : 𝕜) hy
    rw [h0, zero_mul] at hkey
    exact gamma_arnoldi_ne_zero (show m < grade A (b - A x₀) by omega) hkey.symm
  · intro hc
    have hd : ∀ j < m + 1, rotated (Arnoldi.coeff A (b - A x₀)) m j j ≠ 0 := by
      intro j hj
      rcases Nat.lt_or_ge j m with hjm | hjm
      · rw [rotated_diag (Arnoldi.coeff A (b - A x₀)) hh hjm]
        simpa using hρ j hjm
      · have hjm' : j = m := by omega
        subst hjm'
        exact hc
    have hR := isUnit_hessenbergSqOf_rotated (Arnoldi.coeff A (b - A x₀)) hh (le_refl (m + 1)) hd
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro z z' hzz'
    have hw : (hessenbergSqOf (Arnoldi.coeff A (b - A x₀)) (m + 1)).mulVec (z - z') = 0 := by
      rw [Matrix.mulVec_sub, hzz', sub_self]
    have hw2 := mulVec_rotated_eq_zero_of_mulVec_eq_zero (Arnoldi.coeff A (b - A x₀)) hw
    have hzz : z - z' = 0 := Matrix.mulVec_injective_iff_isUnit.mpr hR
      (by rw [hw2, Matrix.mulVec_zero])
    exact sub_eq_zero.mp hzz

/-- Let $r_0 = b - A x_0$ have a finite-dimensional Krylov space, and let $m + 1$ be at most the
grade of $r_0$. If $x_F$ is a Galerkin iterate and $x_G$ is a minimal-residual iterate at step
$m + 1$, then
$$\|b - A x_F\| = \frac{\|b - A x_G\|}{|c_m|}.$$
This is (6.75) and Proposition 6.12 of [saad2003iterative].

No hypothesis $c_m \neq 0$ is needed, although the right-hand side would be $0$ by Lean's
convention for division by zero. For $m + 1$ at most the grade, the existence of a Galerkin
iterate already forces $c_m \neq 0$: the system $H_{m+1} y = \beta e_1$ gives
$R^{(m)}_{mm} y_m = \gamma_m$ after the rotations, and $\gamma_m \neq 0$ below the grade, so
$R^{(m)}_{mm} \neq 0$, that is, $c_m \neq 0$. Equivalently, $H_{m+1}$ is then nonsingular
(`Krylov.isUnit_hessenbergSq_iff_givensC_ne_zero`). -/
theorem IsGalerkinIterate.norm_residual_eq_div_norm_givensC {m : ℕ}
    (hm : m + 1 ≤ grade A (b - A x₀)) {xF xG : E} (hF : IsGalerkinIterate A b x₀ (m + 1) xF)
    (hG : IsMinResidualIterate A b x₀ (m + 1) xG) :
    ‖b - A xF‖ = ‖b - A xG‖ / ‖givensC (Arnoldi.coeff A (b - A x₀)) m‖ := by
  have hh := Arnoldi.isUpperHessenberg_coeff A (b - A x₀)
  obtain ⟨y, hy, hxF⟩ := (isGalerkinIterate_iff_exists_mulVec_eq hm xF).mp hF
  rw [Arnoldi.hessenbergSq_eq] at hy
  have hkey := rotated_self_mul_eq_gamma (Arnoldi.coeff A (b - A x₀)) hh (‖b - A x₀‖ : 𝕜) hy
  have hγ := gamma_arnoldi_ne_zero (show m < grade A (b - A x₀) by omega)
  have hrmm : rotated (Arnoldi.coeff A (b - A x₀)) m m m ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hkey
    exact hγ hkey.symm
  have hρm : givensRho (Arnoldi.coeff A (b - A x₀)) m ≠ 0 :=
    givensRho_ne_zero_of_rotated_ne_zero _ hrmm
  have hρall : ∀ k < m + 1, givensRho (Arnoldi.coeff A (b - A x₀)) k ≠ 0 := by
    intro k hk
    rcases Nat.lt_or_ge k m with h1 | h1
    · exact givensRho_arnoldi_ne_zero (by omega)
    · have hk' : k = m := by omega
      subst hk'
      exact hρm
  have hρnn : 0 ≤ givensRho (Arnoldi.coeff A (b - A x₀)) m :=
    givensRho_nonneg (Arnoldi.coeff A (b - A x₀)) m
  have habs : ‖((givensRho (Arnoldi.coeff A (b - A x₀)) m : ℝ) : 𝕜)‖ =
      givensRho (Arnoldi.coeff A (b - A x₀)) m := by
    rw [RCLike.norm_ofReal, abs_of_nonneg hρnn]
  have hcm : ‖rotated (Arnoldi.coeff A (b - A x₀)) m m m‖ =
      ‖givensC (Arnoldi.coeff A (b - A x₀)) m‖ * givensRho (Arnoldi.coeff A (b - A x₀)) m := by
    rw [givensC, norm_div, habs, div_mul_cancel₀ _ hρm]
  have hsm : ‖Arnoldi.coeff A (b - A x₀) (m + 1) m‖ =
      ‖givensS (Arnoldi.coeff A (b - A x₀)) m‖ * givensRho (Arnoldi.coeff A (b - A x₀)) m := by
    rw [givensS, norm_div, habs, div_mul_cancel₀ _ hρm,
      rotated_eq_of_le (Arnoldi.coeff A (b - A x₀)) m (m + 1) m le_rfl]
  have hcne : ‖givensC (Arnoldi.coeff A (b - A x₀)) m‖ ≠ 0 := by
    rw [norm_ne_zero_iff, ne_eq, givensC_eq_zero_iff]
    exact hrmm
  have hkey' : ‖givensC (Arnoldi.coeff A (b - A x₀)) m‖ *
      givensRho (Arnoldi.coeff A (b - A x₀)) m * ‖y ⟨m, Nat.lt_succ_self m⟩‖ =
      ‖gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) m‖ := by
    rw [← hcm, ← norm_mul, hkey]
  have hFnorm : ‖b - A xF‖ =
      ‖Arnoldi.coeff A (b - A x₀) (m + 1) m‖ * ‖y ⟨m, Nat.lt_succ_self m⟩‖ := by
    rw [hxF, norm_residual_eq_norm_firstVec_sub_mulVec hm y, Arnoldi.hessenberg_eq,
      norm_firstVec_sub_mulVec_of_mulVec_eq (Arnoldi.coeff A (b - A x₀)) hh _ hy, norm_mul]
  have hGnorm := (minres_rotated_of_givensRho_ne_zero hm hρall hG).1
  rw [eq_div_iff hcne, hFnorm, hGnorm, gamma_succ, norm_mul, norm_neg, hsm]
  linear_combination ‖givensS (Arnoldi.coeff A (b - A x₀)) m‖ * hkey'

omit [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] in
/-- For the Arnoldi coefficients of $(A, r_0)$ with $r_0 = b - A x_0$, the rotation parameter $s_m$
is the real nonnegative number
$$s_m = \frac{\|w_m\|}{\rho_m},$$
where $w_m$ is the unnormalized next Arnoldi vector ([saad2003iterative], §6.5.9). -/
theorem givensS_arnoldi_eq (m : ℕ) :
    givensS (Arnoldi.coeff A (b - A x₀)) m =
      (‖Arnoldi.w A (b - A x₀) m‖ / givensRho (Arnoldi.coeff A (b - A x₀)) m : ℝ) := by
  rw [givensS, rotated_eq_of_le (Arnoldi.coeff A (b - A x₀)) m (m + 1) m le_rfl,
    Arnoldi.coeff_succ_self, RCLike.ofReal_div]

end GivensArnoldi

end Krylov
