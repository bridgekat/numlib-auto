/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz
import Numlib.Multigrid.Basic

/-!
# The one-dimensional model problem of two-grid analysis

This module studies the transfer operators between a fine grid of $2m + 1$ interior points and the
coarse grid of the $m$ interior points that remain when every other fine point is dropped. The two
operators are **linear interpolation** $P \in \mathbb{R}^{(2m+1) \times m}$ and **full weighting**
$R = \frac{1}{2} P^T \in \mathbb{R}^{m \times (2m+1)}$. The module computes their action on the
discrete sine modes of `Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz`. This is the standard
Fourier analysis of the two-grid method for the second-difference matrix
$T_k = \operatorname{tridiag}(-1, 2, -1)$ of order $k$, as in [golub2013matrix], §11.6.3–11.6.4,
Lemma 11.6.1 and Theorem 11.6.2, and in [saad2003iterative], §13.3, (13.30)–(13.35) and Example
13.7.

Let $w_l$ for $0 \le l \le 2m$ be the fine sine modes, and let $v_j$ for $0 \le j < m$ be the coarse
sine modes. For a coarse index $j$, let $\theta = (j + 1)\pi / (2m + 2)$ be the angle of the fine
mode $w_j$, and let $c = \cos(\theta/2)$ and $s = \sin(\theta/2)$. The fine mode $w_j$ and its
**alias** $w_{2m-j}$ agree up to sign at the coarse points, and the middle mode $w_m$ vanishes
there. Interpolation and restriction map the pair $\{w_j, w_{2m-j}\}$ to $v_j$ and back, and the
exact coarse-grid correction maps the pair to multiples of $w_j + w_{2m-j}$.

## Main definitions

* `Multigrid.linearInterpolation`: the linear interpolation matrix $P$, with the stencil
  $\frac{1}{2} [1\ 2\ 1]$ in each column.
* `Multigrid.fullWeighting`: the full weighting matrix $R = \frac{1}{2} P^T$, with the stencil
  $\frac{1}{4} [1\ 2\ 1]$ in each row.
* `Multigrid.modeAngle`: the angle $\theta = (j + 1)\pi / (2m + 2)$ of the fine mode $j$.
* `Multigrid.fineIndex`, `Multigrid.aliasIndex`, `Multigrid.middleIndex`: the fine indices $j$,
  $2m - j$ and $m$.
* `Multigrid.modelCoarseCorrection`: the exact coarse-grid correction
  $E = I - P T_m^{-1} (4R) T_{2m+1}$.

## Main results

* `Multigrid.fullWeighting_mul_mul_linearInterpolation`: the **Galerkin identity**
  $R T_{2m+1} P = \frac{1}{4} T_m$. With the mesh scaling, this is $R A^h P = A^{2h}$.
* `Multigrid.linearInterpolation_mulVec_sineVec`: interpolation of the coarse mode $j$ excites the
  fine mode $j$ and its alias, $P v_j = c^2 w_j - s^2 w_{2m-j}$.
* `Multigrid.fullWeighting_mulVec_sineVec`, `Multigrid.fullWeighting_mulVec_sineVec_aliasIndex`,
  `Multigrid.fullWeighting_mulVec_sineVec_middleIndex`: restriction of the three kinds of fine
  modes, $R w_j = c^2 v_j$, $R w_{2m-j} = -s^2 v_j$ and $R w_m = 0$. The general entrywise formula
  is `Multigrid.fullWeighting_mulVec_sineVec_apply`.
* `Multigrid.modelCoarseCorrection_mulVec_sineVec`,
  `Multigrid.modelCoarseCorrection_mulVec_sineVec_aliasIndex`,
  `Multigrid.modelCoarseCorrection_mulVec_sineVec_middleIndex`: the exact coarse-grid correction
  maps $w_j \mapsto s^2 (w_j + w_{2m-j})$ and $w_{2m-j} \mapsto c^2 (w_j + w_{2m-j})$, and it fixes
  $w_m$. So it annihilates the smooth part of each mode pair as $s \to 0$.
* `Multigrid.toEuclideanLin_modelCoarseCorrection`: the exact coarse-grid correction is the abstract
  coarse-grid correction `Multigrid.coarseCorrection` of $T_{2m+1}$ with the prolongation $P$.

## Proof outline

The Galerkin identity is proved on the sine basis. Both sides act on the coarse mode $v_j$ as
multiplication by $4 s^2 c^2 = \sin^2 \theta$. Two matrices that agree on every coarse sine mode are
equal, because the sine matrix squares to a nonzero multiple of the identity.

## Implementation notes

* The mesh width $h = 1/(2m + 2)$ does not appear. The second-difference matrix $T_k$ is
  `Matrix.symmTridiagonalToeplitz k (-1) 2`, and the discretized operators of the sources are
  $A^h = h^{-2} T_{2m+1}$ and $A^{2h} = (2h)^{-2} T_m$.
* Indices start at $0$. The fine points are `i : Fin (2 * m + 1)`, the coarse points are
  `j : Fin m`, and the coarse point $j$ is the fine point $2j + 1$. The sine modes are
  `Matrix.sineVec`: the fine mode $w_l$ is `Matrix.sineVec (2 * m + 1) l` and the coarse mode $v_j$
  is `Matrix.sineVec m j`.
-/

open Matrix Real
open scoped Matrix

namespace Multigrid

variable {m : ℕ}

/-! ### The transfer operators -/

/-- **Linear interpolation** from the $m$ interior points of the coarse grid to the $2m + 1$
interior points of the fine grid is the matrix $P \in \mathbb{R}^{(2m+1) \times m}$ with the
entries
$$P_{ij} = \begin{cases} 1 & \text{if } i = 2j + 1, \\ \frac{1}{2} & \text{if } i = 2j \text{ or
  } i = 2j + 2, \\ 0 & \text{otherwise}. \end{cases}$$

Column $j$ carries the stencil $\frac{1}{2} [1\ 2\ 1]$ on the fine rows $2j$, $2j + 1$,
$2j + 2$. The fine point $2j + 1$ is the coarse point $j$ and takes its value. Each of the two
fine points next to it takes the average of its two coarse neighbours, and a neighbour outside
the coarse grid is the boundary value $0$. Indices start at $0$. -/
noncomputable def linearInterpolation (m : ℕ) : Matrix (Fin (2 * m + 1)) (Fin m) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = 2 * (j : ℕ) + 1 then 1
    else if (i : ℕ) = 2 * (j : ℕ) then 1 / 2
    else if (i : ℕ) = 2 * (j : ℕ) + 2 then 1 / 2
    else 0

/-- The entries of the linear interpolation matrix: $P_{ij} = 1$ if $i = 2j + 1$,
$P_{ij} = \frac{1}{2}$ if $i = 2j$ or $i = 2j + 2$, and $P_{ij} = 0$ otherwise. -/
theorem linearInterpolation_apply (i : Fin (2 * m + 1)) (j : Fin m) :
    linearInterpolation m i j =
      if (i : ℕ) = 2 * (j : ℕ) + 1 then 1
      else if (i : ℕ) = 2 * (j : ℕ) then 1 / 2
      else if (i : ℕ) = 2 * (j : ℕ) + 2 then 1 / 2
      else 0 :=
  rfl

/-- **Full weighting** from the $2m + 1$ interior points of the fine grid to the $m$ interior points
of the coarse grid is the scaled transpose of linear interpolation:
$$R = \tfrac{1}{2} P^T \in \mathbb{R}^{m \times (2m+1)}.$$

Row $j$ carries the stencil $\frac{1}{4} [1\ 2\ 1]$ on the fine columns $2j$, $2j + 1$,
$2j + 2$, by `Multigrid.fullWeighting_apply`. -/
noncomputable def fullWeighting (m : ℕ) : Matrix (Fin m) (Fin (2 * m + 1)) ℝ :=
  (1 / 2 : ℝ) • (linearInterpolation m)ᵀ

/-- The entries of the full weighting matrix: $R_{ji} = \frac{1}{2}$ if $i = 2j + 1$,
$R_{ji} = \frac{1}{4}$ if $i = 2j$ or $i = 2j + 2$, and $R_{ji} = 0$ otherwise. -/
theorem fullWeighting_apply (j : Fin m) (i : Fin (2 * m + 1)) :
    fullWeighting m j i =
      if (i : ℕ) = 2 * (j : ℕ) + 1 then 1 / 2
      else if (i : ℕ) = 2 * (j : ℕ) then 1 / 4
      else if (i : ℕ) = 2 * (j : ℕ) + 2 then 1 / 4
      else 0 := by
  rw [fullWeighting, Matrix.smul_apply, transpose_apply, linearInterpolation_apply, smul_eq_mul]
  split_ifs <;> norm_num

/-- Each entry $P_{ij}$ is half the sum of the indicators of $j + 1 = \lfloor (i + 1)/2 \rfloor$ and
of $j + 1 = \lfloor (i + 2)/2 \rfloor$: the fine point $i$ lies between these two coarse grid
positions, which coincide at a coarse point. -/
private theorem linearInterpolation_apply_eq_half (i : Fin (2 * m + 1)) (j : Fin m) :
    linearInterpolation m i j =
      ((if ((i : ℕ) + 1) / 2 = (j : ℕ) + 1 then 1 else 0) +
        (if ((i : ℕ) + 2) / 2 = (j : ℕ) + 1 then 1 else 0)) / 2 := by
  rw [linearInterpolation_apply]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- The value of a coarse vector $u$ at the coarse grid position $K$: position $j + 1$ carries
$u_j$, and the boundary positions $0$ and $m + 1$ and all positions beyond carry $0$. -/
private noncomputable def coarseAt (u : Fin m → ℝ) (K : ℕ) : ℝ :=
  ∑ j : Fin m, if K = (j : ℕ) + 1 then u j else 0

/-- Linear interpolation averages the coarse values at the two coarse grid positions
$\lfloor (i + 1)/2 \rfloor$ and $\lfloor (i + 2)/2 \rfloor$ nearest to the fine point $i$. -/
private theorem linearInterpolation_mulVec_apply (u : Fin m → ℝ) (i : Fin (2 * m + 1)) :
    (linearInterpolation m *ᵥ u) i =
      (coarseAt u (((i : ℕ) + 1) / 2) + coarseAt u (((i : ℕ) + 2) / 2)) / 2 := by
  simp only [mulVec, dotProduct, linearInterpolation_apply_eq_half, coarseAt]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- Full weighting applies the stencil $\frac{1}{4} [1\ 2\ 1]$ around the fine point $2q + 1$ of the
coarse point $q$: for $v \in \mathbb{R}^{2m+1}$ and $0 \le q < m$,
$$(Rv)_q = \frac{v_{2q} + 2 v_{2q+1} + v_{2q+2}}{4}.$$
-/
theorem fullWeighting_mulVec_apply (v : Fin (2 * m + 1) → ℝ) (q : Fin m) :
    (fullWeighting m *ᵥ v) q =
      (v ⟨2 * q, by omega⟩ + 2 * v ⟨2 * q + 1, by omega⟩ + v ⟨2 * q + 2, by omega⟩) / 4 := by
  set a : Fin (2 * m + 1) := ⟨2 * q, by omega⟩ with ha
  set b : Fin (2 * m + 1) := ⟨2 * q + 1, by omega⟩ with hb
  set c : Fin (2 * m + 1) := ⟨2 * q + 2, by omega⟩ with hc
  have hab : a ≠ b := fun h => by simp [ha, hb, Fin.ext_iff] at h
  have hac : a ≠ c := fun h => by simp [ha, hc, Fin.ext_iff] at h
  have hbc : b ≠ c := fun h => by simp [hb, hc, Fin.ext_iff] at h
  have hzero : ∀ p ∈ Finset.univ, p ∉ ({a, b, c} : Finset (Fin (2 * m + 1))) →
      fullWeighting m q p * v p = 0 := by
    intro p _ hp
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or, ha, hb, hc, Fin.ext_iff] at hp
    rw [fullWeighting_apply, ite_eq_right hp.2.1, ite_eq_right hp.1, ite_eq_right hp.2.2,
      zero_mul]
  rw [mulVec, dotProduct, ← Finset.sum_subset (Finset.subset_univ _) hzero,
    Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton, fullWeighting_apply, fullWeighting_apply, fullWeighting_apply]
  simp only [ha, hb, hc]
  split_ifs <;> first | (exfalso; omega) | ring

/-! ### The sine modes on the two grids -/

/-- The angle $\theta_j = (j + 1)\pi / (2m + 2)$ of the fine sine mode $j$, for $0 \le j < m$. It is
half the angle $(j + 1)\pi / (m + 1)$ of the coarse sine mode $j$. -/
noncomputable def modeAngle (m : ℕ) (j : Fin m) : ℝ := (((j : ℕ) : ℝ) + 1) * π / (2 * m + 2)

/-- The fine index of the coarse mode $j$: the index $j$ read in $\{0, \dots, 2m\}$. The fine mode
with this index has the same frequency as the coarse mode $j$. -/
def fineIndex (j : Fin m) : Fin (2 * m + 1) := ⟨j, by have := j.isLt; omega⟩

/-- The alias $2m - j$ of the fine mode $j$, for $0 \le j < m$. The fine mode $2m - j$ agrees with
the fine mode $j$ up to sign at the coarse points. -/
def aliasIndex (j : Fin m) : Fin (2 * m + 1) := ⟨2 * m - j, by omega⟩

/-- The middle fine index $m$. The fine mode $m$ vanishes at every coarse point. -/
def middleIndex (m : ℕ) : Fin (2 * m + 1) := ⟨m, by omega⟩

/-- The mode angle is positive: $\theta_j > 0$. -/
theorem modeAngle_pos (j : Fin m) : 0 < modeAngle m j := by
  rw [modeAngle]
  positivity

/-- The mode angle is less than $\pi/2$: $\theta_j < \pi/2$. So $\sin(\theta_j/2)$ and
$\cos(\theta_j/2)$ are positive. -/
theorem modeAngle_lt_pi_div_two (j : Fin m) : modeAngle m j < π / 2 := by
  have hj : ((j : ℕ) : ℝ) + 1 ≤ m := by
    have := j.isLt
    exact_mod_cast this
  rw [modeAngle, div_lt_div_iff₀ (by positivity) two_pos]
  nlinarith [Real.pi_pos]

/-- The fine mode $j$ has the angle $\theta_j$: $(w_j)_i = \sin((i + 1)\theta_j)$ for
$0 \le i \le 2m$. -/
theorem sineVec_fineIndex (j : Fin m) (i : Fin (2 * m + 1)) :
    sineVec (2 * m + 1) (fineIndex j) i = Real.sin ((((i : ℕ) : ℝ) + 1) * modeAngle m j) := by
  rw [sineVec_apply, modeAngle, fineIndex]
  push_cast
  ring_nf

/-- The coarse mode $j$ has the angle $2\theta_j$: $(v_j)_q = \sin((q + 1) \cdot 2\theta_j)$ for
$0 \le q < m$. -/
theorem sineVec_coarse (j q : Fin m) :
    sineVec m j q = Real.sin ((((q : ℕ) : ℝ) + 1) * (2 * modeAngle m j)) := by
  rw [sineVec_apply, modeAngle]
  congr 1
  field_simp

/-- The angle of the alias $2m - j$ is $\pi - \theta_j$:
$(2m - j + 1)\pi / (2m + 2) = \pi - \theta_j$. -/
theorem angle_aliasIndex (j : Fin m) :
    (((aliasIndex j : ℕ) : ℝ) + 1) * π / (((2 * m + 1 : ℕ) : ℝ) + 1) = π - modeAngle m j := by
  have hj : (j : ℕ) ≤ 2 * m := by have := j.isLt; omega
  rw [aliasIndex, modeAngle, Fin.val_mk, Nat.cast_sub hj]
  push_cast
  field_simp
  ring

/-- The alias $2m - j$ of the fine mode $j$ is the fine mode $j$ with alternating signs:
$$(w_{2m-j})_i = (-1)^i (w_j)_i \quad \text{for } 0 \le i \le 2m.$$

The reason is that the angle of the alias is $\pi - \theta_j$, by `Multigrid.angle_aliasIndex`. -/
theorem sineVec_aliasIndex (j : Fin m) (i : Fin (2 * m + 1)) :
    sineVec (2 * m + 1) (aliasIndex j) i =
      (-1) ^ (i : ℕ) * sineVec (2 * m + 1) (fineIndex j) i := by
  rw [sineVec_fineIndex, sineVec_apply, angle_aliasIndex]
  rw [show ((((i : ℕ) : ℝ) + 1) * (π - modeAngle m j))
      = (((i : ℕ) + 1 : ℕ) : ℝ) * π - (((i : ℕ) : ℝ) + 1) * modeAngle m j by push_cast; ring,
    Real.sin_sub, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
  ring

/-- The middle fine mode has the angle $\pi/2$: $(w_m)_i = \sin((i + 1)\pi/2)$ for $0 \le i \le 2m$.
-/
theorem sineVec_middleIndex (i : Fin (2 * m + 1)) :
    sineVec (2 * m + 1) (middleIndex m) i = Real.sin ((((i : ℕ) : ℝ) + 1) * (π / 2)) := by
  rw [sineVec_apply, middleIndex]
  congr 1
  push_cast
  field_simp
  ring

/-- The coarse mode $j$ at the coarse grid position $K \le m + 1$, boundaries included, is
$\sin(K \cdot 2\theta_j)$; this vanishes at $K = 0$ and at $K = m + 1$. -/
private theorem coarseAt_sineVec (j : Fin m) {K : ℕ} (hK : K ≤ m + 1) :
    coarseAt (sineVec m j) K = Real.sin (K * (2 * modeAngle m j)) := by
  rcases K with _ | k
  · simp [coarseAt]
  · by_cases hk : k < m
    · rw [coarseAt, Finset.sum_eq_single ⟨k, hk⟩]
      · rw [ite_eq_left (by simp), sineVec_coarse]
        push_cast
        ring_nf
      · intro b _ hb
        refine ite_eq_right fun h => hb (Fin.ext ?_)
        change (b : ℕ) = k
        omega
      · simp
    · have hkm : k = m := by omega
      subst hkm
      have hsum : coarseAt (sineVec k j) (k + 1) = 0 :=
        Finset.sum_eq_zero fun b _ => ite_eq_right fun h => by omega
      rw [hsum, modeAngle]
      have hrw : ((k + 1 : ℕ) : ℝ) * (2 * ((((j : ℕ) : ℝ) + 1) * π / (2 * k + 2)))
          = (((j : ℕ) + 1 : ℕ) : ℝ) * π := by
        push_cast
        field_simp
      rw [hrw, Real.sin_nat_mul_pi]

/-- For every real $\theta$, $\cos\theta = \cos^2(\theta/2) - \sin^2(\theta/2)$. -/
private theorem cos_eq_cos_sq_half_sub (θ : ℝ) :
    Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
  have h := Real.cos_two_mul (θ / 2)
  have h2 := Real.sin_sq_add_cos_sq (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h
  linarith

/-! ### Interpolation and restriction of the sine modes -/

/-- Let $0 \le j < m$, let $\theta = (j + 1)\pi / (2m + 2)$, and let $c = \cos(\theta/2)$ and
$s = \sin(\theta/2)$. Linear interpolation maps the coarse mode $v_j$ to a combination of the
fine mode $w_j$ and its alias $w_{2m-j}$:
$$P v_j = c^2 w_j - s^2 w_{2m-j}.$$

This is the first identity of Lemma 11.6.1 of [golub2013matrix]. At a coarse point, both fine
modes equal the coarse mode up to the sign of the alias, and $c^2 + s^2 = 1$. At a fine point
between two coarse points, the average $\frac{1}{2}(v_{q-1} + v_q)$ of the two neighbouring
coarse values is $\cos\theta$ times the fine mode, and $c^2 - s^2 = \cos\theta$. -/
theorem linearInterpolation_mulVec_sineVec (j : Fin m) :
    linearInterpolation m *ᵥ sineVec m j =
      Real.cos (modeAngle m j / 2) ^ 2 • sineVec (2 * m + 1) (fineIndex j) -
        Real.sin (modeAngle m j / 2) ^ 2 • sineVec (2 * m + 1) (aliasIndex j) := by
  funext i
  have hi := i.isLt
  rw [linearInterpolation_mulVec_apply, coarseAt_sineVec j (by omega),
    coarseAt_sineVec j (by omega), Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
    smul_eq_mul, sineVec_aliasIndex, sineVec_fineIndex]
  set θ := modeAngle m j
  have hcs := Real.sin_sq_add_cos_sq (θ / 2)
  have hcos := cos_eq_cos_sq_half_sub θ
  obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' (i : ℕ)
  · -- a fine point between two coarse points
    have e₁ : Real.sin (((q : ℕ) : ℝ) * (2 * θ)) =
        Real.sin ((((2 * q : ℕ) : ℝ) + 1) * θ - θ) := by
      congr 1; push_cast; ring
    have e₂ : Real.sin (((q + 1 : ℕ) : ℝ) * (2 * θ)) =
        Real.sin ((((2 * q : ℕ) : ℝ) + 1) * θ + θ) := by
      congr 1; push_cast; ring
    rw [show ((i : ℕ) + 1) / 2 = q by omega, show ((i : ℕ) + 2) / 2 = q + 1 by omega, hq,
      (even_two_mul q).neg_one_pow, e₁, e₂, Real.sin_sub, Real.sin_add, hcos]
    ring
  · -- a coarse point
    have e : Real.sin (((q + 1 : ℕ) : ℝ) * (2 * θ)) =
        Real.sin ((((2 * q + 1 : ℕ) : ℝ) + 1) * θ) := by
      congr 1; push_cast; ring
    rw [show ((i : ℕ) + 1) / 2 = q + 1 by omega, show ((i : ℕ) + 2) / 2 = q + 1 by omega, hq,
      (odd_two_mul_add_one q).neg_one_pow, e]
    linear_combination (-Real.sin ((((2 * q + 1 : ℕ) : ℝ) + 1) * θ)) * hcs

/-- Let $0 \le l \le 2m$ and let $\varphi = (l + 1)\pi / (2m + 2)$ be the angle of the fine mode
$w_l$. Then full weighting maps $w_l$ to
$$(R w_l)_q = \cos^2(\varphi/2) \sin(2(q + 1)\varphi) \quad \text{for } 0 \le q < m.$$

This is the computation of Example 13.7 of [saad2003iterative]. The stencil
$\frac{1}{4} [1\ 2\ 1]$ meets $\sin((2q + 1)\varphi) + \sin((2q + 3)\varphi) = 2 \sin((2q +
2)\varphi) \cos\varphi$, and $(1 + \cos\varphi)/2 = \cos^2(\varphi/2)$. The angle is written as
in `Matrix.sineVec`, with the denominator $(2m + 1) + 1$. -/
theorem fullWeighting_mulVec_sineVec_apply (l : Fin (2 * m + 1)) (q : Fin m) :
    (fullWeighting m *ᵥ sineVec (2 * m + 1) l) q =
      Real.cos ((((l : ℕ) : ℝ) + 1) * π / (((2 * m + 1 : ℕ) : ℝ) + 1) / 2) ^ 2 *
        Real.sin (2 * (((q : ℕ) : ℝ) + 1) * ((((l : ℕ) : ℝ) + 1) * π / (((2 * m + 1 : ℕ) : ℝ) + 1)))
    := by
  rw [fullWeighting_mulVec_apply, sineVec_apply, sineVec_apply, sineVec_apply]
  push_cast
  set φ := (((l : ℕ) : ℝ) + 1) * π / (2 * (m : ℝ) + 1 + 1)
  have hcos := cos_eq_cos_sq_half_sub φ
  have hcs := Real.sin_sq_add_cos_sq (φ / 2)
  rw [show (2 * ((q : ℕ) : ℝ) + 1) * φ = (2 * q + 2) * φ - φ by ring,
    show (2 * ((q : ℕ) : ℝ) + 1 + 1) * φ = (2 * q + 2) * φ by ring,
    show (2 * ((q : ℕ) : ℝ) + 2 + 1) * φ = (2 * q + 2) * φ + φ by ring, Real.sin_sub, Real.sin_add,
    hcos, show 2 * (((q : ℕ) : ℝ) + 1) * φ = (2 * q + 2) * φ by ring]
  linear_combination (-Real.sin ((2 * ((q : ℕ) : ℝ) + 2) * φ) / 2) * hcs

/-- Let $0 \le j < m$ and $c = \cos(\theta_j/2)$. Full weighting maps the fine mode $w_j$ to a
multiple of the coarse mode $v_j$:
$$R w_j = c^2 v_j.$$

This is the second identity of Lemma 11.6.1 of [golub2013matrix]. -/
theorem fullWeighting_mulVec_sineVec (j : Fin m) :
    fullWeighting m *ᵥ sineVec (2 * m + 1) (fineIndex j) =
      Real.cos (modeAngle m j / 2) ^ 2 • sineVec m j := by
  funext q
  rw [fullWeighting_mulVec_sineVec_apply, Pi.smul_apply, smul_eq_mul, sineVec_coarse]
  have h : (((fineIndex j : ℕ) : ℝ) + 1) * π / (((2 * m + 1 : ℕ) : ℝ) + 1) = modeAngle m j := by
    rw [fineIndex, modeAngle]
    push_cast
    ring_nf
  rw [h]
  ring_nf

/-- Let $0 \le j < m$ and $s = \sin(\theta_j/2)$. Full weighting maps the alias $w_{2m-j}$ to a
multiple of the coarse mode $v_j$:
$$R w_{2m-j} = -s^2 v_j.$$

This is the second identity of Lemma 11.6.1 of [golub2013matrix]. The alias goes to the same
coarse mode as the fine mode $j$, with the other weight. -/
theorem fullWeighting_mulVec_sineVec_aliasIndex (j : Fin m) :
    fullWeighting m *ᵥ sineVec (2 * m + 1) (aliasIndex j) =
      -(Real.sin (modeAngle m j / 2) ^ 2) • sineVec m j := by
  funext q
  rw [fullWeighting_mulVec_sineVec_apply, Pi.smul_apply, smul_eq_mul, sineVec_coarse]
  have h := angle_aliasIndex j
  set θ := modeAngle m j
  have hc : Real.cos ((π - θ) / 2) = Real.sin (θ / 2) := by
    rw [show (π - θ) / 2 = π / 2 - θ / 2 by ring, Real.cos_pi_div_two_sub]
  have hs : Real.sin (2 * (((q : ℕ) : ℝ) + 1) * (π - θ)) =
      -Real.sin ((((q : ℕ) : ℝ) + 1) * (2 * θ)) := by
    rw [show 2 * (((q : ℕ) : ℝ) + 1) * (π - θ) =
        ((2 * ((q : ℕ) + 1) : ℕ) : ℝ) * π - (((q : ℕ) : ℝ) + 1) * (2 * θ) by push_cast; ring,
      Real.sin_sub, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi, (even_two_mul _).neg_one_pow]
    ring
  rw [h, hc, hs]
  ring

/-- The middle fine mode is invisible on the coarse grid: $R w_m = 0$. -/
theorem fullWeighting_mulVec_sineVec_middleIndex :
    fullWeighting m *ᵥ sineVec (2 * m + 1) (middleIndex m) = 0 := by
  funext q
  rw [fullWeighting_mulVec_sineVec_apply, Pi.zero_apply]
  have h : (((middleIndex m : ℕ) : ℝ) + 1) * π / (((2 * m + 1 : ℕ) : ℝ) + 1) = π / 2 := by
    rw [middleIndex]
    push_cast
    field_simp
    ring
  rw [h, show 2 * (((q : ℕ) : ℝ) + 1) * (π / 2) = (((q : ℕ) + 1 : ℕ) : ℝ) * π by push_cast; ring,
    Real.sin_nat_mul_pi, mul_zero]

/-! ### The Galerkin identity -/

/-- The discrete sine vectors are symmetric in the mode and the point: the entry $i$ of the mode $k$
equals the entry $k$ of the mode $i$. -/
private theorem sineVec_comm {n : ℕ} (k l : Fin n) : sineVec n k l = sineVec n l k := by
  rw [sineVec_apply, sineVec_apply]
  ring_nf

/-- Two matrices that agree on every sine mode are equal, because the sine matrix squares to
$(n + 1)/2$ times the identity, by the orthogonality of the sine modes. -/
private theorem ext_of_mulVec_sineVec {p n : ℕ} {A B : Matrix (Fin p) (Fin n) ℝ}
    (h : ∀ k, A *ᵥ sineVec n k = B *ᵥ sineVec n k) : A = B := by
  have key : ∀ (M : Matrix (Fin p) (Fin n) ℝ) (i : Fin p) (k : Fin n),
      ∑ j, (M *ᵥ sineVec n j) i * sineVec n j k = ((n : ℝ) + 1) / 2 * M i k := by
    intro M i k
    simp only [mulVec, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
    have hl : ∀ l : Fin n, ∑ j, M i l * sineVec n j l * sineVec n j k
        = M i l * (sineVec n l ⬝ᵥ sineVec n k) := by
      intro l
      rw [dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [sineVec_comm j l, sineVec_comm j k]
      ring
    simp only [hl, dotProduct_sineVec, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    ring
  ext i k
  have hA := key A i k
  rw [Finset.sum_congr rfl fun j _ => by rw [h j]] at hA
  rw [key B i k] at hA
  have hn : ((n : ℝ) + 1) / 2 ≠ 0 := by positivity
  exact (mul_left_cancel₀ hn hA).symm

/-- The fine second-difference matrix scales the fine mode $j$ by $4 s^2$:
$T_{2m+1} w_j = 4 \sin^2(\theta_j/2)\, w_j$. -/
private theorem symmTridiagonalToeplitz_mulVec_sineVec_fineIndex (j : Fin m) :
    symmTridiagonalToeplitz (2 * m + 1) (-1) 2 *ᵥ sineVec (2 * m + 1) (fineIndex j) =
      (4 * Real.sin (modeAngle m j / 2) ^ 2) • sineVec (2 * m + 1) (fineIndex j) := by
  rw [symmTridiagonalToeplitz_mulVec_sineVec]
  congr 1
  have h : (((fineIndex j : ℕ) : ℝ) + 1) * π / (((2 * m + 1 : ℕ) : ℝ) + 1) = modeAngle m j := by
    rw [fineIndex, modeAngle]
    push_cast
    ring_nf
  rw [h, cos_eq_cos_sq_half_sub]
  linear_combination (-2 : ℝ) * Real.sin_sq_add_cos_sq (modeAngle m j / 2)

/-- The fine second-difference matrix scales the alias $2m - j$ by $4 c^2$: $T_{2m+1} w_{2m-j} = 4
\cos^2(\theta_j/2)\, w_{2m-j}$. -/
private theorem symmTridiagonalToeplitz_mulVec_sineVec_aliasIndex (j : Fin m) :
    symmTridiagonalToeplitz (2 * m + 1) (-1) 2 *ᵥ sineVec (2 * m + 1) (aliasIndex j) =
      (4 * Real.cos (modeAngle m j / 2) ^ 2) • sineVec (2 * m + 1) (aliasIndex j) := by
  rw [symmTridiagonalToeplitz_mulVec_sineVec]
  congr 1
  have h := angle_aliasIndex j
  rw [h, Real.cos_pi_sub, cos_eq_cos_sq_half_sub]
  linear_combination (-2 : ℝ) * Real.sin_sq_add_cos_sq (modeAngle m j / 2)

/-- The coarse second-difference matrix scales the coarse mode $j$ by
$4 \sin^2\theta_j = 16 s^2 c^2$: $T_m v_j = 16 \sin^2(\theta_j/2) \cos^2(\theta_j/2)\, v_j$. -/
private theorem symmTridiagonalToeplitz_mulVec_sineVec_coarse (j : Fin m) :
    symmTridiagonalToeplitz m (-1) 2 *ᵥ sineVec m j =
      (16 * Real.sin (modeAngle m j / 2) ^ 2 * Real.cos (modeAngle m j / 2) ^ 2) •
        sineVec m j := by
  rw [symmTridiagonalToeplitz_mulVec_sineVec]
  congr 1
  have h : (((j : ℕ) : ℝ) + 1) * π / ((m : ℝ) + 1) = 2 * modeAngle m j := by
    rw [modeAngle]
    field_simp
  have hcs := Real.sin_sq_add_cos_sq (modeAngle m j / 2)
  rw [h, show 2 * modeAngle m j = 2 * (2 * (modeAngle m j / 2)) by ring, Real.cos_two_mul,
    Real.cos_two_mul]
  linear_combination (-16 * Real.cos (modeAngle m j / 2) ^ 2) * hcs

/-- The **Galerkin identity** of the model problem. Let $T_k = \operatorname{tridiag}(-1, 2, -1)$ of
order $k$. Full weighting $R$, the fine matrix $T_{2m+1}$ and linear interpolation $P$ satisfy
$$R\, T_{2m+1}\, P = \tfrac{1}{4} T_m.$$

With $A^h = h^{-2} T_{2m+1}$ and $A^{2h} = (2h)^{-2} T_m$, this says that the coarse matrix is
the Galerkin one, $R A^h P = A^{2h}$ ([golub2013matrix], §11.6.3). Both sides multiply the
coarse mode $v_j$ by $4 s^2 c^2$: interpolation gives $c^2 w_j - s^2 w_{2m-j}$, the fine matrix
scales the two fine modes by $4 s^2$ and $4 c^2$, and restriction returns $c^2 v_j$ and
$-s^2 v_j$. -/
theorem fullWeighting_mul_mul_linearInterpolation :
    fullWeighting m * symmTridiagonalToeplitz (2 * m + 1) (-1) 2 * linearInterpolation m =
      (1 / 4 : ℝ) • symmTridiagonalToeplitz m (-1) 2 := by
  refine ext_of_mulVec_sineVec fun j => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, linearInterpolation_mulVec_sineVec, mulVec_sub,
    mulVec_smul, mulVec_smul, symmTridiagonalToeplitz_mulVec_sineVec_fineIndex,
    symmTridiagonalToeplitz_mulVec_sineVec_aliasIndex, smul_smul, smul_smul, mulVec_sub,
    mulVec_smul, mulVec_smul, fullWeighting_mulVec_sineVec,
    fullWeighting_mulVec_sineVec_aliasIndex, smul_smul, smul_smul, ← sub_smul, smul_mulVec,
    symmTridiagonalToeplitz_mulVec_sineVec_coarse, smul_smul]
  congr 1
  have hcs := Real.sin_sq_add_cos_sq (modeAngle m j / 2)
  linear_combination (4 * Real.sin (modeAngle m j / 2) ^ 2 *
    Real.cos (modeAngle m j / 2) ^ 2) * hcs

/-! ### The exact coarse-grid correction -/

/-- The **exact coarse-grid correction** of the model problem is the matrix
$$E = I - P\, T_m^{-1} (4R)\, T_{2m+1} \in \mathbb{R}^{(2m+1) \times (2m+1)}.$$

This is the matrix $E^h = I - P (A^{2h})^{-1} R A^h$ of (11.6.20) of [golub2013matrix], after
the scaling $A^h = h^{-2} T_{2m+1}$ and $A^{2h} = (2h)^{-2} T_m$. The inverse $T_m^{-1}$ is the
matrix inverse of Mathlib. It is the true inverse, because $T_m$ is positive definite. -/
noncomputable def modelCoarseCorrection (m : ℕ) : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ :=
  1 - linearInterpolation m * (symmTridiagonalToeplitz m (-1) 2)⁻¹ * ((4 : ℝ) • fullWeighting m) *
    symmTridiagonalToeplitz (2 * m + 1) (-1) 2

/-- The coarse second-difference matrix is invertible: $T_m^{-1} (T_m v) = v$ for every
$v \in \mathbb{R}^m$. -/
private theorem inv_mulVec_mulVec_coarse (v : Fin m → ℝ) :
    (symmTridiagonalToeplitz m (-1) 2)⁻¹ *ᵥ (symmTridiagonalToeplitz m (-1) 2 *ᵥ v) = v := by
  have hdet : IsUnit (symmTridiagonalToeplitz m (-1) 2).det :=
    (posDef_symmTridiagonalToeplitz_neg_one_two m).isUnit.map Matrix.detMonoidHom
  rw [mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]

/-- The exact coarse-grid correction acts as $Ew = w - P\, T_m^{-1} (4R)\, T_{2m+1} w$, through the
coarse residual that it corrects. -/
private theorem modelCoarseCorrection_mulVec (w : Fin (2 * m + 1) → ℝ) :
    modelCoarseCorrection m *ᵥ w = w - linearInterpolation m *ᵥ
      ((symmTridiagonalToeplitz m (-1) 2)⁻¹ *ᵥ
        (((4 : ℝ) • fullWeighting m) *ᵥ (symmTridiagonalToeplitz (2 * m + 1) (-1) 2 *ᵥ w))) := by
  simp only [modelCoarseCorrection, sub_mulVec, one_mulVec, mulVec_mulVec, Matrix.mul_assoc]

/-- Let $0 \le j < m$ and $s = \sin(\theta_j/2)$. The exact coarse-grid correction maps the fine
mode $w_j$ to
$$E w_j = s^2 (w_j + w_{2m-j}).$$

This is (11.6.21) of Theorem 11.6.2 of [golub2013matrix]. The restricted residual
$4R\, T_{2m+1} w_j = 16 s^2 c^2 v_j$ is exactly $T_m v_j$, so the correction subtracts the
interpolant $P v_j = c^2 w_j - s^2 w_{2m-j}$. -/
theorem modelCoarseCorrection_mulVec_sineVec (j : Fin m) :
    modelCoarseCorrection m *ᵥ sineVec (2 * m + 1) (fineIndex j) =
      Real.sin (modeAngle m j / 2) ^ 2 •
        (sineVec (2 * m + 1) (fineIndex j) + sineVec (2 * m + 1) (aliasIndex j)) := by
  have h : ((4 : ℝ) • fullWeighting m) *ᵥ
      (symmTridiagonalToeplitz (2 * m + 1) (-1) 2 *ᵥ sineVec (2 * m + 1) (fineIndex j)) =
      symmTridiagonalToeplitz m (-1) 2 *ᵥ sineVec m j := by
    rw [symmTridiagonalToeplitz_mulVec_sineVec_fineIndex,
      symmTridiagonalToeplitz_mulVec_sineVec_coarse, mulVec_smul, smul_mulVec,
      fullWeighting_mulVec_sineVec, smul_smul, smul_smul]
    congr 1
    ring
  rw [modelCoarseCorrection_mulVec, h, inv_mulVec_mulVec_coarse,
    linearInterpolation_mulVec_sineVec]
  have hcs := Real.sin_sq_add_cos_sq (modeAngle m j / 2)
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-sineVec (2 * m + 1) (fineIndex j) i) * hcs

/-- Let $0 \le j < m$ and $c = \cos(\theta_j/2)$. The exact coarse-grid correction maps the alias
$w_{2m-j}$ to
$$E w_{2m-j} = c^2 (w_j + w_{2m-j}).$$

This is (11.6.21) of Theorem 11.6.2 of [golub2013matrix]. The restricted residual is $-T_m v_j$,
so the correction adds the interpolant $P v_j$. -/
theorem modelCoarseCorrection_mulVec_sineVec_aliasIndex (j : Fin m) :
    modelCoarseCorrection m *ᵥ sineVec (2 * m + 1) (aliasIndex j) =
      Real.cos (modeAngle m j / 2) ^ 2 •
        (sineVec (2 * m + 1) (fineIndex j) + sineVec (2 * m + 1) (aliasIndex j)) := by
  have h : ((4 : ℝ) • fullWeighting m) *ᵥ
      (symmTridiagonalToeplitz (2 * m + 1) (-1) 2 *ᵥ sineVec (2 * m + 1) (aliasIndex j)) =
      symmTridiagonalToeplitz m (-1) 2 *ᵥ (-sineVec m j) := by
    rw [symmTridiagonalToeplitz_mulVec_sineVec_aliasIndex, mulVec_neg,
      symmTridiagonalToeplitz_mulVec_sineVec_coarse, mulVec_smul, smul_mulVec,
      fullWeighting_mulVec_sineVec_aliasIndex, smul_smul, smul_smul, ← neg_smul]
    congr 1
    ring
  rw [modelCoarseCorrection_mulVec, h, inv_mulVec_mulVec_coarse, mulVec_neg,
    linearInterpolation_mulVec_sineVec]
  have hcs := Real.sin_sq_add_cos_sq (modeAngle m j / 2)
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-sineVec (2 * m + 1) (aliasIndex j) i) * hcs

/-- The exact coarse-grid correction fixes the middle fine mode: $E w_m = w_m$, because full
weighting annihilates $w_m$.

This is (11.6.22) of Theorem 11.6.2 of [golub2013matrix]. -/
theorem modelCoarseCorrection_mulVec_sineVec_middleIndex :
    modelCoarseCorrection m *ᵥ sineVec (2 * m + 1) (middleIndex m) =
      sineVec (2 * m + 1) (middleIndex m) := by
  rw [modelCoarseCorrection_mulVec, symmTridiagonalToeplitz_mulVec_sineVec, mulVec_smul,
    smul_mulVec, fullWeighting_mulVec_sineVec_middleIndex, smul_zero, smul_zero,
    mulVec_zero, mulVec_zero, sub_zero]

/-! ### The bridge to the abstract two-grid theory -/

/-- The exact coarse-grid correction of the model problem is the abstract coarse-grid correction. As
a linear map on $\mathbb{R}^{2m+1}$ with the Euclidean inner product,
$E = I - P\, T_m^{-1} (4R)\, T_{2m+1}$ equals the coarse-grid correction $I - Q$ for the
symmetric positive definite matrix $A = T_{2m+1}$ and the prolongation $P$, where $Q$ is the
$A$-orthogonal projector onto $\operatorname{range} P$.

This is the statement of [golub2013matrix], §11.6.4. The coarse solve of the correction is the
Galerkin one, because $P^T = 2R$ and $R\, T_{2m+1} P = \frac{1}{4} T_m$
(`Multigrid.fullWeighting_mul_mul_linearInterpolation`). The matrices act through
`Matrix.toEuclideanLin`, and the abstract correction is `Multigrid.coarseCorrection`. -/
theorem toEuclideanLin_modelCoarseCorrection :
    toEuclideanLin (modelCoarseCorrection m) =
      coarseCorrection (toEuclideanLin (symmTridiagonalToeplitz (2 * m + 1) (-1) 2))
        (posDef_symmTridiagonalToeplitz_neg_one_two (2 * m + 1)).isSymmetricCoercive_toEuclideanLin
        (toEuclideanLin (linearInterpolation m)) := by
  set T := symmTridiagonalToeplitz (2 * m + 1) (-1) 2
  set Tm := symmTridiagonalToeplitz m (-1) 2
  have hPT : (linearInterpolation m)ᵀ = (2 : ℝ) • fullWeighting m := by
    rw [fullWeighting, smul_smul]
    norm_num
  have hTm : IsUnit Tm.det := (posDef_symmTridiagonalToeplitz_neg_one_two m).isUnit.map detMonoidHom
  have key : (2 : ℝ) • fullWeighting m * (T * (linearInterpolation m *
      (Tm⁻¹ * ((4 : ℝ) • fullWeighting m) * T))) = (2 : ℝ) • fullWeighting m * T := by
    have hG : fullWeighting m * T * linearInterpolation m * Tm⁻¹ = (1 / 4 : ℝ) • 1 := by
      rw [fullWeighting_mul_mul_linearInterpolation, Matrix.smul_mul, mul_nonsing_inv _ hTm]
    calc _ = ((4 : ℝ) * 2) • ((fullWeighting m * T * linearInterpolation m * Tm⁻¹) *
          (fullWeighting m * T)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, smul_smul]
      _ = _ := by
          rw [hG, Matrix.smul_mul, Matrix.one_mul, smul_smul, Matrix.smul_mul]
          norm_num
  ext1 x
  rw [coarseCorrection_apply]
  have hy : galerkinCoarse (toEuclideanLin T) (toEuclideanLin (linearInterpolation m))
      (toEuclideanLin (Tm⁻¹ * ((4 : ℝ) • fullWeighting m) * T) x) =
      LinearMap.adjoint (toEuclideanLin (linearInterpolation m)) (toEuclideanLin T x) := by
    rw [galerkinCoarse_apply, ← toEuclideanLin_conjTranspose_eq_adjoint,
      conjTranspose_eq_transpose_of_trivial, hPT]
    simp only [← toEuclideanLin_mul_apply]
    rw [key]
  rw [coarseProjection_apply_eq _ _ _ hy, ← toEuclideanLin_mul_apply, modelCoarseCorrection,
    map_sub, toEuclideanLin_one, LinearMap.sub_apply, LinearMap.id_apply]
  simp only [Matrix.mul_assoc]
  rfl

end Multigrid
