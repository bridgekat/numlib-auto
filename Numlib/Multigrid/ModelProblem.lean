import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz
import Numlib.Multigrid.Basic

/-!
# The one-dimensional model problem of two-grid analysis

The transfer operators between a fine grid of `2m + 1` interior points and the coarse grid of the
`m` interior points obtained by dropping every other one — **linear interpolation**
`Multigrid.linearInterpolation m` and **full weighting** `Multigrid.fullWeighting m` — and their
action on the discrete sine modes of `Numlib/LinearAlgebra/Matrix/TridiagonalToeplitz`. This is the
standard Fourier analysis of the two-grid method for the second-difference matrix
`T_k = tridiag(-1, 2, -1)` (`Matrix.symmTridiagonalToeplitz k (-1) 2`), stated without the mesh
width `h = 1/(2m + 2)`: a surface puts it back as `A^h = h⁻² T_{2m+1}`, `A^{2h} = (2h)⁻² T_m`.

## Conventions

Indices are `0`-based: fine points `i : Fin (2m + 1)`, coarse points `j : Fin m`, and coarse point
`j` is fine point `2j + 1`. The fine sine mode `l` and its *alias* `2m - l` agree up to sign at the
coarse points (`Multigrid.sineVec_aliasIndex`), and the middle mode `m` vanishes there. With
`θ = Multigrid.modeAngle m j = (j + 1)π/(2m + 2)`, the angle of fine mode `j`, the constants are
`c = cos(θ/2)` and `s = sin(θ/2)`.

## Main results

* `Multigrid.fullWeighting_mul_mul_linearInterpolation`, the **Galerkin identity**
  `R T_{2m+1} P = ¼ T_m`: with the mesh scaling, `R A^h P = A^{2h}`.
* `Multigrid.linearInterpolation_mulVec_sineVec`: interpolation of the coarse mode `j` excites the
  fine mode `j` and its alias, `P v_j = c² w_j - s² w_{2m-j}`.
* `Multigrid.fullWeighting_mulVec_sineVec` and its siblings: restriction of the three kinds of fine
  modes, `R w_j = c² v_j`, `R w_{2m-j} = -s² v_j` and `R w_m = 0`. The general entrywise formula is
  `Multigrid.fullWeighting_mulVec_sineVec_apply`.
* `Multigrid.modelCoarseCorrection_mulVec_sineVec` and its siblings: the exact coarse-grid
  correction `E = 1 - P T_m⁻¹ (4R) T_{2m+1}` maps `w_j ↦ s² (w_j + w_{2m-j})`,
  `w_{2m-j} ↦ c² (w_j + w_{2m-j})` and fixes `w_m`, so it
  annihilates the smooth part of each mode pair as `s → 0`.

The Galerkin identity is proved on the sine basis: both sides act on the coarse mode `j` as
multiplication by `4 s² c² = sin² θ`, and two matrices that agree on every coarse sine mode are
equal because the sine matrix squares to a nonzero multiple of the identity.

## References

[golub2013matrix] §11.6.3–11.6.4, Lemma 11.6.1 and Theorem 11.6.2; [saad2003iterative] §13.3,
(13.30)–(13.35), and Example 13.7.
-/

open Matrix Real
open scoped Matrix

namespace Multigrid

variable {m : ℕ}

/-! ### The transfer operators -/

/-- **Linear interpolation** from the `m` interior points of the coarse grid to the `2m + 1`
interior points of the fine grid. Column `j` carries the stencil `½ [1 2 1]` on the fine rows
`2j, 2j + 1, 2j + 2`: the fine point `2j + 1` is the coarse point `j` and takes its value, and the
two fine points either side of it take the average of their coarse neighbours, a neighbour outside
`Fin m` being the boundary value `0`. -/
noncomputable def linearInterpolation (m : ℕ) : Matrix (Fin (2 * m + 1)) (Fin m) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = 2 * (j : ℕ) + 1 then 1
    else if (i : ℕ) = 2 * (j : ℕ) then 1 / 2
    else if (i : ℕ) = 2 * (j : ℕ) + 2 then 1 / 2
    else 0

/-- The entries of the interpolation matrix. -/
theorem linearInterpolation_apply (i : Fin (2 * m + 1)) (j : Fin m) :
    linearInterpolation m i j =
      if (i : ℕ) = 2 * (j : ℕ) + 1 then 1
      else if (i : ℕ) = 2 * (j : ℕ) then 1 / 2
      else if (i : ℕ) = 2 * (j : ℕ) + 2 then 1 / 2
      else 0 :=
  rfl

/-- **Full weighting** from the `2m + 1` fine to the `m` coarse interior points, the scaled
transpose `½ Pᵀ` of linear interpolation: row `j` carries the stencil `¼ [1 2 1]` on the fine
columns `2j, 2j + 1, 2j + 2` (`Multigrid.fullWeighting_apply`). -/
noncomputable def fullWeighting (m : ℕ) : Matrix (Fin m) (Fin (2 * m + 1)) ℝ :=
  (1 / 2 : ℝ) • (linearInterpolation m)ᵀ

/-- The entries of the full-weighting matrix. -/
theorem fullWeighting_apply (j : Fin m) (i : Fin (2 * m + 1)) :
    fullWeighting m j i =
      if (i : ℕ) = 2 * (j : ℕ) + 1 then 1 / 2
      else if (i : ℕ) = 2 * (j : ℕ) then 1 / 4
      else if (i : ℕ) = 2 * (j : ℕ) + 2 then 1 / 4
      else 0 := by
  rw [fullWeighting, Matrix.smul_apply, transpose_apply, linearInterpolation_apply, smul_eq_mul]
  split_ifs <;> norm_num

/-- The entries of the interpolation matrix, as the average of the two coarse grid positions
nearest the fine point: fine point `i` lies between the coarse positions `⌊(i + 1)/2⌋` and
`⌊(i + 2)/2⌋` (counted from the left boundary `0`), which coincide at a coarse point. -/
private theorem linearInterpolation_apply_eq_half (i : Fin (2 * m + 1)) (j : Fin m) :
    linearInterpolation m i j =
      ((if ((i : ℕ) + 1) / 2 = (j : ℕ) + 1 then 1 else 0) +
        (if ((i : ℕ) + 2) / 2 = (j : ℕ) + 1 then 1 else 0)) / 2 := by
  rw [linearInterpolation_apply]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- A coarse vector read at the coarse grid position `K`, the boundary positions `0` and `m + 1`
(and everything beyond) carrying `0`: position `j + 1` is the coarse point `j`. -/
private noncomputable def coarseAt (u : Fin m → ℝ) (K : ℕ) : ℝ :=
  ∑ j : Fin m, if K = (j : ℕ) + 1 then u j else 0

/-- Linear interpolation averages the coarse values at the two coarse grid positions nearest the
fine point. -/
private theorem linearInterpolation_mulVec_apply (u : Fin m → ℝ) (i : Fin (2 * m + 1)) :
    (linearInterpolation m *ᵥ u) i =
      (coarseAt u (((i : ℕ) + 1) / 2) + coarseAt u (((i : ℕ) + 2) / 2)) / 2 := by
  simp only [mulVec, dotProduct, linearInterpolation_apply_eq_half, coarseAt]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- Full weighting is the `¼ [1 2 1]` stencil around the fine point carrying the coarse point. -/
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

/-- The angle `θ = (j + 1)π/(2m + 2)` of the fine sine mode `j`, half the angle of the coarse sine
mode `j`. -/
noncomputable def modeAngle (m : ℕ) (j : Fin m) : ℝ := (((j : ℕ) : ℝ) + 1) * π / (2 * m + 2)

/-- The fine index of the coarse mode `j`: the fine mode of the same frequency. -/
def fineIndex (j : Fin m) : Fin (2 * m + 1) := ⟨j, by have := j.isLt; omega⟩

/-- The alias `2m - j` of the fine mode `j`: the fine mode that agrees with it up to sign at the
coarse points. -/
def aliasIndex (j : Fin m) : Fin (2 * m + 1) := ⟨2 * m - j, by omega⟩

/-- The middle fine mode `m`, which vanishes at every coarse point. -/
def middleIndex (m : ℕ) : Fin (2 * m + 1) := ⟨m, by omega⟩

/-- The mode angle is positive. -/
theorem modeAngle_pos (j : Fin m) : 0 < modeAngle m j := by
  rw [modeAngle]
  positivity

/-- The mode angle is below `π/2`, so `sin (θ/2)` and `cos (θ/2)` are positive. -/
theorem modeAngle_lt_pi_div_two (j : Fin m) : modeAngle m j < π / 2 := by
  have hj : ((j : ℕ) : ℝ) + 1 ≤ m := by
    have := j.isLt
    exact_mod_cast this
  rw [modeAngle, div_lt_div_iff₀ (by positivity) two_pos]
  nlinarith [Real.pi_pos]

/-- The fine mode `j` has the angle `θ`. -/
theorem sineVec_fineIndex (j : Fin m) (i : Fin (2 * m + 1)) :
    sineVec (2 * m + 1) (fineIndex j) i = Real.sin ((((i : ℕ) : ℝ) + 1) * modeAngle m j) := by
  rw [sineVec_apply, modeAngle, fineIndex]
  push_cast
  ring_nf

/-- The coarse mode `j` has the angle `2θ`. -/
theorem sineVec_coarse (j q : Fin m) :
    sineVec m j q = Real.sin ((((q : ℕ) : ℝ) + 1) * (2 * modeAngle m j)) := by
  rw [sineVec_apply, modeAngle]
  congr 1
  field_simp

/-- The alias `2m - j` of the fine mode `j` is the fine mode with the signs alternated, because
its angle is `π - θ`. -/
theorem sineVec_aliasIndex (j : Fin m) (i : Fin (2 * m + 1)) :
    sineVec (2 * m + 1) (aliasIndex j) i =
      (-1) ^ (i : ℕ) * sineVec (2 * m + 1) (fineIndex j) i := by
  rw [sineVec_fineIndex, sineVec_apply, aliasIndex]
  have hj : (j : ℕ) ≤ 2 * m := by have := j.isLt; omega
  have hang : ((((2 * m - j : ℕ) : ℕ) : ℝ) + 1) * π / (((2 * m + 1 : ℕ) : ℝ) + 1)
      = π - modeAngle m j := by
    rw [Nat.cast_sub hj, modeAngle]
    push_cast
    field_simp
    ring
  rw [hang, show ((((i : ℕ) : ℝ) + 1) * (π - modeAngle m j))
      = (((i : ℕ) + 1 : ℕ) : ℝ) * π - (((i : ℕ) : ℝ) + 1) * modeAngle m j by push_cast; ring,
    Real.sin_sub, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
  ring

/-- The middle fine mode has the angle `π/2`. -/
theorem sineVec_middleIndex (i : Fin (2 * m + 1)) :
    sineVec (2 * m + 1) (middleIndex m) i = Real.sin ((((i : ℕ) : ℝ) + 1) * (π / 2)) := by
  rw [sineVec_apply, middleIndex]
  congr 1
  push_cast
  field_simp
  ring

/-- A coarse sine mode read at a coarse grid position, boundaries included: position `K` carries
`sin (K · 2θ)`, which vanishes at `K = 0` and at `K = m + 1`. -/
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
        Finset.sum_eq_zero fun b _ => ite_eq_right fun h => by have := b.isLt; omega
      rw [hsum, modeAngle]
      have hrw : ((k + 1 : ℕ) : ℝ) * (2 * ((((j : ℕ) : ℝ) + 1) * π / (2 * k + 2)))
          = (((j : ℕ) + 1 : ℕ) : ℝ) * π := by
        push_cast
        field_simp
      rw [hrw, Real.sin_nat_mul_pi]

/-- `cos θ = c² - s²` and `c² + s² = 1`, for `c = cos (θ/2)`, `s = sin (θ/2)`. -/
private theorem cos_eq_cos_sq_half_sub (θ : ℝ) :
    Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
  have h := Real.cos_two_mul (θ / 2)
  have h2 := Real.sin_sq_add_cos_sq (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h
  linarith

/-! ### Interpolation and restriction of the sine modes -/

/-- **Interpolation of a coarse sine mode** ([golub2013matrix] Lemma 11.6.1, first identity): the
coarse mode `j` is interpolated to a combination of the fine mode `j` and its alias `2m - j`,
`P v_j = c² w_j - s² w_{2m-j}` with `c = cos (θ/2)`, `s = sin (θ/2)`, `θ = (j + 1)π/(2m + 2)`.

At a coarse point both fine modes equal the coarse one up to the sign of the alias, and
`c² + s² = 1`; at a fine point between two coarse points the average `½ (v_{q-1} + v_q)` is
`cos θ` times the fine mode, and `c² - s² = cos θ`. -/
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

/-- **Full weighting of a fine sine mode**, entrywise ([saad2003iterative] Example 13.7): for the
fine mode `l` with angle `φ = (l + 1)π/(2m + 2)`, `(R w_l)_q = cos²(φ/2) sin(2(q + 1)φ)`. The
`¼ [1 2 1]` stencil meets `sin((2q + 1)φ) + sin((2q + 3)φ) = 2 sin((2q + 2)φ) cos φ`, and
`(1 + cos φ)/2 = cos²(φ/2)`. -/
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

/-- **Restriction of the fine mode `j`** ([golub2013matrix] Lemma 11.6.1, second identity):
`R w_j = c² v_j`. -/
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

/-- **Restriction of the alias `2m - j`** ([golub2013matrix] Lemma 11.6.1, second identity):
`R w_{2m-j} = -s² v_j`, the same coarse mode as the fine mode `j` with the other weight. -/
theorem fullWeighting_mulVec_sineVec_aliasIndex (j : Fin m) :
    fullWeighting m *ᵥ sineVec (2 * m + 1) (aliasIndex j) =
      -(Real.sin (modeAngle m j / 2) ^ 2) • sineVec m j := by
  funext q
  rw [fullWeighting_mulVec_sineVec_apply, Pi.smul_apply, smul_eq_mul, sineVec_coarse]
  have hj : (j : ℕ) ≤ 2 * m := by have := j.isLt; omega
  have h : (((aliasIndex j : ℕ) : ℝ) + 1) * π / (((2 * m + 1 : ℕ) : ℝ) + 1)
      = π - modeAngle m j := by
    rw [aliasIndex, modeAngle, Fin.val_mk, Nat.cast_sub hj]
    push_cast
    field_simp
    ring
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

/-- **The middle fine mode is invisible on the coarse grid**: `R w_m = 0`. -/
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

/-- The discrete sine vectors are symmetric in the mode and the point. -/
private theorem sineVec_comm {n : ℕ} (k l : Fin n) : sineVec n k l = sineVec n l k := by
  rw [sineVec_apply, sineVec_apply]
  ring_nf

/-- Two matrices that agree on every sine mode are equal: the sine matrix squares to `(n + 1)/2`
times the identity, by the orthogonality of the sine modes. -/
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

/-- The second-difference matrix on the fine grid scales the fine mode `j` by `4 s²`. -/
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

/-- The second-difference matrix on the fine grid scales the alias `2m - j` by `4 c²`. -/
private theorem symmTridiagonalToeplitz_mulVec_sineVec_aliasIndex (j : Fin m) :
    symmTridiagonalToeplitz (2 * m + 1) (-1) 2 *ᵥ sineVec (2 * m + 1) (aliasIndex j) =
      (4 * Real.cos (modeAngle m j / 2) ^ 2) • sineVec (2 * m + 1) (aliasIndex j) := by
  rw [symmTridiagonalToeplitz_mulVec_sineVec]
  congr 1
  have hj : (j : ℕ) ≤ 2 * m := by have := j.isLt; omega
  have h : (((aliasIndex j : ℕ) : ℝ) + 1) * π / (((2 * m + 1 : ℕ) : ℝ) + 1)
      = π - modeAngle m j := by
    rw [aliasIndex, modeAngle, Fin.val_mk, Nat.cast_sub hj]
    push_cast
    field_simp
    ring
  rw [h, Real.cos_pi_sub, cos_eq_cos_sq_half_sub]
  linear_combination (-2 : ℝ) * Real.sin_sq_add_cos_sq (modeAngle m j / 2)

/-- The second-difference matrix on the coarse grid scales the coarse mode `j` by
`4 sin² θ = 16 s² c²`. -/
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

/-- **The Galerkin identity of the model problem**: `R T_{2m+1} P = ¼ T_m`, so that with
`A^h = h⁻² T_{2m+1}` and `A^{2h} = (2h)⁻² T_m` the coarse matrix is the Galerkin one,
`R A^h P = A^{2h}` ([golub2013matrix] §11.6.3). Both sides multiply the coarse mode `j` by
`4 s² c²`: interpolation gives `c² w_j - s² w_{2m-j}`, the fine matrix scales the two fine modes by
`4 s²` and `4 c²`, and restriction returns `c² v_j` and `-s² v_j`. -/
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

/-- The exact coarse-grid correction of the model problem, `E = 1 - P T_m⁻¹ (4R) T_{2m+1}`: the
book's `E^h = I - P (A^{2h})⁻¹ R A^h` after the scaling `A^h = h⁻² T_{2m+1}`,
`A^{2h} = (2h)⁻² T_m` ([golub2013matrix] (11.6.20)). -/
noncomputable def modelCoarseCorrection (m : ℕ) : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ :=
  1 - linearInterpolation m * (symmTridiagonalToeplitz m (-1) 2)⁻¹ * ((4 : ℝ) • fullWeighting m) *
    symmTridiagonalToeplitz (2 * m + 1) (-1) 2

/-- The coarse second-difference matrix is invertible. -/
private theorem inv_mulVec_mulVec_coarse (v : Fin m → ℝ) :
    (symmTridiagonalToeplitz m (-1) 2)⁻¹ *ᵥ (symmTridiagonalToeplitz m (-1) 2 *ᵥ v) = v := by
  have hdet : IsUnit (symmTridiagonalToeplitz m (-1) 2).det :=
    (posDef_symmTridiagonalToeplitz_neg_one_two m).isUnit.map Matrix.detMonoidHom
  rw [mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]

/-- The action of the exact coarse-grid correction, through the coarse residual it corrects. -/
private theorem modelCoarseCorrection_mulVec (w : Fin (2 * m + 1) → ℝ) :
    modelCoarseCorrection m *ᵥ w = w - linearInterpolation m *ᵥ
      ((symmTridiagonalToeplitz m (-1) 2)⁻¹ *ᵥ
        (((4 : ℝ) • fullWeighting m) *ᵥ (symmTridiagonalToeplitz (2 * m + 1) (-1) 2 *ᵥ w))) := by
  simp only [modelCoarseCorrection, sub_mulVec, one_mulVec, mulVec_mulVec, Matrix.mul_assoc]

/-- The fine mode `j` under the exact coarse-grid correction
([golub2013matrix] Theorem 11.6.2, (11.6.21)): `E w_j = s² (w_j + w_{2m-j})`. The restricted
residual `4 R T_{2m+1} w_j = 16 s² c² v_j` is exactly `T_m v_j`, so the correction subtracts the
interpolant `P v_j = c² w_j - s² w_{2m-j}`. -/
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

/-- The alias `2m - j` under the exact coarse-grid correction
([golub2013matrix] Theorem 11.6.2, (11.6.21)): `E w_{2m-j} = c² (w_j + w_{2m-j})`. The restricted
residual is `-T_m v_j`, so the correction adds the interpolant `P v_j`. -/
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

/-- The middle mode is fixed by the exact coarse-grid correction
([golub2013matrix] Theorem 11.6.2, (11.6.22)): `E w_m = w_m`, because full weighting annihilates
it. -/
theorem modelCoarseCorrection_mulVec_sineVec_middleIndex :
    modelCoarseCorrection m *ᵥ sineVec (2 * m + 1) (middleIndex m) =
      sineVec (2 * m + 1) (middleIndex m) := by
  rw [modelCoarseCorrection_mulVec, symmTridiagonalToeplitz_mulVec_sineVec, mulVec_smul,
    smul_mulVec, fullWeighting_mulVec_sineVec_middleIndex, smul_zero, smul_zero,
    mulVec_zero, mulVec_zero, sub_zero]

/-! ### The bridge to the abstract two-grid theory -/

/-- **The model correction is the abstract coarse-grid correction.** As an operator on the fine
grid, `E = 1 - P T_m⁻¹ (4R) T_{2m+1}` is `Multigrid.coarseCorrection` of `A = T_{2m+1}` and the
prolongation `P`: the `A`-orthogonal projector complement onto `ran P`
([golub2013matrix] §11.6.4). The coarse solve of the correction is the Galerkin one, because
`Pᵀ = 2R` and `R T_{2m+1} P = ¼ T_m` (`Multigrid.fullWeighting_mul_mul_linearInterpolation`). -/
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
    rw [galerkinCoarse_apply, ← toEuclideanLin_conjTranspose,
      conjTranspose_eq_transpose_of_trivial, hPT]
    simp only [← toEuclideanLin_mul_apply]
    rw [key]
  rw [coarseProjection_apply_eq _ _ _ hy, ← toEuclideanLin_mul_apply, modelCoarseCorrection,
    map_sub, toEuclideanLin_one, LinearMap.sub_apply, LinearMap.id_apply]
  simp only [Matrix.mul_assoc]
  rfl

@[deprecated (since := "2026-09-30")]
alias coarseCorrection_mulVec_sineVec := modelCoarseCorrection_mulVec_sineVec
@[deprecated (since := "2026-09-30")]
alias coarseCorrection_mulVec_sineVec_aliasIndex := modelCoarseCorrection_mulVec_sineVec_aliasIndex
@[deprecated (since := "2026-09-30")]
alias coarseCorrection_mulVec_sineVec_middleIndex :=
  modelCoarseCorrection_mulVec_sineVec_middleIndex

end Multigrid
