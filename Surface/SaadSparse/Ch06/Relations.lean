import SaadSparse.Ch06.FOM
import SaadSparse.Ch06.GMRES

/-!
# Saad, §6.5.7: relations between FOM and GMRES

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003, §6.5.7, together with the problems P-6.9, P-6.13 and P-6.14.

The section compares the two Krylov methods built on the same Arnoldi basis: FOM
(`Ch06/FOM.lean`, the Galerkin iterate) and GMRES (`Ch06/GMRES.lean`, the minimal-residual
iterate). `ρF` and `ρG` are their residual norms, `ξ` the diagonal entry of `Q_{m-1} H̄_m` of
Proposition 6.12, and `Rtilde`, `gtilde`, `ytilde` the "one rotation short" Givens data of
Lemma 6.16 (Freund); `ρFmin` is the book's `ρ^F_{m*}`.

Every numbered result is a specialization. (6.62) and Proposition 6.12 come from the Givens
layer of `Numlib/Krylov/Hessenberg.lean`; Propositions 6.13, 6.15, 6.17, Corollary 6.14 and
(6.74)–(6.75) from the specification-level relations of `Numlib/Krylov/Relations.lean`. Only
Lemma 6.16, whose statement is about the *coordinates* `y_m` rather than about the iterates, is
proved here, by the book's own computation (6.72)–(6.73): `R̃_m` and `R_m` differ in the single
entry `(m, m)`, where the former carries `ξ_m` and the latter `ρ_{m-1} = ξ_m/c_m`.

Statements are over `ℝ`, the book's setting in §6.5; the definitions are polymorphic in `𝕜`.
-/

open scoped Matrix

namespace SaadSparse.Ch06

section General

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### D10: the two residual norms and the Freund data -/

/-- `ρ_m^G = ‖b - A x_m^G‖₂`, the GMRES residual norm after `m` steps (§6.5.7). -/
noncomputable abbrev ρG (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : ℝ :=
  ‖b - op A (gmresFixed A b x₀ m)‖

/-- `ρ_m^F = ‖b - A x_m^F‖₂`, the FOM residual norm after `m` steps; the book's `ρ_m^F` is
meaningful exactly when `H_m` is nonsingular (`FOMDefined`). -/
noncomputable abbrev ρF (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : ℝ :=
  ‖b - op A (fomFixed A b x₀ m)‖

/-- Proposition 6.12: `ξ = (Q_{m-1} H̄_m)_{mm}`, the diagonal entry left by the first `m - 1`
rotations (`0`-based: the `(m-1, m-1)` entry of `H̄^{(m-1)}`). -/
noncomputable def ξ (h : ℕ → ℕ → 𝕜) (m : ℕ) : 𝕜 := Krylov.rotated h (m - 1) (m - 1) (m - 1)

/-- Lemma 6.16: `R̃_m`, the top `m × m` block of `Q_{m-1} H̄_m` — the triangular factor one
rotation short of `R_m`. -/
noncomputable def Rtilde (h : ℕ → ℕ → 𝕜) (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜 :=
  Krylov.hessenbergSqOf (Krylov.rotated h (m - 1)) m

/-- Lemma 6.16: `g̃_m`, the first `m` entries of `Q_{m-1}(β e_1)`. -/
noncomputable def gtilde (h : ℕ → ℕ → 𝕜) (c : 𝕜) (m : ℕ) : Fin m → 𝕜 :=
  fun i => if (i : ℕ) < m - 1 then Krylov.gvec h c (i : ℕ) else Krylov.gamma h c (m - 1)

/-- Lemma 6.16: `ỹ_m = R̃_m⁻¹ g̃_m`, the coordinates of the FOM approximation in the Givens
description of §6.5.3. -/
noncomputable def ytilde (h : ℕ → ℕ → 𝕜) (c : 𝕜) (m : ℕ) : Fin m → 𝕜 :=
  (Rtilde h m)⁻¹ *ᵥ gtilde h c m

theorem Rtilde_apply (h : ℕ → ℕ → 𝕜) {m : ℕ} (i j : Fin m) :
    Rtilde h m i j = Krylov.rotated h (m - 1) (i : ℕ) (j : ℕ) := rfl

theorem gtilde_last (h : ℕ → ℕ → 𝕜) (c : 𝕜) (m : ℕ) :
    gtilde h c (m + 1) (Fin.last m) = Krylov.gamma h c m := by
  rw [gtilde, Nat.add_sub_cancel]
  exact ite_eq_right (by simp)

theorem gtilde_castSucc (h : ℕ → ℕ → 𝕜) (c : 𝕜) {m : ℕ} (i : Fin m) :
    gtilde h c (m + 1) i.castSucc = Krylov.gvec h c (i : ℕ) := by
  rw [gtilde, Nat.add_sub_cancel]
  exact ite_eq_left i.isLt

/-! ### `R̃_m` versus `R_m`

The two triangular factors differ in a single entry, which is the whole content of the book's
block computation (6.72)–(6.73). The unfolding `rotated_succ_apply'` is definitional. -/

private theorem rotated_succ_apply' (h : ℕ → ℕ → 𝕜) (k i j : ℕ) :
    Krylov.rotated h (k + 1) i j =
      if i = k then
        starRingEnd 𝕜 (Krylov.givensC h k) * Krylov.rotated h k k j +
          starRingEnd 𝕜 (Krylov.givensS h k) * Krylov.rotated h k (k + 1) j
      else if i = k + 1 then
        -Krylov.givensS h k * Krylov.rotated h k k j +
          Krylov.givensC h k * Krylov.rotated h k (k + 1) j
      else Krylov.rotated h k i j := rfl

/-- Rotation `k` changes only rows `k` and `k + 1`. -/
private theorem rotated_succ_of_ne (h : ℕ → ℕ → 𝕜) {k i : ℕ} (h1 : i ≠ k) (h2 : i ≠ k + 1)
    (j : ℕ) : Krylov.rotated h (k + 1) i j = Krylov.rotated h k i j := by
  rw [rotated_succ_apply', ite_eq_right h1, ite_eq_right h2]

/-- **(6.72)–(6.73)**: `R_{m+1}` and `R̃_{m+1}` agree except in the entry `(m, m)`, where the
former carries `ρ_m` and the latter the pivot `ξ_{m+1}`. -/
theorem R_mulVec_eq_Rtilde_mulVec_add (h : ℕ → ℕ → 𝕜)
    (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0) (m : ℕ) (v : Fin (m + 1) → 𝕜) :
    R h (m + 1) *ᵥ v = Rtilde h (m + 1) *ᵥ v +
      Pi.single (Fin.last m)
        ((((Krylov.givensRho h m : ℝ) : 𝕜) - Krylov.rotated h m m m) * v (Fin.last m)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply]
  rcases eq_or_ne i (Fin.last m) with rfl | hi
  · rw [Pi.single_eq_same, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have h1 : ∀ j : Fin m, R h (m + 1) (Fin.last m) j.castSucc * v j.castSucc = 0 := by
      intro j
      rw [R_apply, Fin.val_last, Fin.val_castSucc,
        Krylov.rotated_eq_zero_of_lt h hh (m + 1) m (j : ℕ) (by omega) j.isLt, zero_mul]
    have h2 : ∀ j : Fin m, Rtilde h (m + 1) (Fin.last m) j.castSucc * v j.castSucc = 0 := by
      intro j
      rw [Rtilde_apply, Nat.add_sub_cancel, Fin.val_last, Fin.val_castSucc,
        Krylov.rotated_eq_zero_of_lt h hh m m (j : ℕ) j.isLt j.isLt, zero_mul]
    rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_congr rfl (fun j _ => h2 j)]
    rw [R_apply, Rtilde_apply, Nat.add_sub_cancel, Fin.val_last,
      Krylov.rotated_succ_self h m]
    ring
  · have hlt : (i : ℕ) < m := by
      have := i.isLt
      have : (i : ℕ) ≠ m := fun hc => hi (Fin.ext (by simpa using hc))
      omega
    rw [Pi.single_eq_of_ne hi, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [R_apply, Rtilde_apply, Nat.add_sub_cancel,
      rotated_succ_of_ne h (by omega) (by omega) (j : ℕ)]

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-- Step `0` of FOM is the trivial one: `H_0` is the empty matrix. -/
theorem fomDefined_zero : FOMDefined A b x₀ 0 := by
  rw [FOMDefined, Matrix.isUnit_iff_isUnit_det, Matrix.det_isEmpty]
  exact isUnit_one

open scoped Classical in
/-- Proposition 6.15: `ρ^F_{m*}`, the smallest FOM residual norm reached in the first `m` steps,
the steps with a singular `H_i` being skipped. -/
noncomputable def ρFmin (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : ℝ :=
  ((Finset.range (m + 1)).filter (FOMDefined A b x₀)).inf'
    ⟨0, Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.succ_pos m), fomDefined_zero A b x₀⟩⟩
    (ρF A b x₀)

/-! ### Nonsingularity of `R_m` and `R̃_m` -/

/-- The Arnoldi coefficients are Hessenberg, the standing hypothesis of the Givens layer. -/
theorem arnoldiCoeff_hessenberg :
    ∀ i j : ℕ, j + 1 < i → arnoldiCoeff A (v₁ A b x₀) i j = 0 :=
  fun _ _ hij => arnoldiCoeff_v₁_eq_zero_of_lt A b x₀ hij

/-- Below the grade no rotation degenerates, so `R_m` is nonsingular with no hypothesis on
`A`. -/
theorem isUnit_R_of_lt_grade {m : ℕ} (hm : m < grade A (v₁ A b x₀)) :
    IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m) := by
  refine (isUnit_R_iff _ (arnoldiCoeff_hessenberg A b x₀)).2 fun k hk => ?_
  rw [arnoldiCoeff_v₁]
  exact Krylov.givensRho_arnoldi_ne_zero (by rw [← grade_v₁]; omega)

/-- A nonsingular `H_{m+1}` gives a nonzero cosine `c_m`
(`Krylov.isUnit_hessenbergSq_iff_givensC_ne_zero`). -/
theorem givensC_ne_zero_of_fomDefined {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ (m + 1)) : c (arnoldiCoeff A (v₁ A b x₀)) m ≠ 0 := by
  rw [arnoldiCoeff_v₁]
  refine (Krylov.isUnit_hessenbergSq_iff_givensC_ne_zero (by rw [← grade_v₁]; exact hm)).1 ?_
  rw [← H_v₁ A b x₀]
  exact hH

/-- The pivot `ξ_{m+1}` is nonzero when `H_{m+1}` is nonsingular. -/
theorem ξ_ne_zero_of_fomDefined {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ (m + 1)) : ξ (arnoldiCoeff A (v₁ A b x₀)) (m + 1) ≠ 0 := by
  rw [ξ, Nat.add_sub_cancel]
  intro h0
  exact givensC_ne_zero_of_fomDefined A b x₀ hm hH
    ((Krylov.givensC_eq_zero_iff (arnoldiCoeff A (v₁ A b x₀)) m).2 h0)

/-- `ρ_m` is nonzero when `H_{m+1}` is nonsingular. -/
theorem givensRho_ne_zero_of_fomDefined {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ (m + 1)) :
    Krylov.givensRho (arnoldiCoeff A (v₁ A b x₀)) m ≠ 0 := by
  refine Krylov.givensRho_ne_zero_of_rotated_ne_zero _ ?_
  have := ξ_ne_zero_of_fomDefined A b x₀ hm hH
  rwa [ξ, Nat.add_sub_cancel] at this

/-- `R_m` is nonsingular as soon as `m` Arnoldi steps have been taken and `H_m` is nonsingular:
the earlier rotations are nondegenerate below the grade, the last one because its pivot is
`ξ_m ≠ 0`. -/
theorem isUnit_R_of_fomDefined {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ m) : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m) := by
  refine (isUnit_R_iff _ (arnoldiCoeff_hessenberg A b x₀)).2 fun k hk => ?_
  rcases Nat.lt_or_ge (k + 1) m with h1 | h1
  · rw [arnoldiCoeff_v₁]
    exact Krylov.givensRho_arnoldi_ne_zero (by rw [← grade_v₁]; omega)
  · have hkm : m = k + 1 := by omega
    subst hkm
    exact givensRho_ne_zero_of_fomDefined A b x₀ hm hH

/-- `R̃_{m+1}` is nonsingular under the same hypotheses: its diagonal is `ρ_0, …, ρ_{m-1}, ξ`. -/
theorem isUnit_Rtilde_of_fomDefined {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ (m + 1)) :
    IsUnit (Rtilde (arnoldiCoeff A (v₁ A b x₀)) (m + 1)) := by
  rw [Rtilde, Nat.add_sub_cancel]
  refine Krylov.isUnit_hessenbergSqOf_rotated _ (arnoldiCoeff_hessenberg A b x₀)
    (le_refl (m + 1)) fun j hj => ?_
  rcases Nat.lt_or_ge j m with h1 | h1
  · rw [Krylov.rotated_diag _ (arnoldiCoeff_hessenberg A b x₀) h1]
    have hρ : Krylov.givensRho (arnoldiCoeff A (v₁ A b x₀)) j ≠ 0 := by
      rw [arnoldiCoeff_v₁]
      exact Krylov.givensRho_arnoldi_ne_zero (by rw [← grade_v₁]; omega)
    simpa using hρ
  · have hjm : j = m := by omega
    subst hjm
    have := ξ_ne_zero_of_fomDefined A b x₀ hm hH
    rwa [ξ, Nat.add_sub_cancel] at this

/-! ### The two iterates as backbone specifications -/

/-- The GMRES residual norm is `|γ_{m+1}|` (6.42), the form used throughout §6.5.7. -/
theorem ρG_eq_norm_gamma {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    ρG A b x₀ m = ‖γ (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m‖ :=
  eq_6_42 A b x₀ hm hR

/-- Algorithm 6.9 computes the minimal-residual iterate at every step below the grade. -/
theorem gmresFixed_isMinResIterate_of_lt {m : ℕ} (hm : m < grade A (v₁ A b x₀)) :
    Krylov.IsMinResIterate (op A) b x₀ m (gmresFixed A b x₀ m) :=
  gmresFixed_isMinResIterate A b x₀ hm.le (isUnit_R_of_lt_grade A b x₀ hm)

/-- Algorithm 6.4 computes the Galerkin iterate whenever `H_m` is nonsingular. -/
theorem fomFixed_isGalerkin {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ m) :
    Krylov.IsGalerkinIterate (op A) b x₀ m (fomFixed A b x₀ m) :=
  fomFixed_isGalerkinIterate A b x₀ hH hm

/-- `ρ_m^G ≤ ρ_m^F`: the two iterates minimize over the same affine space. -/
theorem ρG_le_ρF {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (hH : FOMDefined A b x₀ m)
    (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) : ρG A b x₀ m ≤ ρF A b x₀ m :=
  Krylov.norm_residual_minRes_le_galerkin (gmresFixed_isMinResIterate A b x₀ hm hR)
    (fomFixed_isGalerkin A b x₀ hm hH)

/-- The GMRES residual norms are nonincreasing (`𝒦_m ⊆ 𝒦_{m+1}`). -/
theorem ρG_succ_le {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) (m + 1))) :
    ρG A b x₀ (m + 1) ≤ ρG A b x₀ m :=
  IsMinRes.norm_residual_le (gmresFixed_isMinResIterate_of_lt A b x₀ (by omega))
    (gmresFixed_isMinResIterate A b x₀ hm hR)
    (Krylov.subspace_mono (op A) (b - op A x₀) (Nat.le_succ m))

/-- The padded GMRES vector `(y_m; 0)` solves the system of step `m + 1` except in its last
entry, which it misses entirely: this is the book's remark that `R_{m+1}` acquires one new row
and one new column. -/
theorem R_mulVec_snoc (h : ℕ → ℕ → 𝕜) (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0) (t : 𝕜) {m : ℕ}
    (yp : Fin m → 𝕜) (hyp : R h m *ᵥ yp = g h t m) :
    R h (m + 1) *ᵥ (Fin.snoc yp (0 : 𝕜) : Fin (m + 1) → 𝕜)
      = g h t (m + 1) - Pi.single (Fin.last m) (Krylov.gvec h t m) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.sub_apply]
  rw [Fin.sum_univ_castSucc, Fin.snoc_last, mul_zero, add_zero]
  rcases eq_or_ne i (Fin.last m) with rfl | hi
  · rw [Pi.single_eq_same, g_apply, Fin.val_last, sub_self]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [R_apply, Fin.val_last, Fin.val_castSucc,
      Krylov.rotated_eq_zero_of_lt h hh (m + 1) m (j : ℕ) (by omega) j.isLt, zero_mul]
  · have hlt : (i : ℕ) < m := by
      have := i.isLt
      have : (i : ℕ) ≠ m := fun hc => hi (Fin.ext (by simpa using hc))
      omega
    rw [Pi.single_eq_of_ne hi, sub_zero]
    have hrow : ∀ j : Fin m, R h (m + 1) i j.castSucc *
        (Fin.snoc yp (0 : 𝕜) : Fin (m + 1) → 𝕜) j.castSucc
        = R h m ⟨(i : ℕ), hlt⟩ j * yp j := by
      intro j
      rw [Fin.snoc_castSucc, R_apply, R_apply, Fin.val_castSucc,
        Krylov.rotated_succ_eq_of_lt h hh m (j : ℕ) j.isLt (i : ℕ)]
    rw [Finset.sum_congr rfl fun j _ => hrow j]
    have hval := congrFun hyp ⟨(i : ℕ), hlt⟩
    simp only [Matrix.mulVec, dotProduct] at hval
    rw [hval, g_apply, g_apply]

open scoped Classical in
/-- `ρ^F_{m*}` is at most any FOM residual norm of the first `m` steps. -/
theorem ρFmin_le {m i : ℕ} (hi : i ≤ m) (hH : FOMDefined A b x₀ i) :
    ρFmin A b x₀ m ≤ ρF A b x₀ i := by
  rw [ρFmin]
  exact Finset.inf'_le _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hH⟩)

open scoped Classical in
/-- A lower bound for every FOM step of the first `m` bounds `ρ^F_{m*}` from below. -/
theorem le_ρFmin {m : ℕ} {r : ℝ} (h : ∀ i ≤ m, FOMDefined A b x₀ i → r ≤ ρF A b x₀ i) :
    r ≤ ρFmin A b x₀ m := by
  rw [ρFmin]
  refine Finset.le_inf' _ _ fun i hi => ?_
  obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi
  exact h i (by have := Finset.mem_range.1 hi1; omega) hi2

end General

/-! ### The numbered results of §6.5.7, in the book's real setting -/

section BookResults

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n))

/-! #### (6.62) -/

/-- **(6.62)**: `ρ_{m+1}^G = |s_{m+1}| ρ_m^G`. -/
theorem ρG_succ {m : ℕ} (hm : m + 1 < grade A (v₁ A b x₀)) :
    ρG A b x₀ (m + 1) = ‖s (arnoldiCoeff A (v₁ A b x₀)) m‖ * ρG A b x₀ m := by
  rw [arnoldiCoeff_v₁]
  exact Krylov.IsMinResIterate.norm_residual_succ_eq (by rw [← grade_v₁]; exact hm)
    (gmresFixed_isMinResIterate_of_lt A b x₀ (by omega))
    (gmresFixed_isMinResIterate_of_lt A b x₀ hm)

/-- **(6.62)**: `ρ_m^G = |s_1 s_2 ⋯ s_m| β`. -/
theorem eq_6_62 {m : ℕ} (hm : m < grade A (v₁ A b x₀)) :
    ρG A b x₀ m
      = (∏ i ∈ Finset.range m, ‖s (arnoldiCoeff A (v₁ A b x₀)) i‖) * β A b x₀ := by
  rw [ρG_eq_norm_gamma A b x₀ hm.le (isUnit_R_of_lt_grade A b x₀ hm), norm_gamma_eq_prod,
    RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]

/-! #### Proposition 6.12 (Brown) and (6.63) -/

/-- **Proposition 6.12**, first form: `ρ_{m+1}^F = ρ_{m+1}^G/|c_{m+1}|`. -/
theorem ρF_eq_div_norm_c {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ (m + 1)) :
    ρF A b x₀ (m + 1) = ρG A b x₀ (m + 1) / ‖c (arnoldiCoeff A (v₁ A b x₀)) m‖ := by
  rw [arnoldiCoeff_v₁]
  exact Krylov.IsGalerkinIterate.norm_residual_eq_div_norm_givensC
    (by rw [← grade_v₁]; exact hm) (fomFixed_isGalerkin A b x₀ hm hH)
    (gmresFixed_isMinResIterate A b x₀ hm (isUnit_R_of_fomDefined A b x₀ hm hH))

/-- The subdiagonal Arnoldi entry survives the first `m` rotations unchanged. -/
private theorem rotated_succ_row (h : ℕ → ℕ → ℝ) (m : ℕ) :
    Krylov.rotated h m (m + 1) m = h (m + 1) m :=
  Krylov.rotated_eq_of_le h m (m + 1) m le_rfl

/-- **(6.63)**: `ρ_{m+1}^F = ρ_{m+1}^G √(1 + h_{m+2,m+1}²/ξ²)`. -/
theorem eq_6_63 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ (m + 1)) :
    ρF A b x₀ (m + 1) = ρG A b x₀ (m + 1) *
      Real.sqrt (1 + arnoldiCoeff A (v₁ A b x₀) (m + 1) m ^ 2 /
        ξ (arnoldiCoeff A (v₁ A b x₀)) (m + 1) ^ 2) := by
  set h := arnoldiCoeff A (v₁ A b x₀) with hdef
  have hξ : ξ h (m + 1) = Krylov.rotated h m m m := by rw [ξ, Nat.add_sub_cancel]
  have hξ0 : Krylov.rotated h m m m ≠ 0 := by
    have := ξ_ne_zero_of_fomDefined A b x₀ hm hH
    rwa [hξ] at this
  have hρ0 : Krylov.givensRho h m ≠ 0 := givensRho_ne_zero_of_fomDefined A b x₀ hm hH
  have hρpos : 0 < Krylov.givensRho h m :=
    lt_of_le_of_ne (Krylov.givensRho_nonneg h m) (Ne.symm hρ0)
  have hsq : Krylov.givensRho h m ^ 2 = Krylov.rotated h m m m ^ 2 + h (m + 1) m ^ 2 := by
    rw [Krylov.givensRho_sq, rotated_succ_row, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
      sq_abs]
  have hc : ‖c h m‖ = |Krylov.rotated h m m m| / Krylov.givensRho h m := by
    rw [show c h m = Krylov.givensC h m from rfl, Krylov.givensC, norm_div,
      RCLike.norm_ofReal, abs_of_nonneg (Krylov.givensRho_nonneg h m), Real.norm_eq_abs]
  have hcne : ‖c h m‖ ≠ 0 := by
    rw [hc]
    exact div_ne_zero (abs_ne_zero.2 hξ0) hρ0
  have habs : (0 : ℝ) < |Krylov.rotated h m m m| := abs_pos.2 hξ0
  have hkey : Real.sqrt (1 + h (m + 1) m ^ 2 / ξ h (m + 1) ^ 2) = 1 / ‖c h m‖ := by
    rw [hξ, hc, one_div_div]
    rw [show (1 : ℝ) + h (m + 1) m ^ 2 / Krylov.rotated h m m m ^ 2
        = (Krylov.givensRho h m / |Krylov.rotated h m m m|) ^ 2 by
      rw [div_pow, sq_abs, hsq]
      field_simp]
    exact Real.sqrt_sq (by positivity)
  rw [ρF_eq_div_norm_c A b x₀ hm hH, hkey, ← hdef, div_eq_mul_one_div]

/-- **Proposition 6.12** (Brown), as stated in the book: if `m ≥ 1` Arnoldi steps have been
taken and `H_m` is nonsingular, then `c_m ≠ 0` and
`ρ_m^F = ρ_m^G/|c_m| = ρ_m^G √(1 + h_{m+1,m}²/ξ²)`. -/
theorem prop_6_12 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (hm0 : 0 < m)
    (hH : FOMDefined A b x₀ m) :
    c (arnoldiCoeff A (v₁ A b x₀)) (m - 1) ≠ 0 ∧
      ρF A b x₀ m = ρG A b x₀ m / ‖c (arnoldiCoeff A (v₁ A b x₀)) (m - 1)‖ ∧
        ρF A b x₀ m = ρG A b x₀ m *
          Real.sqrt (1 + arnoldiCoeff A (v₁ A b x₀) m (m - 1) ^ 2 /
            ξ (arnoldiCoeff A (v₁ A b x₀)) m ^ 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact ⟨givensC_ne_zero_of_fomDefined A b x₀ hm hH, ρF_eq_div_norm_c A b x₀ hm hH,
    eq_6_63 A b x₀ hm hH⟩

/-! #### Proposition 6.13 (Cullum–Greenbaum), (6.64)–(6.65) -/

/-- **(6.65)**: `1/(ρ_{m+1}^F)² + 1/(ρ_m^G)² = 1/(ρ_{m+1}^G)²`. -/
theorem eq_6_65 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hH : FOMDefined A b x₀ (m + 1))
    (h0 : ρG A b x₀ (m + 1) ≠ 0) :
    1 / ρF A b x₀ (m + 1) ^ 2 + 1 / ρG A b x₀ m ^ 2 = 1 / ρG A b x₀ (m + 1) ^ 2 := by
  have hkey := Krylov.inv_sq_norm_residual_minRes
    (gmresFixed_isMinResIterate_of_lt A b x₀ (by omega))
    (gmresFixed_isMinResIterate A b x₀ hm (isUnit_R_of_fomDefined A b x₀ hm hH))
    (fomFixed_isGalerkin A b x₀ hm hH) (norm_ne_zero_iff.1 h0)
  linarith

/-- **(6.64)** (Cullum–Greenbaum): `ρ_{m+1}^F = ρ_{m+1}^G/√(1 - (ρ_{m+1}^G/ρ_m^G)²)`. -/
theorem prop_6_13 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hH : FOMDefined A b x₀ (m + 1))
    (h0 : ρG A b x₀ (m + 1) ≠ 0) :
    ρF A b x₀ (m + 1)
      = ρG A b x₀ (m + 1) /
        Real.sqrt (1 - (ρG A b x₀ (m + 1) / ρG A b x₀ m) ^ 2) := by
  have h65 := eq_6_65 A b x₀ hm hH h0
  have hRm1 := isUnit_R_of_fomDefined A b x₀ hm hH
  have hGF := ρG_le_ρF A b x₀ hm hH hRm1
  have hGG := ρG_succ_le A b x₀ hm hRm1
  have ha : 0 < ρG A b x₀ (m + 1) := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have hf : 0 < ρF A b x₀ (m + 1) := lt_of_lt_of_le ha hGF
  have hp : 0 < ρG A b x₀ m := lt_of_lt_of_le ha hGG
  have hmul : ρF A b x₀ (m + 1) ^ 2 * (ρG A b x₀ m ^ 2 - ρG A b x₀ (m + 1) ^ 2)
      = ρG A b x₀ m ^ 2 * ρG A b x₀ (m + 1) ^ 2 := by
    field_simp at h65
    nlinarith [h65]
  have hgap : 0 < ρG A b x₀ m ^ 2 - ρG A b x₀ (m + 1) ^ 2 := by
    have hprod : (0 : ℝ) <
        ρF A b x₀ (m + 1) ^ 2 * (ρG A b x₀ m ^ 2 - ρG A b x₀ (m + 1) ^ 2) := by
      rw [hmul]; positivity
    rcases mul_pos_iff.1 hprod with ⟨-, hgt⟩ | ⟨hlt', -⟩
    · exact hgt
    · nlinarith
  have hnn : (0 : ℝ) ≤ 1 - (ρG A b x₀ (m + 1) / ρG A b x₀ m) ^ 2 := by
    rw [div_pow]
    rw [sub_nonneg, div_le_one (by positivity)]
    nlinarith
  have hs2 : Real.sqrt (1 - (ρG A b x₀ (m + 1) / ρG A b x₀ m) ^ 2) ^ 2
      = 1 - (ρG A b x₀ (m + 1) / ρG A b x₀ m) ^ 2 := Real.sq_sqrt hnn
  have hspos : 0 < Real.sqrt (1 - (ρG A b x₀ (m + 1) / ρG A b x₀ m) ^ 2) := by
    refine Real.sqrt_pos.2 ?_
    rw [div_pow, sub_pos, div_lt_one (by positivity)]
    nlinarith
  rw [eq_div_iff (ne_of_gt hspos)]
  have hsq : (ρF A b x₀ (m + 1) *
      Real.sqrt (1 - (ρG A b x₀ (m + 1) / ρG A b x₀ m) ^ 2)) ^ 2
      = ρG A b x₀ (m + 1) ^ 2 := by
    rw [mul_pow, hs2, div_pow]
    field_simp
    nlinarith [hmul]
  nlinarith [hsq, ha.le, mul_pos hf hspos]

/-! #### (6.66) and Corollary 6.14, (6.67) -/

/-- **(6.66)**: `∑_{i=0}^m 1/(ρ_i^F)² = 1/(ρ_m^G)²`. -/
theorem eq_6_66 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (hH : ∀ i ≤ m, FOMDefined A b x₀ i)
    (h0 : ρG A b x₀ m ≠ 0) :
    ∑ i ∈ Finset.range (m + 1), 1 / ρF A b x₀ i ^ 2 = 1 / ρG A b x₀ m ^ 2 :=
  (Krylov.inv_sq_norm_residual_minRes_eq_sum (xF := fun i => fomFixed A b x₀ i)
    (gmresFixed_isMinResIterate A b x₀ hm (isUnit_R_of_fomDefined A b x₀ hm (hH m le_rfl)))
    (fun i hi => fomFixed_isGalerkin A b x₀ (hi.trans hm) (hH i hi))
    (norm_ne_zero_iff.1 h0)).symm

/-- **Corollary 6.14**, (6.67): `ρ_m^G = 1/√(∑_{i=0}^m (1/ρ_i^F)²)`. -/
theorem cor_6_14 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (hH : ∀ i ≤ m, FOMDefined A b x₀ i)
    (h0 : ρG A b x₀ m ≠ 0) :
    ρG A b x₀ m = 1 / Real.sqrt (∑ i ∈ Finset.range (m + 1), 1 / ρF A b x₀ i ^ 2) := by
  have ha : 0 < ρG A b x₀ m := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  rw [eq_6_66 A b x₀ hm hH h0,
    show (1 : ℝ) / ρG A b x₀ m ^ 2 = (1 / ρG A b x₀ m) ^ 2 by rw [div_pow, one_pow],
    Real.sqrt_sq (by positivity), one_div_one_div]

/-! #### Proposition 6.15, (6.68) -/

/-- **Proposition 6.15**, (6.68): `ρ_m^G ≤ ρ^F_{m*} ≤ √(m+1) ρ_m^G`. -/
theorem prop_6_15 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (hH : ∀ i ≤ m, FOMDefined A b x₀ i) :
    ρG A b x₀ m ≤ ρFmin A b x₀ m ∧
      ρFmin A b x₀ m ≤ Real.sqrt (m + 1) * ρG A b x₀ m := by
  have hG := gmresFixed_isMinResIterate A b x₀ hm
    (isUnit_R_of_fomDefined A b x₀ hm (hH m le_rfl))
  constructor
  · refine le_ρFmin A b x₀ fun i hi' _ => ?_
    exact hG.min (fomFixed A b x₀ i)
      (Krylov.subspace_mono (op A) (b - op A x₀) hi'
        (fomFixed_isGalerkin A b x₀ (hi'.trans hm) (hH i hi')).mem)
  · obtain ⟨i, hi, hle⟩ := Krylov.exists_norm_residual_galerkin_le
      (xF := fun i => fomFixed A b x₀ i) hG
      (fun i hi => fomFixed_isGalerkin A b x₀ (hi.trans hm) (hH i hi))
    exact le_trans (ρFmin_le A b x₀ hi (hH i hi)) hle

/-! #### (6.74)–(6.75) -/

/-- **(6.74)**: `x_{m+1}^G = s_{m+1}² x_m^G + c_{m+1}² x_{m+1}^F`. -/
theorem eq_6_74 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hA : IsUnit A)
    (hH : FOMDefined A b x₀ (m + 1)) (h0 : ρG A b x₀ (m + 1) ≠ 0) :
    gmresFixed A b x₀ (m + 1)
      = s (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 • gmresFixed A b x₀ m +
        c (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 • fomFixed A b x₀ (m + 1) := by
  set h := arnoldiCoeff A (v₁ A b x₀) with hdef
  have hRm1 := isUnit_R_of_fomDefined A b x₀ hm hH
  have hGF := ρG_le_ρF A b x₀ hm hH hRm1
  have ha : 0 < ρG A b x₀ (m + 1) := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have hf : 0 < ρF A b x₀ (m + 1) := lt_of_lt_of_le ha hGF
  have hF0 : b - op A (fomFixed A b x₀ (m + 1)) ≠ 0 := norm_ne_zero_iff.1 (ne_of_gt hf)
  have hcne : ‖c h m‖ ≠ 0 := norm_ne_zero_iff.2 (givensC_ne_zero_of_fomDefined A b x₀ hm hH)
  have hratio : ρG A b x₀ (m + 1) ^ 2 / ρF A b x₀ (m + 1) ^ 2 = c h m ^ 2 := by
    rw [ρF_eq_div_norm_c A b x₀ hm hH, div_pow, div_div_eq_mul_div, ← hdef]
    rw [show ‖c h m‖ ^ 2 = c h m ^ 2 by rw [Real.norm_eq_abs, sq_abs]]
    field_simp
  have hcs : 1 - c h m ^ 2 = s h m ^ 2 := by
    have := eq_6_35 h (givensRho_ne_zero_of_fomDefined A b x₀ hm hH)
    linarith
  have hcomb := Krylov.minRes_eq_combination
    (gmresFixed_isMinResIterate_of_lt A b x₀ (by omega))
    (gmresFixed_isMinResIterate A b x₀ hm hRm1) (fomFixed_isGalerkin A b x₀ hm hH)
    (injective_op_of_isUnit hA) hF0
  rw [hcomb, hratio, hcs]
  norm_num

/-- Splitting the residual of a convex combination, the vector identity behind (6.75). -/
private theorem residual_combination {N : ℕ}
    (Aop : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N))
    (u v w : EuclideanSpace ℝ (Fin N)) {p q : ℝ} (hpq : p + q = 1) :
    u - Aop (p • v + q • w) = p • (u - Aop v) + q • (u - Aop w) := by
  rw [map_add, map_smul, map_smul]
  match_scalars <;> linarith

/-- **(6.75)**: `r_{m+1}^G = s_{m+1}² r_m^G + c_{m+1}² r_{m+1}^F`. -/
theorem eq_6_75 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hA : IsUnit A)
    (hH : FOMDefined A b x₀ (m + 1)) (h0 : ρG A b x₀ (m + 1) ≠ 0) :
    b - op A (gmresFixed A b x₀ (m + 1))
      = s (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 • (b - op A (gmresFixed A b x₀ m)) +
        c (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 • (b - op A (fomFixed A b x₀ (m + 1))) := by
  have hcs := eq_6_35 (arnoldiCoeff A (v₁ A b x₀))
    (givensRho_ne_zero_of_fomDefined A b x₀ hm hH)
  rw [eq_6_74 A b x₀ hm hA hH h0]
  exact residual_combination (op A) b _ _ (by linarith)

/-! #### P-6.14: Proposition 6.12 from (6.75) -/

/-- **P-6.14**: the two residuals on the right of (6.75) are orthogonal, so
`(ρ_{m+1}^G)² = s⁴ (ρ_m^G)² + c⁴ (ρ_{m+1}^F)²`. -/
theorem p_6_14 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hA : IsUnit A)
    (hH : FOMDefined A b x₀ (m + 1)) (h0 : ρG A b x₀ (m + 1) ≠ 0) :
    inner ℝ (b - op A (gmresFixed A b x₀ m)) (b - op A (fomFixed A b x₀ (m + 1))) = 0 ∧
      ρG A b x₀ (m + 1) ^ 2
        = s (arnoldiCoeff A (v₁ A b x₀)) m ^ 4 * ρG A b x₀ m ^ 2 +
          c (arnoldiCoeff A (v₁ A b x₀)) m ^ 4 * ρF A b x₀ (m + 1) ^ 2 := by
  have hG := gmresFixed_isMinResIterate_of_lt A b x₀ (show m < grade A (v₁ A b x₀) by omega)
  have hF := fomFixed_isGalerkin A b x₀ hm hH
  have horth : inner ℝ (b - op A (gmresFixed A b x₀ m))
      (b - op A (fomFixed A b x₀ (m + 1))) = 0 :=
    IsPetrovGalerkin.inner_residual_eq_zero hF (Krylov.residual_mem_subspace_succ hG.mem)
  refine ⟨horth, ?_⟩
  have horth' : inner ℝ (s (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 •
      (b - op A (gmresFixed A b x₀ m)))
      (c (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 • (b - op A (fomFixed A b x₀ (m + 1))))
      = (0 : ℝ) := by
    rw [real_inner_smul_left, real_inner_smul_right, horth, mul_zero, mul_zero]
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth'
  rw [← eq_6_75 A b x₀ hm hA hH h0, norm_smul, norm_smul,
    Real.norm_of_nonneg (sq_nonneg (s (arnoldiCoeff A (v₁ A b x₀)) m)),
    Real.norm_of_nonneg (sq_nonneg (c (arnoldiCoeff A (v₁ A b x₀)) m))] at hpy
  nlinarith [hpy]

/-! #### P-6.13: `x_m^G = x_m^F` forces both to be exact -/

/-- **P-6.13**: if `H_m` is nonsingular and the two approximations coincide, both are exact. -/
theorem p_6_13 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hH : FOMDefined A b x₀ (m + 1))
    (heq : gmresFixed A b x₀ (m + 1) = fomFixed A b x₀ (m + 1)) :
    b - op A (gmresFixed A b x₀ (m + 1)) = 0 ∧ b - op A (fomFixed A b x₀ (m + 1)) = 0 := by
  have hRm1 := isUnit_R_of_fomDefined A b x₀ hm hH
  have hcne : ‖c (arnoldiCoeff A (v₁ A b x₀)) m‖ ≠ 0 :=
    norm_ne_zero_iff.2 (givensC_ne_zero_of_fomDefined A b x₀ hm hH)
  have hdiv := ρF_eq_div_norm_c A b x₀ hm hH
  have hG0 : ρG A b x₀ (m + 1) = 0 := by
    by_contra h0
    have hFG : ρF A b x₀ (m + 1) = ρG A b x₀ (m + 1) :=
      congrArg (fun x => ‖b - op A x‖) heq.symm
    rw [hFG, eq_div_iff hcne] at hdiv
    have hc1 : ‖c (arnoldiCoeff A (v₁ A b x₀)) m‖ = 1 :=
      mul_left_cancel₀ h0 (by rw [mul_one]; exact hdiv)
    have hs0 : s (arnoldiCoeff A (v₁ A b x₀)) m = 0 := by
      have hcs := eq_6_35 (arnoldiCoeff A (v₁ A b x₀))
        (givensRho_ne_zero_of_fomDefined A b x₀ hm hH)
      have hc2 : c (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 = 1 := by
        rw [show c (arnoldiCoeff A (v₁ A b x₀)) m ^ 2
            = ‖c (arnoldiCoeff A (v₁ A b x₀)) m‖ ^ 2 by rw [Real.norm_eq_abs, sq_abs], hc1]
        norm_num
      nlinarith
    have : ρG A b x₀ (m + 1) = 0 := by
      rw [ρG_eq_norm_gamma A b x₀ hm hRm1, gamma_succ, hs0, neg_zero, zero_mul, norm_zero]
    exact h0 this
  have hF0 : ρF A b x₀ (m + 1) = 0 := by rw [hdiv, hG0, zero_div]
  exact ⟨norm_eq_zero.1 hG0, norm_eq_zero.1 hF0⟩

/-! #### Proposition 6.17 (Brown) and P-6.9 -/

/-- A Galerkin iterate at step `m + 1` exists exactly when `H_{m+1}` is nonsingular, provided
GMRES has not converged. -/
private theorem exists_galerkin_iff {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hA : IsUnit A)
    (h0 : ρG A b x₀ (m + 1) ≠ 0) :
    (∃ x, Krylov.IsGalerkinIterate (op A) b x₀ (m + 1) x) ↔ FOMDefined A b x₀ (m + 1) := by
  refine ⟨fun ⟨xF, hF⟩ => ?_, fun hH => ⟨_, fomFixed_isGalerkin A b x₀ hm hH⟩⟩
  have hG := gmresFixed_isMinResIterate A b x₀ hm (isUnit_R_of_isUnit A b x₀ hA hm)
  have hkey := Krylov.IsGalerkinIterate.norm_residual_eq_div_norm_givensC
    (by rw [← grade_v₁]; exact hm) hF hG
  have hcne : Krylov.givensC (Arnoldi.coeff (op A) (r₀ A b x₀)) m ≠ 0 := by
    intro hc
    rw [hc, norm_zero, div_zero] at hkey
    exact h0 (le_antisymm (by rw [← hkey]; exact hG.min xF hF.mem) (norm_nonneg _))
  rw [FOMDefined, H_v₁]
  exact (Krylov.isUnit_hessenbergSq_iff_givensC_ne_zero (by rw [← grade_v₁]; exact hm)).2 hcne

/-- **Proposition 6.17** (Brown) and **P-6.9**: GMRES makes no progress at step `m + 1` exactly
when FOM breaks down there (`H_{m+1}` singular). -/
theorem prop_6_17 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hA : IsUnit A)
    (h0 : ρG A b x₀ (m + 1) ≠ 0) :
    gmresFixed A b x₀ (m + 1) = gmresFixed A b x₀ m ↔ ¬ FOMDefined A b x₀ (m + 1) := by
  have hG := gmresFixed_isMinResIterate_of_lt A b x₀ (show m < grade A (v₁ A b x₀) by omega)
  have hG' := gmresFixed_isMinResIterate A b x₀ hm (isUnit_R_of_isUnit A b x₀ hA hm)
  have hbb := Krylov.norm_residual_minRes_eq_iff_not_exists_galerkin hG hG'
    (norm_ne_zero_iff.1 h0) (by rw [← grade_v₁]; exact hm)
  rw [← exists_galerkin_iff A b x₀ hm hA h0, ← hbb]
  constructor
  · intro heq
    rw [heq]
  · intro heq
    obtain ⟨z, -, huniq⟩ :=
      Krylov.existsUnique_isMinResIterate_of_injective (injective_op_of_isUnit hA) b x₀ (m + 1)
    have hGm : Krylov.IsMinResIterate (op A) b x₀ (m + 1) (gmresFixed A b x₀ m) := by
      refine ⟨Krylov.subspace_mono (op A) (b - op A x₀) (Nat.le_succ m) hG.mem, fun y hy => ?_⟩
      rw [← heq]
      exact hG'.min y hy
    rw [huniq _ hG', huniq _ hGm]

/-! #### Lemma 6.16 (Freund), (6.69)–(6.73) -/

/-- **(6.70)**: the last entry of `g_{m+1}` is `c_{m+1} γ_{m+1}`. -/
theorem eq_6_70 (h : ℕ → ℕ → ℝ) (t : ℝ) (m : ℕ) :
    g h t (m + 1) (Fin.last m) = c h m * γ h t m := by
  rw [g_apply, Fin.val_last, Krylov.gvec]
  simp

/-- **(6.71)**: the last diagonal entry of `R_{m+1}` is `ξ_{m+1}/c_{m+1}`. -/
theorem eq_6_71 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hH : FOMDefined A b x₀ (m + 1)) :
    R (arnoldiCoeff A (v₁ A b x₀)) (m + 1) (Fin.last m) (Fin.last m)
      = ξ (arnoldiCoeff A (v₁ A b x₀)) (m + 1) / c (arnoldiCoeff A (v₁ A b x₀)) m := by
  have hξ : ξ (arnoldiCoeff A (v₁ A b x₀)) (m + 1)
      = Krylov.rotated (arnoldiCoeff A (v₁ A b x₀)) m m m := by rw [ξ, Nat.add_sub_cancel]
  have hξ0 : Krylov.rotated (arnoldiCoeff A (v₁ A b x₀)) m m m ≠ 0 := by
    have := ξ_ne_zero_of_fomDefined A b x₀ hm hH
    rwa [hξ] at this
  rw [R_apply, Fin.val_last, Krylov.rotated_succ_self, hξ,
    show c (arnoldiCoeff A (v₁ A b x₀)) m = Krylov.givensC (arnoldiCoeff A (v₁ A b x₀)) m from
      rfl,
    Krylov.givensC, div_div_eq_mul_div, eq_div_iff hξ0]
  ring

/-- The core of **Lemma 6.16**, at the level of the Givens data alone: `R_{m+1}` and `R̃_{m+1}`
differ only in the entry `(m, m)`, and the right-hand sides `g_{m+1}` and `g̃_{m+1}` only in
their last entry `c_m γ_m` versus `γ_m`; solving both systems against the padded previous
solution therefore gives two multiples of the same vector. -/
private theorem sub_snoc_eq_smul (h : ℕ → ℕ → ℝ) (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0)
    (t : ℝ) {m : ℕ} (hρ : Krylov.givensRho h m ≠ 0)
    (hRt : IsUnit (Rtilde h (m + 1))) (y : Fin (m + 1) → ℝ) (yp : Fin m → ℝ)
    (hy : R h (m + 1) *ᵥ y = g h t (m + 1)) (hyp : R h m *ᵥ yp = g h t m) :
    y - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ)
      = Krylov.givensC h m ^ 2 •
        (ytilde h t (m + 1) - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ)) := by
  have hzlast : (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ) (Fin.last m) = 0 := Fin.snoc_last _ _
  have hRz := R_mulVec_snoc h hh t yp hyp
  have hρ' : Krylov.rotated h (m + 1) m m ≠ 0 := by
    rw [Krylov.rotated_succ_self]
    simpa using hρ
  have hcdef : Krylov.givensC h m =
      Krylov.rotated h m m m / Krylov.rotated h (m + 1) m m := by
    rw [Krylov.rotated_succ_self, Krylov.givensC]
  have hgv : Krylov.gvec h t m = Krylov.givensC h m * Krylov.gamma h t m := by
    rw [Krylov.gvec]
    simp
  have hRtz : Rtilde h (m + 1) *ᵥ (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ)
      = R h (m + 1) *ᵥ (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ) := by
    rw [R_mulVec_eq_Rtilde_mulVec_add h hh m _, hzlast, mul_zero, Pi.single_zero, add_zero]
  have hu : R h (m + 1) *ᵥ (y - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ))
      = Pi.single (Fin.last m) (Krylov.gvec h t m) := by
    rw [Matrix.mulVec_sub, hy, hRz]
    abel
  have hw : Rtilde h (m + 1) *ᵥ
      (ytilde h t (m + 1) - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ))
      = Pi.single (Fin.last m) (Krylov.gamma h t m) := by
    rw [Matrix.mulVec_sub, ytilde, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hRt), Matrix.one_mulVec,
      hRtz, hRz]
    funext i
    rcases eq_or_ne i (Fin.last m) with rfl | hi
    · rw [Pi.sub_apply, Pi.sub_apply, gtilde_last, g_apply, Fin.val_last, Pi.single_eq_same,
        Pi.single_eq_same]
      ring
    · obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.2 hi
      rw [Pi.sub_apply, Pi.sub_apply, gtilde_castSucc, g_apply, Fin.val_castSucc,
        Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi]
      ring
  have hulast : Krylov.rotated h (m + 1) m m *
      (y - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ)) (Fin.last m)
      = Krylov.givensC h m * Krylov.gamma h t m := by
    have hlast := congrFun hu (Fin.last m)
    simp only [Matrix.mulVec, dotProduct, Pi.single_eq_same] at hlast
    rw [Fin.sum_univ_castSucc] at hlast
    have hz : ∀ j : Fin m, R h (m + 1) (Fin.last m) j.castSucc *
        (y - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ)) j.castSucc = 0 := by
      intro j
      rw [R_apply, Fin.val_last, Fin.val_castSucc,
        Krylov.rotated_eq_zero_of_lt h hh (m + 1) m (j : ℕ) (by omega) j.isLt, zero_mul]
    rw [Finset.sum_congr rfl fun j _ => hz j, Finset.sum_const_zero, zero_add, R_apply,
      Fin.val_last] at hlast
    rw [hlast, hgv]
  have hentry : Krylov.gvec h t m -
      (Krylov.rotated h (m + 1) m m - Krylov.rotated h m m m) *
        (y - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ)) (Fin.last m)
      = Krylov.givensC h m ^ 2 * Krylov.gamma h t m := by
    have hxi : Krylov.rotated h m m m
        = Krylov.givensC h m * Krylov.rotated h (m + 1) m m := by
      rw [hcdef]
      field_simp
    rw [hgv, hxi]
    linear_combination (Krylov.givensC h m - 1) * hulast
  have hRtu : Rtilde h (m + 1) *ᵥ (y - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ))
      = Pi.single (Fin.last m) (Krylov.givensC h m ^ 2 * Krylov.gamma h t m) := by
    have hsplit := R_mulVec_eq_Rtilde_mulVec_add h hh m
      (y - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ))
    rw [hu, ← Krylov.rotated_succ_self h m] at hsplit
    funext i
    rcases eq_or_ne i (Fin.last m) with rfl | hi
    · have hval := congrFun hsplit (Fin.last m)
      rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_same] at hval
      rw [Pi.single_eq_same, ← hentry]
      linarith [hval]
    · have hval := congrFun hsplit i
      rw [Pi.add_apply, Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, add_zero] at hval
      rw [Pi.single_eq_of_ne hi, ← hval]
  refine Matrix.mulVec_injective_iff_isUnit.2 hRt ?_
  rw [hRtu, Matrix.mulVec_smul, hw]
  funext i
  rcases eq_or_ne i (Fin.last m) with rfl | hi
  · rw [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, smul_eq_mul]
  · rw [Pi.smul_apply, Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, smul_eq_mul, mul_zero]

/-- **(6.69)** (Lemma 6.16, Freund): `y_{m+1} - (y_m; 0) = c_{m+1}²(ỹ_{m+1} - (y_m; 0))`. -/
theorem lemma_6_16 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ (m + 1)) :
    gmresY A b x₀ (m + 1) - (Fin.snoc (gmresY A b x₀ m) (0 : ℝ) : Fin (m + 1) → ℝ)
      = c (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 •
        (ytilde (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀) (m + 1) -
          (Fin.snoc (gmresY A b x₀ m) (0 : ℝ) : Fin (m + 1) → ℝ)) := by
  have hy := mulVec_R_gmresY A b x₀ (isUnit_R_of_fomDefined A b x₀ hm hH)
  have hyp := mulVec_R_gmresY A b x₀
    (isUnit_R_of_lt_grade A b x₀ (show m < grade A (v₁ A b x₀) by omega))
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hy hyp
  exact sub_snoc_eq_smul (arnoldiCoeff A (v₁ A b x₀)) (arnoldiCoeff_hessenberg A b x₀)
    (β A b x₀) (givensRho_ne_zero_of_fomDefined A b x₀ hm hH)
    (isUnit_Rtilde_of_fomDefined A b x₀ hm hH) _ _ hy hyp

end BookResults

end SaadSparse.Ch06

