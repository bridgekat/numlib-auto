import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Krylov.Iterate
import Numlib.Krylov.Relations

/-!
# Hessenberg relations, FOM/GMRES coordinates and Givens rotations

* `Krylov.HessenbergRelation A v h`: a sequence `v` with `A v_j = ∑_{i ≤ j+1} h i j v_i`
  ([saad2003iterative] (6.6)–(6.7)), *without* orthogonality, so that the residual formulas
  [saad2003iterative] (6.18), (6.27) and Prop 6.7 apply verbatim to IOM/DIOM/DQGMRES and
  ([saad2003iterative] Ch. 7) to the bi-Lanczos basis of QMR; Arnoldi is the instance
  `Arnoldi.hessenbergRelation`.
* FOM and GMRES in coordinates ([saad2003iterative] (6.16)–(6.17), (6.28)–(6.30)): for `m ≤ grade`,
  the Galerkin iterate is `x₀ + V_m y` with `H_m y = β e₁`, exists uniquely iff `H_m` is a unit, and
  the minimal-residual iterate is `x₀ + V_m y` with `y` the least-squares solution of `H̄_m y ≈ β
  e₁`.
* Givens rotations, indexed by `ℕ` (no `Fin` casts): the progressive QR factorization of the
  Hessenberg coefficients `h`, the parameters `c_k, s_k, ρ_k`, the transformed right-hand side `γ_k,
  g_k` with `γ_{k+1} = -s_k γ_k` ([saad2003iterative] (6.37), (6.44)–(6.47), (6.80)–(6.81);
  [choi2006iterative] §2.2.3; [fong2012cg] §4.2), `‖r_m‖ = |γ_m|` ([saad2003iterative] (6.42)), and
  the spec-level identifications `|s_m| = ‖r^G_{m+1}‖ / ‖r^G_m‖`, `|c_m| = ‖r^G_{m+1}‖ /
  ‖r^F_{m+1}‖`, `H_{m+1}` unit iff `c_m ≠ 0` ([saad2003iterative] Prop 6.9, (6.75), Lemma 6.16).
  Because the rotations are computed from the infinite coefficient function, prefix stability across
  `m` is automatic.

Here `r^G_m` is the residual of the minimal-residual (GMRES) iterate and `r^F_m` that of the
Galerkin (FOM) iterate, both over `x₀ + 𝒦_m`.
-/

open Krylov Finset

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Krylov

/-- The rectangular `(m+1) × m` Hessenberg matrix of a coefficient function `h`. -/
def hessenbergOf (h : ℕ → ℕ → 𝕜) (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) 𝕜 :=
  Matrix.of fun i j => h i j

/-- The square `m × m` Hessenberg matrix of a coefficient function `h`. -/
def hessenbergSqOf (h : ℕ → ℕ → 𝕜) (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜 :=
  Matrix.of fun i j => h i j

/-- `β e₁ ∈ 𝕜^m`. -/
def firstVec (β : 𝕜) (m : ℕ) : Fin m → 𝕜 := fun i => if (i : ℕ) = 0 then β else 0

/-- A sequence `v` satisfying the Hessenberg relation `A v_j = ∑_{i ≤ j+1} h i j v_i` with `h` upper
Hessenberg ([saad2003iterative], (6.6)–(6.9) without orthogonality). -/
structure HessenbergRelation (A : E →ₗ[𝕜] E) (v : ℕ → E) (h : ℕ → ℕ → 𝕜) : Prop where
  /-- The expansion of `A v_j` in the vectors up to `v_{j+1}`. -/
  apply_eq : ∀ j, A (v j) = ∑ i ∈ range (j + 2), h i j • v i
  /-- The coefficients are upper Hessenberg. -/
  eq_zero_of_lt : ∀ i j, j + 1 < i → h i j = 0

namespace HessenbergRelation

variable {A : E →ₗ[𝕜] E} {v : ℕ → E} {h : ℕ → ℕ → 𝕜} (hv : HessenbergRelation A v h)
include hv

/-- The matrix `H̄_m` cut out of the coefficients of a Hessenberg relation is upper Hessenberg. -/
theorem hessenbergOf_isUpperHessenbergRect (m : ℕ) : (hessenbergOf h m).IsUpperHessenbergRect :=
  fun i j hij => hv.eq_zero_of_lt i j hij

/-- The Hessenberg expansion of `A v_j` may be taken over any range containing `j + 2`. -/
private theorem apply_eq_range (j N : ℕ) (hj : j + 2 ≤ N) :
    A (v j) = ∑ i ∈ range N, h i j • v i := by
  rw [hv.apply_eq j]
  refine Finset.sum_subset (by simpa using hj) fun i hi hi' => ?_
  rw [Finset.mem_range] at hi'
  rw [hv.eq_zero_of_lt i j (by omega), zero_smul]

/-- `A V_m = V_{m+1} H̄_m` ([saad2003iterative], (6.7)) in coordinates. -/
theorem apply_sum (m : ℕ) (y : Fin m → 𝕜) :
    A (∑ j, y j • v j) = ∑ i : Fin (m + 1), (hessenbergOf h m).mulVec y i • v i := by
  rw [map_sum]
  have hleft : ∀ j : Fin m, A (y j • v j) = ∑ i : Fin (m + 1), (y j * h i j) • v i := by
    intro j
    rw [map_smul, hv.apply_eq_range (j : ℕ) (m + 1) (by omega), Finset.smul_sum,
      ← Fin.sum_univ_eq_sum_range (fun i => y j • h i (j : ℕ) • v i) (m + 1)]
    exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
  rw [Finset.sum_congr rfl fun j _ => hleft j, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hessenbergOf, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]

/-- [saad2003iterative], (6.27): with `r₀ = β v₀`, the residual of `x₀ + V_m y` is `V_{m+1} (β e₁ -
H̄_m y)`. -/
theorem residual_eq {b x₀ : E} {β : 𝕜} (hr : b - A x₀ = β • v 0) (m : ℕ) (y : Fin m → 𝕜) :
    b - A (x₀ + ∑ j, y j • v j) =
      ∑ i : Fin (m + 1), (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) i • v i := by
  have hfirst : ∑ i : Fin (m + 1), firstVec β (m + 1) i • v i = β • v 0 := by
    rw [Finset.sum_eq_single (⟨0, Nat.succ_pos m⟩ : Fin (m + 1))]
    · rfl
    · intro i _ hi
      have : (i : ℕ) ≠ 0 := fun hc => hi (Fin.ext hc)
      simp [firstVec, this]
    · intro hc; exact absurd (Finset.mem_univ _) hc
  have hAx : A (x₀ + ∑ j, y j • v j) = A x₀ + ∑ i : Fin (m + 1),
      (hessenbergOf h m).mulVec y i • v i := by
    rw [map_add, hv.apply_sum m y]
  have hsplit : ∑ i : Fin (m + 1), (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) i • v i
      = β • v 0 - ∑ i : Fin (m + 1), (hessenbergOf h m).mulVec y i • v i := by
    rw [← hfirst, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply, sub_smul]
  rw [hsplit, hAx, ← hr]
  abel

/-- [saad2003iterative], Prop 6.7 / (6.18): if `H_m y = β e₁` then the residual of `x₀ + V_m y` is
`-(h_{m,m-1} y_{m-1}) v_m`. -/
theorem residual_eq_of_mulVec_eq {b x₀ : E} {β : 𝕜} (hr : b - A x₀ = β • v 0) {m : ℕ}
    (hm : 0 < m) (y : Fin m → 𝕜) (hy : (hessenbergSqOf h m).mulVec y = firstVec β m) :
    b - A (x₀ + ∑ j, y j • v j) = -(h m (m - 1) * y ⟨m - 1, by omega⟩) • v m := by
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

end HessenbergRelation

end Krylov

namespace Arnoldi

variable (A : E →ₗ[𝕜] E) (b : E)

/-- `H̄_m` of the Arnoldi process is the rectangular Hessenberg matrix of its coefficients. -/
theorem hessenberg_eq (m : ℕ) : hessenberg A b m = hessenbergOf (coeff A b) m := rfl

/-- `H_m` of the Arnoldi process is the square Hessenberg matrix of its coefficients. -/
theorem hessenbergSq_eq (m : ℕ) : hessenbergSq A b m = hessenbergSqOf (coeff A b) m := rfl

/-- The Arnoldi vectors and coefficients satisfy the Hessenberg relation (for every `j`, also after
breakdown where both sides vanish). -/
theorem hessenbergRelation : HessenbergRelation A (vec A b) (coeff A b) :=
  ⟨apply_vec A b, fun _ _ hij => coeff_eq_zero_of_lt A b hij⟩

/-- `β v₀ = r₀`: the first Arnoldi vector is the normalized starting vector (and both sides vanish
when `b = 0`). -/
theorem smul_vec_zero : (‖b‖ : 𝕜) • vec A b 0 = b := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  · have hne : ((‖b‖ : ℝ) : 𝕜) ≠ 0 := by simpa using norm_ne_zero_iff.mpr hb
    rw [vec_zero A b hb, smul_smul, mul_inv_cancel₀ hne, one_smul]

end Arnoldi

namespace Krylov

section ArnoldiCoords

/-! ### Coordinates in the Arnoldi basis

Auxiliary lemmas expressing membership in `𝒦_m`, orthogonality to `𝒦_m` and the norm of a
combination of Arnoldi vectors in terms of the coefficient vector. -/

variable (A : E →ₗ[𝕜] E) (r : E)

/-- `𝒦_m` is spanned by the `Fin m`-indexed family of Arnoldi vectors. -/
private theorem span_range_vec (m : ℕ) :
    Submodule.span 𝕜 (Set.range fun j : Fin m => Arnoldi.vec A r (j : ℕ)) = subspace A r m := by
  rw [← Arnoldi.span_vec A r m]
  congr 1
  ext z
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨(j : ℕ), j.isLt, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, rfl⟩

/-- Membership in `𝒦_m` is the existence of Arnoldi coordinates: `z ∈ 𝒦_m` iff `z = V_m y` for some
`y : Fin m → 𝕜`. -/
theorem mem_subspace_iff_exists_coeffs (m : ℕ) (z : E) :
    z ∈ subspace A r m ↔ ∃ y : Fin m → 𝕜, z = ∑ j, y j • Arnoldi.vec A r (j : ℕ) := by
  rw [← span_range_vec A r m, Submodule.mem_span_range_iff_exists_fun]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

private theorem vec_mem_subspace_of_lt {m j : ℕ} (hj : j < m) :
    Arnoldi.vec A r j ∈ subspace A r m := by
  rw [← span_range_vec A r m]
  exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩

private theorem sum_smul_vec_mem (m : ℕ) (y : Fin m → 𝕜) :
    ∑ j, y j • Arnoldi.vec A r (j : ℕ) ∈ subspace A r m :=
  (mem_subspace_iff_exists_coeffs A r m _).mpr ⟨y, rfl⟩

variable [FiniteDimensional 𝕜 (fullSubspace A r)]

/-- Below the grade the Arnoldi vectors are orthonormal, so they read off coefficients. -/
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

/-- Pythagoras: the norm of a combination of Arnoldi vectors whose coefficients vanish past the
grade is the `ℓ²` norm of the coefficient vector. -/
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

/-- The Arnoldi vectors below the grade are linearly independent. -/
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
  have hin := Submodule.inner_right_of_mem_orthogonal (vec_mem_subspace_of_lt A r hj) h
  rwa [inner_vec_sum_eq A r c j (lt_of_lt_of_le hj hm)] at hin

/-- The residual coefficient vector vanishes at the last index once the grade is reached. -/
theorem residual_coeff_eq_zero {m : ℕ} (hm : m ≤ grade A r) (y : Fin m → 𝕜)
    (i : Fin (m + 1)) (hi : grade A r ≤ (i : ℕ)) :
    (firstVec (‖r‖ : 𝕜) (m + 1) - (Arnoldi.hessenberg A r m).mulVec y) i = 0 := by
  have him : (i : ℕ) = m := by have := i.isLt; omega
  have hmv : ∀ j : Fin m, Arnoldi.coeff A r (i : ℕ) (j : ℕ) = 0 := by
    intro j
    rw [him]
    rcases Nat.lt_or_ge ((j : ℕ) + 1) m with hj | hj
    · exact Arnoldi.coeff_eq_zero_of_lt A r hj
    · have hjm : (j : ℕ) + 1 = m := by have := j.isLt; omega
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

/-- The Galerkin condition in coordinates. -/
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

/-- [saad2003iterative], (6.28): for `m ≤ grade`, `‖b - A (x₀ + V_m y)‖ = ‖β e₁ - H̄_m y‖₂`. -/
theorem norm_residual_eq_norm_firstVec_sub_mulVec {m : ℕ} (hm : m ≤ grade A (b - A x₀))
    (y : Fin m → 𝕜) :
    ‖b - A (x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j)‖ =
      ‖(WithLp.toLp 2 (firstVec (‖b - A x₀‖ : 𝕜) (m + 1) -
        (Arnoldi.hessenberg A (b - A x₀) m).mulVec y) : EuclideanSpace 𝕜 (Fin (m + 1)))‖ := by
  rw [(Arnoldi.hessenbergRelation A (b - A x₀)).residual_eq
    (Arnoldi.smul_vec_zero A (b - A x₀)).symm m y]
  exact norm_sum_smul_vec_eq A (b - A x₀) _ (residual_coeff_eq_zero A (b - A x₀) hm y)

/-- FOM ([saad2003iterative], (6.16)–(6.17)): `x₀ + V_m y` is the Galerkin iterate iff `H_m y = β
e₁`. -/
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

/-- FOM in coordinates, in point form: for `m ≤ grade`, a point is the Galerkin iterate over `x₀ +
𝒦_m` exactly when it is `x₀ + V_m y` for some solution `y` of the small square system `H_m y = β
e₁`, with `β = ‖r₀‖`. The companion `Krylov.isGalerkinIterate_iff_mulVec_eq` starts from a given
coordinate vector; quantifying it away here is what lets solvability of the Hessenberg system be
traded for existence and uniqueness of the iterate
(`Krylov.existsUnique_isGalerkinIterate_iff_isUnit`). -/
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

/-- FOM is well defined iff `H_m` is nonsingular ([saad2003iterative], §6.4, Props 6.12–6.17's
hypothesis). -/
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
/-- [saad2003iterative], Prop 6.7 for Arnoldi: the Galerkin residual is `-(h_{m,m-1} y_{m-1}) v_m`.
-/
theorem residual_galerkin_eq {m : ℕ} (hm : 0 < m) (y : Fin m → 𝕜)
    (hy : (Arnoldi.hessenbergSq A (b - A x₀) m).mulVec y = firstVec (‖b - A x₀‖ : 𝕜) m) :
    b - A (x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j) =
      -(Arnoldi.coeff A (b - A x₀) m (m - 1) * y ⟨m - 1, by omega⟩) •
        Arnoldi.vec A (b - A x₀) m :=
  (Arnoldi.hessenbergRelation A (b - A x₀)).residual_eq_of_mulVec_eq
    (Arnoldi.smul_vec_zero A (b - A x₀)).symm hm y hy

/-- GMRES ([saad2003iterative], (6.29)–(6.30)): `x₀ + V_m y` is the minimal-residual iterate iff `y`
minimizes `‖β e₁ - H̄_m z‖₂`. -/
theorem isMinResIterate_iff_isMinOn {m : ℕ} (hm : m ≤ grade A (b - A x₀)) (y : Fin m → 𝕜) :
    IsMinResIterate A b x₀ m (x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j) ↔
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

end Coordinates

section Givens

/-! ### Givens rotations, `ℕ`-indexed

`rotated h k` is the coefficient function after the first `k` rotations; rotation `k` acts on rows
`k, k+1` and annihilates the entry `(k+1, k)`. With `a = (rotated h k) k k`, `d = (rotated h k)
(k+1) k`, `ρ_k = √(|a|² + |d|²)`, `c_k = a / ρ_k`, `s_k = d / ρ_k`, the rotation is `[[c̄_k, s̄_k],
[-s_k, c_k]]` ([saad2003iterative], (6.80) for complex `𝕜`; `s_k` is real for Arnoldi coefficients).
-/

/-- The Hessenberg coefficients after `k` Givens rotations. -/
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

/-- `ρ_k = √(|r_kk|² + |h_{k+1,k}|²)`. -/
noncomputable def givensRho (k : ℕ) : ℝ :=
  Real.sqrt (‖rotated h k k k‖ ^ 2 + ‖rotated h k (k + 1) k‖ ^ 2)

/-- `c_k = r_kk / ρ_k`. -/
noncomputable def givensC (k : ℕ) : 𝕜 := rotated h k k k / (givensRho h k : 𝕜)

/-- `s_k = h_{k+1,k} / ρ_k`. -/
noncomputable def givensS (k : ℕ) : 𝕜 := rotated h k (k + 1) k / (givensRho h k : 𝕜)

/-- `γ_0 = β`, `γ_{k+1} = -s_k γ_k` ([saad2003iterative], (6.47)): the last entry of the rotated
right-hand side. -/
noncomputable def gamma (β : 𝕜) : ℕ → 𝕜
  | 0 => β
  | k + 1 => -givensS h k * gamma β k

/-- `g_k = c̄_k γ_k`: the `k`-th entry of `Q_m (β e₁)` for `k < m`. -/
noncomputable def gvec (β : 𝕜) (k : ℕ) : 𝕜 := starRingEnd 𝕜 (givensC h k) * gamma h β k

/-- [saad2003iterative], (6.47): the last entry of the rotated right-hand side obeys `γ_{k+1} = -s_k
γ_k`. This is the second defining clause of `Krylov.gamma` stated as a rewritable equation. Since
`‖r_m‖ = |γ_m|` (`Krylov.IsMinResIterate.norm_residual_eq_norm_gamma`), it is the residual
recurrence of the minimal-residual iteration, and the induction step behind `‖γ_m‖ = ∏_{k<m} |s_k|
‖β‖`. -/
theorem gamma_succ (β : 𝕜) (k : ℕ) : gamma h β (k + 1) = -givensS h k * gamma h β k := rfl

/-- Unfolding of `rotated` at a successor, in terms of `givensC` and `givensS`. -/
theorem rotated_succ_apply (k i j : ℕ) :
    rotated h (k + 1) i j =
      if i = k then
        starRingEnd 𝕜 (givensC h k) * rotated h k k j +
          starRingEnd 𝕜 (givensS h k) * rotated h k (k + 1) j
      else if i = k + 1 then
        -givensS h k * rotated h k k j + givensC h k * rotated h k (k + 1) j
      else rotated h k i j := rfl

/-- `ρ_k` is a norm, hence nonnegative. -/
theorem givensRho_nonneg (k : ℕ) : 0 ≤ givensRho h k := Real.sqrt_nonneg _

/-- `ρ_k² = |h_{kk}|² + |h_{k+1,k}|²` for the entries as rotation `k` sees them. -/
theorem givensRho_sq (k : ℕ) :
    givensRho h k ^ 2 = ‖rotated h k k k‖ ^ 2 + ‖rotated h k (k + 1) k‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- `ρ_k = 0` exactly when the two entries being rotated both vanish. -/
private theorem rotated_eq_zero_of_givensRho_eq_zero {k : ℕ} (hρ : givensRho h k = 0) :
    rotated h k k k = 0 ∧ rotated h k (k + 1) k = 0 := by
  have hsum : ‖rotated h k k k‖ ^ 2 + ‖rotated h k (k + 1) k‖ ^ 2 = 0 := by
    rw [← givensRho_sq, hρ]
    ring
  obtain ⟨h1, h2⟩ := (add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).mp hsum
  exact ⟨norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h1),
    norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h2)⟩

/-- `‖γ_m‖ = ∏_{k < m} |s_k| ‖β‖` ([saad2003iterative], (6.47)). -/
theorem norm_gamma_eq_prod (β : 𝕜) (m : ℕ) :
    ‖gamma h β m‖ = (∏ k ∈ range m, ‖givensS h k‖) * ‖β‖ := by
  induction m with
  | zero => simp [gamma]
  | succ m ih =>
      rw [gamma_succ, norm_mul, norm_neg, ih, Finset.prod_range_succ]
      ring

/-- `|c_k|² + |s_k|² = 1`: the parameters of rotation `k` are those of a genuine rotation, so long
as the two entries it mixes are not both zero. That proviso is the content of `ρ_k ≠ 0`: at a
breakdown both `c_k` and `s_k` are `0 / 0 = 0` and the identity fails. -/
theorem norm_givensC_sq_add_norm_givensS_sq (k : ℕ) (hρ : givensRho h k ≠ 0) :
    ‖givensC h k‖ ^ 2 + ‖givensS h k‖ ^ 2 = 1 := by
  have habs : ‖((givensRho h k : ℝ) : 𝕜)‖ = givensRho h k := by
    rw [RCLike.norm_ofReal, abs_of_nonneg (givensRho_nonneg h k)]
  rw [givensC, givensS, norm_div, norm_div, habs, div_pow, div_pow, ← add_div,
    ← givensRho_sq h k]
  exact div_self (pow_ne_zero 2 hρ)

/-- Rotation `k` produces the real diagonal entry `ρ_k` and annihilates `(k+1, k)`. -/
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

/-- Rotation `k` annihilates the subdiagonal entry it was built for: `(k+1, k)` becomes `0`. -/
theorem rotated_succ_succ_self (k : ℕ) : rotated h (k + 1) (k + 1) k = 0 := by
  rw [rotated_succ_apply, ite_eq_right (by omega), ite_eq_left rfl, givensC, givensS]
  ring

/-- Rows below `k` are untouched by the first `k` rotations. -/
theorem rotated_eq_of_le (k i j : ℕ) (hi : k + 1 ≤ i) : rotated h k i j = h i j := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
      rw [rotated_succ_apply, ite_eq_right (by omega), ite_eq_right (by omega)]
      exact ih i (by omega)

/-- After `k` rotations the first `k` columns are upper triangular. -/
theorem rotated_eq_zero_of_lt (hh : ∀ i j, j + 1 < i → h i j = 0) (k i j : ℕ) (hj : j < k)
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
            exact hh i j (by omega)

/-- Columns `j < k` are not changed by rotation `k`, for Hessenberg `h`. -/
theorem rotated_succ_eq_of_lt (hh : ∀ i j, j + 1 < i → h i j = 0) (k j : ℕ) (hj : j < k) (i : ℕ) :
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

/-- The `k`-th rotation as an `(m+1) × (m+1)` matrix (identity outside rows/columns `k, k+1`). -/
noncomputable def givensMatrix (k m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜 :=
  Matrix.of fun i j =>
    if (i : ℕ) = k ∧ (j : ℕ) = k then starRingEnd 𝕜 (givensC h k)
    else if (i : ℕ) = k ∧ (j : ℕ) = k + 1 then starRingEnd 𝕜 (givensS h k)
    else if (i : ℕ) = k + 1 ∧ (j : ℕ) = k then -givensS h k
    else if (i : ℕ) = k + 1 ∧ (j : ℕ) = k + 1 then givensC h k
    else if i = j then 1 else 0

/-- A sum over `Fin N` all of whose terms outside `{p, q}` vanish. -/
private theorem sum_pair_of_eq_zero {ι : Type*} [Fintype ι] {p q : ι}
    (hpq : p ≠ q) (f : ι → 𝕜) (hf : ∀ l, l ≠ p → l ≠ q → f l = 0) :
    ∑ l, f l = f p + f q := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ ({p, q} : Finset ι))
    (fun x _ hx => hf x (fun hc => hx (by simp [hc])) fun hc => hx (by simp [hc])),
    Finset.sum_pair hpq]

/-- The row action of a Givens matrix. -/
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
  · rw [sum_pair_of_eq_zero hpq _ ?_]
    · simp [givensMatrix, h1]
    · intro l hlp hlq
      have hl1 : (l : ℕ) ≠ k := fun hc => hlp (Fin.ext hc)
      have hl2 : (l : ℕ) ≠ k + 1 := fun hc => hlq (Fin.ext hc)
      have hil : i ≠ l := fun hc => hl1 (hc ▸ h1)
      simp [givensMatrix, h1, hl1, hl2, hil]
  · rw [sum_pair_of_eq_zero hpq _ ?_]
    · simp [givensMatrix, h2]
    · intro l hlp hlq
      have hl1 : (l : ℕ) ≠ k := fun hc => hlp (Fin.ext hc)
      have hl2 : (l : ℕ) ≠ k + 1 := fun hc => hlq (Fin.ext hc)
      have hil : i ≠ l := fun hc => hl2 (hc ▸ h2)
      simp [givensMatrix, h2, hl1, hl2, hil]
  · rw [Finset.sum_eq_single i]
    · simp [givensMatrix, h1, h2]
    · intro l _ hli
      simp [givensMatrix, h1, h2, Ne.symm hli]
    · intro hc; exact absurd (Finset.mem_univ _) hc

/-- The `k`-th column of a Givens matrix. -/
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

/-- The `(k+1)`-st column of a Givens matrix. -/
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

/-- Outside columns `k` and `k+1` a Givens matrix agrees with the identity. -/
private theorem givensMatrix_apply_of_col_ne (k m : ℕ) (p q : Fin (m + 1)) (h1 : (q : ℕ) ≠ k)
    (h2 : (q : ℕ) ≠ k + 1) : givensMatrix h k m p q = if p = q then 1 else 0 := by
  simp [givensMatrix, h1, h2]

/-- A Givens rotation is unitary, provided the pair of entries it acts on does not vanish. It
differs from the identity only in the four entries indexed by rows and columns `k` and `k + 1`, and
`|c_k|² + |s_k|² = 1` makes that two-by-two block unitary. -/
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

/-- `Ω_k H̄^{(k)} = H̄^{(k+1)}` for `k < m`. -/
theorem givensMatrix_mul_hessenbergOf_rotated (k m : ℕ) (hk : k < m) :
    givensMatrix h k m * hessenbergOf (rotated h k) m = hessenbergOf (rotated h (k + 1)) m := by
  ext i j
  rw [Matrix.mul_apply, givensMatrix_row h k m hk i (fun l => hessenbergOf (rotated h k) m l j)]
  change _ = rotated h (k + 1) (i : ℕ) (j : ℕ)
  rw [rotated_succ_apply]
  split_ifs <;> rfl

/-- `Q^{(n)}_m = Ω_{n-1} ⋯ Ω_0`, the product of the first `n` rotations, as an `(m+1) × (m+1)`
matrix. Only `n = m` occurs in the factorization `Q_m H̄_m = R̄_m`, but the partial products carry
the induction and describe the breakdown case, where the last rotation degenerates. -/
noncomputable def givensQAux (n m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜 :=
  (((List.range n).map fun k => givensMatrix h k m).reverse).prod

/-- `Q_m = Ω_{m-1} ⋯ Ω_0`. -/
noncomputable def givensQ (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜 := givensQAux h m m

/-- `Q_m` is the partial product at `n = m`. -/
theorem givensQ_eq_givensQAux (m : ℕ) : givensQ h m = givensQAux h m m := rfl

/-- No rotations applied is the identity. -/
@[simp]
theorem givensQAux_zero (m : ℕ) : givensQAux h 0 m = 1 := by simp [givensQAux]

/-- One more rotation multiplies on the left: `Q^{(n+1)}_m = Ω_n Q^{(n)}_m`. -/
theorem givensQAux_succ (n m : ℕ) :
    givensQAux h (n + 1) m = givensMatrix h n m * givensQAux h n m := by
  rw [givensQAux, givensQAux, List.range_succ, List.map_append, List.reverse_append]
  simp

/-- The rotation matrices are stable in `m`: the leading block of `Ω_k` at size `m + 2` is `Ω_k` at
size `m + 1`. -/
theorem givensMatrix_castSucc (k m : ℕ) (i j : Fin (m + 1)) :
    givensMatrix h k (m + 1) i.castSucc j.castSucc = givensMatrix h k m i j := by
  simp only [givensMatrix, Matrix.of_apply, Fin.val_castSucc, Fin.castSucc_inj]

/-- The last row of `Ω_m`, seen inside `Fin (m + 2)`. -/
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

/-- Rows beyond the first `n` are rows of the identity in `Q^{(n)}_m`. -/
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

/-- The leading block of `Q^{(n)}_{m+1}` is `Q^{(n)}_m`, for `n ≤ m`. -/
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

/-- `Q^{(n)}_m H̄_m = H̄^{(n)}_m` for `n ≤ m`. -/
theorem givensQAux_mul_hessenbergOf {n m : ℕ} (hn : n ≤ m) :
    givensQAux h n m * hessenbergOf h m = hessenbergOf (rotated h n) m := by
  induction n with
  | zero => simp [rotated]
  | succ n ih =>
      rw [givensQAux_succ, Matrix.mul_assoc, ih (by omega),
        givensMatrix_mul_hessenbergOf_rotated h n m (by omega)]

/-- `Q_m H̄_m = R̄_m` ([saad2003iterative], (6.38)–(6.39)): the rotated coefficients form the
triangular factor. -/
theorem givensQ_mul_hessenbergOf (m : ℕ) :
    givensQ h m * hessenbergOf h m = hessenbergOf (rotated h m) m :=
  givensQAux_mul_hessenbergOf h le_rfl

/-- A product of genuine rotations is unitary; `ρ_k ≠ 0` is what makes rotation `k` genuine. -/
theorem givensQAux_mem_unitaryGroup {n m : ℕ} (hn : n ≤ m) (hρ : ∀ k < n, givensRho h k ≠ 0) :
    givensQAux h n m ∈ Matrix.unitaryGroup (Fin (m + 1)) 𝕜 := by
  refine Submonoid.list_prod_mem _ ?_
  intro M hM
  rw [List.mem_reverse, List.mem_map] at hM
  obtain ⟨k, hk, rfl⟩ := hM
  rw [List.mem_range] at hk
  exact givensMatrix_mem_unitaryGroup h k m (by omega) (hρ k hk)

/-- The accumulated rotation `Q_m = Ω_{m-1} ⋯ Ω_0` is unitary as long as no single rotation
degenerates. This is what makes `Q_m` a Euclidean isometry, so that the least-squares quantity `‖β
e₁ - H̄_m y‖` may be read off the triangular factor `R̄_m = Q_m H̄_m` instead — the route to `‖r_m‖
= |γ_m|`. -/
theorem givensQ_mem_unitaryGroup (m : ℕ) (hρ : ∀ k < m, givensRho h k ≠ 0) :
    givensQ h m ∈ Matrix.unitaryGroup (Fin (m + 1)) 𝕜 :=
  givensQAux_mem_unitaryGroup h le_rfl hρ

/-- Outside its leading `(n+1) × (n+1)` block the product of the first `n` rotations is the
identity: the columns after `n` are unchanged. -/
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

/-- The right-hand side after `n` rotations: `(g_0, …, g_{n-1}, γ_n, 0, …)`. -/
noncomputable def gvecTrunc (β : 𝕜) (n i : ℕ) : 𝕜 :=
  if i < n then gvec h β i else if i = n then gamma h β n else 0

/-- Entry `n` of the truncated right-hand side is the running residual `γ_n`. -/
theorem gvecTrunc_self (β : 𝕜) (n : ℕ) : gvecTrunc h β n n = gamma h β n := by
  simp [gvecTrunc]

/-- The truncated right-hand side stops just after `γ_n`. -/
theorem gvecTrunc_succ (β : 𝕜) (n : ℕ) : gvecTrunc h β n (n + 1) = 0 := by
  simp [gvecTrunc]

/-- Below `n` the truncated right-hand side is the solved part `g_i`. -/
theorem gvecTrunc_of_lt (β : 𝕜) {n i : ℕ} (hi : i < n) :
    gvecTrunc h β n i = gvec h β i := by simp [gvecTrunc, hi]

/-- Above `n` the truncated right-hand side vanishes. -/
theorem gvecTrunc_of_gt (β : 𝕜) {n i : ℕ} (hi : n < i) : gvecTrunc h β n i = 0 := by
  simp [gvecTrunc, Nat.not_lt.mpr hi.le, hi.ne']

/-- The first `n` rotations turn `β e₁` into `(g_0, …, g_{n-1}, γ_n, 0, …)` ([saad2003iterative],
(6.44)–(6.46)). -/
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

/-- `Q_m (β e₁) = (g_0, …, g_{m-1}, γ_m)` ([saad2003iterative], (6.40), (6.44)–(6.47)). -/
theorem givensQ_mulVec_firstVec (β : 𝕜) (m : ℕ) :
    (givensQ h m).mulVec (firstVec β (m + 1)) =
      fun i : Fin (m + 1) => if (i : ℕ) < m then gvec h β i else gamma h β m := by
  rw [givensQ_eq_givensQAux, givensQAux_mulVec_firstVec h β m m le_rfl]
  funext i
  by_cases hi : (i : ℕ) < m
  · rw [gvecTrunc_of_lt h β hi, ite_eq_left hi]
  · have : (i : ℕ) = m := by omega
    rw [ite_eq_right hi, this, gvecTrunc_self]

/-- The last row of `R̄_m` vanishes. -/
theorem rotated_last_row (hh : ∀ i j, j + 1 < i → h i j = 0) (m j : ℕ) (hj : j < m) :
    rotated h m m j = 0 :=
  rotated_eq_zero_of_lt h hh m m j hj hj

/-! #### The triangular factor `R` -/

/-- `c_k` vanishes exactly when the pivot entry `r_kk` does. -/
theorem givensC_eq_zero_iff (k : ℕ) : givensC h k = 0 ↔ rotated h k k k = 0 := by
  rw [givensC, div_eq_zero_iff]
  refine ⟨fun hc => hc.elim id fun h0 => ?_, fun h0 => Or.inl h0⟩
  exact (rotated_eq_zero_of_givensRho_eq_zero h (by simpa using h0)).1

/-- A nonzero pivot forces a nonzero `ρ_k`, so no rotation degenerates there. -/
theorem givensRho_ne_zero_of_rotated_ne_zero {k : ℕ} (hk : rotated h k k k ≠ 0) :
    givensRho h k ≠ 0 := fun h0 => hk (rotated_eq_zero_of_givensRho_eq_zero h h0).1

/-- The diagonal of the triangular factor is `ρ_0, …, ρ_{n-1}` ([saad2003iterative], (6.37)). -/
theorem rotated_diag (hh : ∀ i j, j + 1 < i → h i j = 0) {n j : ℕ} (hj : j < n) :
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

/-- The square block of `H̄^{(n)}` is upper triangular as soon as its size does not exceed `n + 1`:
the first `n` columns have been triangularized and column `n` sits on the diagonal. -/
theorem hessenbergSqOf_rotated_isUpperTriangular (hh : ∀ i j, j + 1 < i → h i j = 0) {n N : ℕ}
    (hN : N ≤ n + 1) : (hessenbergSqOf (rotated h n) N).IsUpperTriangular := by
  intro i j hij
  have h1 : (j : ℕ) < (i : ℕ) := hij
  have h2 := i.isLt
  exact rotated_eq_zero_of_lt h hh n i j (by omega) h1

/-- The determinant of the triangular factor is the product of its diagonal. -/
theorem det_hessenbergSqOf_rotated (hh : ∀ i j, j + 1 < i → h i j = 0) {n N : ℕ}
    (hN : N ≤ n + 1) :
    (hessenbergSqOf (rotated h n) N).det = ∏ j : Fin N, rotated h n (j : ℕ) (j : ℕ) :=
  Matrix.det_of_isUpperTriangular (hessenbergSqOf_rotated_isUpperTriangular h hh hN)

/-- The triangular factor is nonsingular exactly when its diagonal has no zero. -/
theorem isUnit_hessenbergSqOf_rotated (hh : ∀ i j, j + 1 < i → h i j = 0) {n N : ℕ}
    (hN : N ≤ n + 1) (hd : ∀ j < N, rotated h n j j ≠ 0) :
    IsUnit (hessenbergSqOf (rotated h n) N) := by
  rw [Matrix.isUnit_iff_isUnit_det, det_hessenbergSqOf_rotated h hh hN, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr fun j _ => hd (j : ℕ) j.isLt

/-- `R_m` is nonsingular when no rotation degenerates. -/
theorem isUnit_hessenbergSqOf_rotated_self (hh : ∀ i j, j + 1 < i → h i j = 0) {m : ℕ}
    (hρ : ∀ k < m, givensRho h k ≠ 0) : IsUnit (hessenbergSqOf (rotated h m) m) :=
  isUnit_hessenbergSqOf_rotated h hh (by omega) fun j hj => by
    rw [rotated_diag h hh hj]
    simpa using hρ j hj

/-! #### The least-squares residual in rotated coordinates -/

/-- [saad2003iterative], (6.41): the `m` rotations are an isometry taking the least-squares residual
`β e₁ - H̄_m y` to `(g_m - R_m y, γ_m)`, so its square norm splits into the part the triangular
system can annihilate and the fixed remainder `|γ_m|²`. -/
theorem norm_sq_firstVec_sub_mulVec_eq (hh : ∀ i j, j + 1 < i → h i j = 0) {m : ℕ}
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

/-- When rotation `m` degenerates, row `m` of `R_{m+1}` vanishes: its diagonal entry is `ρ_m`. -/
theorem rotated_succ_row_eq_zero_of_givensRho_eq_zero (hh : ∀ i j, j + 1 < i → h i j = 0) {m : ℕ}
    (hρm : givensRho h m = 0) {j : ℕ} (hj : j ≤ m) : rotated h (m + 1) m j = 0 := by
  rcases Nat.lt_or_ge j m with hjm | hjm
  · exact rotated_eq_zero_of_lt h hh (m + 1) m j (by omega) hjm
  · have hjm' : j = m := by omega
    rw [hjm', rotated_succ_self h m, hρm]
    simp

/-- When rotation `m` degenerates, `c_m = 0`, hence the rotated right-hand side entry `g_m = c̄_m
γ_m` vanishes. -/
theorem gvec_eq_zero_of_givensRho_eq_zero {m : ℕ} (hρm : givensRho h m = 0) (β : 𝕜) :
    gvec h β m = 0 := by
  rw [gvec, (givensC_eq_zero_iff h m).mpr (rotated_eq_zero_of_givensRho_eq_zero h hρm).1,
    map_zero, zero_mul]

/-- A two-step Pythagoras bookkeeping lemma: a vector of length `N + 2` whose last entry vanishes
and whose remaining entries match those of a vector of length `N + 1` except for an extra `C` at
index `N`. -/
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
  have h3 : ∑ _i : Fin (N + 1), (0 : ℝ) = 0 := by simp
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

/-- The breakdown analogue of `norm_sq_firstVec_sub_mulVec_eq`: if rotation `m` degenerates (`ρ_m =
0`, so both entries it acts on already vanish) then the first `m` rotations still split the
least-squares residual of step `m + 1`, but the remainder is `|γ_m|`, not `|γ_{m+1}| = 0`. -/
theorem norm_sq_firstVec_sub_mulVec_eq_of_breakdown (hh : ∀ i j, j + 1 < i → h i j = 0) {m : ℕ}
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
    · have hjm : (j : ℕ) = m := by have := j.isLt; omega
      rw [hjm]; exact ha
  have hrowB : ∀ j : Fin (m + 1), rotated h m (m + 1) (j : ℕ) = 0 := by
    intro j
    rcases Nat.lt_or_ge (j : ℕ) m with hj | hj
    · exact rotated_eq_zero_of_lt h hh m (m + 1) (j : ℕ) hj (by omega)
    · have hjm : (j : ℕ) = m := by have := j.isLt; omega
      rw [hjm]; exact hb
  have hrowC : ∀ j : Fin (m + 1), rotated h (m + 1) m (j : ℕ) = 0 := fun j =>
    rotated_succ_row_eq_zero_of_givensRho_eq_zero h hh hρm (by have := j.isLt; omega)
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
    · have him : (i : ℕ) = m := by have := i.isLt; omega
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

/-! #### The square system `H_{m+1} y = v` in rotated coordinates -/

/-- Rows `0, …, m` of `Q^{(m)}_{m+1}` ignore the last coordinate, because the first `m` rotations
leave column `m + 1` alone. -/
private theorem givensQAux_mulVec_of_last {m : ℕ} (v : Fin (m + 2) → 𝕜)
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

/-- The first `m` rotations carry the square system `H_{m+1} y` to `R_{m+1} y`. -/
theorem hessenbergSqOf_rotated_mulVec {m : ℕ} (y : Fin (m + 1) → 𝕜) (i : Fin (m + 1)) :
    (hessenbergSqOf (rotated h m) (m + 1)).mulVec y i =
      (givensQAux h m (m + 1)).mulVec ((hessenbergOf h (m + 1)).mulVec y) i.castSucc := by
  rw [Matrix.mulVec_mulVec, givensQAux_mul_hessenbergOf h (by omega)]
  rfl

/-- `H_{m+1} y = 0` implies `R_{m+1} y = 0`: the extra Hessenberg row is invisible to the first `m +
1` rotated equations. -/
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

/-- [saad2003iterative], Prop 6.7 in coordinates: if `H_{m+1} y = β e₁` then the rectangular
residual `β e₁ - H̄_{m+1} y` is carried by its last entry alone. -/
theorem firstVec_sub_mulVec_apply_of_mulVec_eq (hh : ∀ i j, j + 1 < i → h i j = 0) (β : 𝕜)
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
        rw [hh (m + 1) (j : ℕ) (by omega), zero_mul]
      · intro hc; exact absurd (Finset.mem_univ _) hc
    rw [Pi.sub_apply, hfv, hmv, ite_eq_left hl, zero_sub]
  · have hlm : (l : ℕ) < m + 1 := by have := l.isLt; omega
    have e1 : firstVec β (m + 2) l = firstVec β (m + 1) ⟨(l : ℕ), hlm⟩ := rfl
    have e2 : (hessenbergOf h (m + 1)).mulVec y l =
        (hessenbergSqOf h (m + 1)).mulVec y ⟨(l : ℕ), hlm⟩ := rfl
    rw [Pi.sub_apply, e1, e2, hy, sub_self, ite_eq_right hl]

/-- The Galerkin residual in coordinates: `‖β e₁ - H̄_{m+1} y‖₂ = |h_{m+1,m} y_m|`
([saad2003iterative], (6.18)). -/
theorem norm_firstVec_sub_mulVec_of_mulVec_eq (hh : ∀ i j, j + 1 < i → h i j = 0) (β : 𝕜)
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

/-- [saad2003iterative], (6.43): if `H_{m+1} y = β e₁` then the last of the rotated equations reads
`r_mm y_m = γ_m`. -/
theorem rotated_self_mul_eq_gamma (hh : ∀ i j, j + 1 < i → h i j = 0) (β : 𝕜) {m : ℕ}
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

end Givens

section GivensArnoldi

/-! ### Identifications for the Arnoldi coefficients (`β = ‖r₀‖`) -/

variable {A : E →ₗ[𝕜] E} {b x₀ : E} [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]

/-- Strictly below the grade the subdiagonal Arnoldi coefficient is nonzero, so `ρ_k ≠ 0` and
rotation `k` is unitary. -/
theorem givensRho_arnoldi_ne_zero {k : ℕ} (hk : k + 1 < grade A (b - A x₀)) :
    givensRho (Arnoldi.coeff A (b - A x₀)) k ≠ 0 := by
  intro h0
  have h1 := (rotated_eq_zero_of_givensRho_eq_zero (Arnoldi.coeff A (b - A x₀)) h0).2
  rw [rotated_eq_of_le (Arnoldi.coeff A (b - A x₀)) k (k + 1) k le_rfl] at h1
  exact absurd ((Arnoldi.coeff_succ_self_eq_zero_iff A (b - A x₀) k).mp h1) (by omega)

/-- `γ_m ≠ 0` strictly below the grade: every `s_k` and the initial residual are nonzero
([saad2003iterative], (6.47)). -/
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

/-- A minimum of `P` over a family whose square splits as `D + G²`, with `D` attaining `0`, forces
`D = 0` and `P = G`. The arithmetic core of the Givens residual identities. -/
private theorem eq_of_min_split {P Q D G : ℝ} (hP2 : P ^ 2 = D + G ^ 2) (hQ2 : Q ^ 2 = G ^ 2)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hD : 0 ≤ D) (hG : 0 ≤ G) (hPQ : P ≤ Q) : D = 0 ∧ P = G := by
  have hD0 : D = 0 := le_antisymm (by nlinarith) hD
  refine ⟨hD0, ?_⟩
  rw [hD0, zero_add] at hP2
  nlinarith

/-- The minimal-residual iterate in rotated coordinates, when no rotation degenerates: its residual
norm is `|γ_m|` and its coordinate vector solves the triangular system `R_m y = g_m`
([saad2003iterative], (6.41)–(6.43)). -/
private theorem minres_rotated_of_givensRho_ne_zero {m : ℕ} (hm : m ≤ grade A (b - A x₀))
    (hρ : ∀ k < m, givensRho (Arnoldi.coeff A (b - A x₀)) k ≠ 0) {x : E}
    (hx : IsMinResIterate A b x₀ m x) :
    ‖b - A x‖ = ‖gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) m‖ ∧
      ∃ y : Fin m → 𝕜,
        (hessenbergSqOf (rotated (Arnoldi.coeff A (b - A x₀)) m) m).mulVec y =
            (fun i : Fin m => gvec (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) (i : ℕ)) ∧
          x = x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j := by
  have hh : ∀ i j : ℕ, j + 1 < i → Arnoldi.coeff A (b - A x₀) i j = 0 :=
    fun i j hij => Arnoldi.coeff_eq_zero_of_lt A (b - A x₀) hij
  obtain ⟨y, hy⟩ := (mem_subspace_iff_exists_coeffs A (b - A x₀) m _).mp hx.mem
  have hxe : x = x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j := by rw [← hy]; abel
  rw [hxe] at hx
  have hmin := (isMinResIterate_iff_isMinOn hm y).mp hx
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

/-- The breakdown case of `IsMinResIterate.exists_mulVec_rotated_eq`: some rotation before step `m`
degenerates. -/
private theorem minres_rotated_of_breakdown {m : ℕ} (hm : m ≤ grade A (b - A x₀))
    (hρ : ¬∀ k < m, givensRho (Arnoldi.coeff A (b - A x₀)) k ≠ 0) {x : E}
    (hx : IsMinResIterate A b x₀ m x) :
    ∃ y : Fin m → 𝕜, (hessenbergSqOf (rotated (Arnoldi.coeff A (b - A x₀)) m) m).mulVec y =
        (fun i : Fin m => gvec (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) i) ∧
      x = x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j := by
  have hh : ∀ i j : ℕ, j + 1 < i → Arnoldi.coeff A (b - A x₀) i j = 0 :=
    fun i j hij => Arnoldi.coeff_eq_zero_of_lt A (b - A x₀) hij
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
  have hmin := (isMinResIterate_iff_isMinOn hm y).mp hx
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
    · have hik : (i : ℕ) = k := by have := i.isLt; omega
      simp only [Matrix.mulVec, dotProduct, hessenbergSqOf, Matrix.of_apply, hik,
        gvec_eq_zero_of_givensRho_eq_zero (Arnoldi.coeff A (b - A x₀)) hρk]
      exact Finset.sum_eq_zero fun j _ => by
        rw [rotated_succ_row_eq_zero_of_givensRho_eq_zero (Arnoldi.coeff A (b - A x₀)) hh hρk
          (by have := j.isLt; omega), zero_mul]
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

/-- [saad2003iterative], (6.42), Prop 6.9(3): `‖r^G_m‖ = |γ_m|`.

The hypothesis `m < grade` is strict, and cannot be weakened to `m ≤ grade`: with `m = grade` the
statement is **false**.  Counterexample: `𝕜 = E = ℝ`, `A = 0`, `b = 1`, `x₀ = 0`.  Then `r₀ = 1`,
`𝒦_∞ = ℝ` so `grade = 1`, and `m = 1 ≤ grade`.  Every `x` is a minimal-residual iterate with `‖b - A
x‖ = 1`, while `h₀₀ = ⟪v₀, A v₀⟫ = 0` and `h₁₀ = 0` give `ρ₀ = 0`, hence `s₀ = 0 / 0 = 0` and `γ₁ =
-s₀ γ₀ = 0`.  With `m < grade` one gets `Arnoldi.coeff A r₀ (k+1) k ≠ 0`, hence `ρ_k ≠ 0`, for every
`k < m`, which is what the proof needs (`givensQ` unitary and `R_m` nonsingular).  The `m = grade`
case is covered by `IsMinResIterate.norm_residual_eq_norm_gamma_of_givensRho_ne_zero`, which assumes
exactly that. -/
theorem IsMinResIterate.norm_residual_eq_norm_gamma {m : ℕ} (hm : m < grade A (b - A x₀)) {x : E}
    (hx : IsMinResIterate A b x₀ m x) :
    ‖b - A x‖ = ‖gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) m‖ :=
  (minres_rotated_of_givensRho_ne_zero hm.le
    (fun k hk => givensRho_arnoldi_ne_zero (by omega)) hx).1

/-- [saad2003iterative], (6.42) at the boundary `m = grade`: `‖r^G_m‖ = |γ_m|` holds for every `m ≤
grade` at which no rotation has degenerated, which is the hypothesis
`IsMinResIterate.norm_residual_eq_norm_gamma` derives from `m < grade`. -/
theorem IsMinResIterate.norm_residual_eq_norm_gamma_of_givensRho_ne_zero {m : ℕ}
    (hm : m ≤ grade A (b - A x₀))
    (hρ : ∀ k < m, givensRho (Arnoldi.coeff A (b - A x₀)) k ≠ 0) {x : E}
    (hx : IsMinResIterate A b x₀ m x) :
    ‖b - A x‖ = ‖gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) m‖ :=
  (minres_rotated_of_givensRho_ne_zero hm hρ hx).1

/-- [saad2003iterative], (6.43)/(6.30): the minimal-residual iterate is `x₀ + V_m y` with `R_m y =
g_m`.

Unlike `IsMinResIterate.norm_residual_eq_norm_gamma` this holds up to and including `m = grade`. At
the boundary the last rotation may degenerate (`ρ_{m-1} = 0`), and then `R_m` is singular — but its
last row and the last entry `g_{m-1} = c̄_{m-1} γ_{m-1}` of the right-hand side both vanish, so the
system is still consistent and the minimal-residual coordinates solve it. -/
theorem IsMinResIterate.exists_mulVec_rotated_eq {m : ℕ} (hm : m ≤ grade A (b - A x₀)) {x : E}
    (hx : IsMinResIterate A b x₀ m x) :
    ∃ y : Fin m → 𝕜, (hessenbergSqOf (rotated (Arnoldi.coeff A (b - A x₀)) m) m).mulVec y =
        (fun i : Fin m => gvec (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) i) ∧
      x = x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j := by
  by_cases hρ : ∀ k < m, givensRho (Arnoldi.coeff A (b - A x₀)) k ≠ 0
  · exact (minres_rotated_of_givensRho_ne_zero hm hρ hx).2
  · exact minres_rotated_of_breakdown hm hρ hx

/-- `|s_m| = ‖r^G_{m+1}‖ / ‖r^G_m‖` ([saad2003iterative], (6.47), Prop 6.9).

As for `norm_residual_eq_norm_gamma`, the hypothesis `m + 1 < grade` is strict: the same
counterexample (`𝕜 = E = ℝ`, `A = 0`, `b = 1`, `x₀ = 0`, `m = 0`, `grade = 1`) has `‖b - A x'‖ = 1`
but `‖s₀‖ * ‖b - A x‖ = 0`. -/
theorem IsMinResIterate.norm_residual_succ_eq {m : ℕ} (hm : m + 1 < grade A (b - A x₀)) {x x' : E}
    (hx : IsMinResIterate A b x₀ m x) (hx' : IsMinResIterate A b x₀ (m + 1) x') :
    ‖b - A x'‖ = ‖givensS (Arnoldi.coeff A (b - A x₀)) m‖ * ‖b - A x‖ := by
  rw [hx'.norm_residual_eq_norm_gamma hm, hx.norm_residual_eq_norm_gamma (by omega),
    gamma_succ, norm_mul, norm_neg]

/-- `H_{m+1}` is nonsingular iff `c_m ≠ 0` ([saad2003iterative], Prop 6.9(1) / Lemma 6.16, `m + 1 ≤
grade`). -/
theorem isUnit_hessenbergSq_iff_givensC_ne_zero {m : ℕ} (hm : m + 1 ≤ grade A (b - A x₀)) :
    IsUnit (Arnoldi.hessenbergSq A (b - A x₀) (m + 1)) ↔
      givensC (Arnoldi.coeff A (b - A x₀)) m ≠ 0 := by
  have hh : ∀ i j : ℕ, j + 1 < i → Arnoldi.coeff A (b - A x₀) i j = 0 :=
    fun i j hij => Arnoldi.coeff_eq_zero_of_lt A (b - A x₀) hij
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

/-- [saad2003iterative], (6.75) / Prop 6.12: `‖r^F_{m+1}‖ = ‖r^G_{m+1}‖ / |c_m|`.

No hypothesis `c_m ≠ 0` is needed, even though the right-hand side would then be `0` by Lean's
convention for division: with `m + 1 ≤ grade` the existence of a Galerkin iterate already forces
`c_m ≠ 0`.  Indeed `H_{m+1} y = β e₁` gives `r_mm y_m = γ_m` after the rotations, and `γ_m ≠ 0`
strictly below the grade, so `r_mm ≠ 0`, i.e. `c_m ≠ 0`; equivalently `H_{m+1}` is then a unit
(`isUnit_hessenbergSq_iff_givensC_ne_zero`). -/
theorem IsGalerkinIterate.norm_residual_eq_div_norm_givensC {m : ℕ}
    (hm : m + 1 ≤ grade A (b - A x₀)) {xF xG : E} (hF : IsGalerkinIterate A b x₀ (m + 1) xF)
    (hG : IsMinResIterate A b x₀ (m + 1) xG) :
    ‖b - A xF‖ = ‖b - A xG‖ / ‖givensC (Arnoldi.coeff A (b - A x₀)) m‖ := by
  have hh : ∀ i j : ℕ, j + 1 < i → Arnoldi.coeff A (b - A x₀) i j = 0 :=
    fun i j hij => Arnoldi.coeff_eq_zero_of_lt A (b - A x₀) hij
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
/-- The rotation `s_m` is real and nonnegative for Arnoldi coefficients ([saad2003iterative],
§6.5.9). -/
theorem givensS_arnoldi_eq (m : ℕ) :
    givensS (Arnoldi.coeff A (b - A x₀)) m =
      (‖Arnoldi.w A (b - A x₀) m‖ / givensRho (Arnoldi.coeff A (b - A x₀)) m : ℝ) := by
  rw [givensS, rotated_eq_of_le (Arnoldi.coeff A (b - A x₀)) m (m + 1) m le_rfl,
    Arnoldi.coeff_succ_self, RCLike.ofReal_div]

end GivensArnoldi

end Krylov
