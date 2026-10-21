import Numlib.LinearAlgebra.Matrix.HessenbergSolutionDecay
import Mathlib.Data.Nat.Dist
import Numlib.LinearAlgebra.Matrix.PosDef

/-!
# Inverse entry decay for positive definite tridiagonal matrices

Polynomial bandwidth localizes every column, and the normalized Chebyshev residual
polynomial gives a geometric bound for actual solutions and inverse entries.
-/

noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped InnerProductSpace
namespace Matrix
variable {N : ℕ} {T : Matrix (Fin N) (Fin N) ℝ}

/-- Powers of a tridiagonal matrix have bandwidth at most their exponent. -/
theorem IsTridiagonal.pow_apply_eq_zero_of_lt_dist {R : Type*} [Semiring R]
    {A : Matrix (Fin N) (Fin N) R} (hT : A.IsTridiagonal)
    (k : ℕ) (i j : Fin N) (hij : k < Nat.dist i j) : (A ^ k) i j = 0 := by
  induction k generalizing i j with
  | zero =>
    have hne : i ≠ j := by intro he; subst j; simp at hij
    simp [hne]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hil : 1 < Nat.dist i l
    · have ht : A i l = 0 := (isTridiagonal_iff_fin.mp hT) i l (by
        unfold Nat.dist at hil
        omega)
      rw [ht, zero_mul]
    · have hlj : k < Nat.dist l j := by
        have hd := Nat.dist.triangle_inequality (i : ℕ) l j
        omega
      rw [ih l j hlj, mul_zero]

/-- A matrix polynomial has zero entries beyond its degree times the tridiagonal
bandwidth. This applies to every commutative coefficient semiring and does not require symmetry. -/
theorem IsTridiagonal.aeval_apply_eq_zero_of_natDegree_lt_dist
    {R : Type*} [CommSemiring R] {A : Matrix (Fin N) (Fin N) R}
    (hT : A.IsTridiagonal) (p : R[X]) (i j : Fin N)
    (hij : p.natDegree < Nat.dist i j) : aeval A p i j = 0 := by
  rw [Polynomial.aeval_eq_sum_range]
  simp only [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro k hk
  have hpow := hT.pow_apply_eq_zero_of_lt_dist k i j
    (lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hij)
  simp [hpow]

/-- A Krylov vector started in one coordinate vanishes beyond its polynomial bandwidth. -/
theorem IsTridiagonal.apply_eq_zero_of_mem_krylov (hT : T.IsTridiagonal)
    {c : ℝ} {m : ℕ} {j : Fin N} {z : EuclideanSpace ℝ (Fin N)}
    (hz : z ∈ Krylov.subspace (toEuclideanLin T) (c • EuclideanSpace.single j 1) m)
    {i : Fin N} (hi : m ≤ Nat.dist i j) : z i = 0 := by
  induction hz using Submodule.span_induction with
  | mem v hv =>
    rcases hv with ⟨k, rfl⟩
    change ((toEuclideanLin T ^ (k : ℕ)) (c • EuclideanSpace.single j 1)) i = 0
    rw [map_smul, PiLp.smul_apply, smul_eq_mul, ← toEuclideanLin_pow]
    change c * (T ^ (k : ℕ) *ᵥ Pi.single j 1) i = 0
    have hp := hT.pow_apply_eq_zero_of_lt_dist (k : ℕ) i j (lt_of_lt_of_le k.isLt hi)
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, hp]
  | zero => rfl
  | add v w _ _ hv hw => simp only [PiLp.add_apply, hv, hw, add_zero]
  | smul r v _ hv => simp only [PiLp.smul_apply, hv, smul_zero]

/-- Actual solutions with a single-coordinate right-hand side decay with the distance
from that coordinate. The scalar spectral interval is included. -/
theorem IsTridiagonal.solution_coordinate_le (hT : T.IsTridiagonal)
    {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hB : (toEuclideanLin T).IsSymmetricBoundedBy a b)
    {x : EuclideanSpace ℝ (Fin N)} {j : Fin N}
    (hx : toEuclideanLin T x = c • EuclideanSpace.single j 1) (i : Fin N) :
    |x i| ≤ 2 * ((Real.sqrt (b / a) - 1) / (Real.sqrt (b / a) + 1)) ^
      Nat.dist i j * ‖x‖ := by
  rcases hab.lt_or_eq with hab | rfl
  · let p := shifted (Nat.dist i j) a b 0
    have hp : p.eval 0 = 1 := shifted_eval_self (Nat.dist i j) hab (by
      intro h; exact (not_le_of_gt ha) h.1)
    obtain ⟨z, hz, hres⟩ := Krylov.exists_mem_of_residual_poly
      (A := toEuclideanLin T) (b := toEuclideanLin T x) (x₀ := 0)
      p (shifted_degree_le _ _ _ _) hp
    simp only [map_zero, sub_zero] at hz hres
    have herror : x - z = aeval (toEuclideanLin T) p x := by
      apply (hB.isSymmetricCoercive ha).isCoercive.injective
      rw [map_sub, hres, Module.End.aeval_apply_apply]
    have hzi : z i = 0 := hT.apply_eq_zero_of_mem_krylov (by rwa [hx] at hz) le_rfl
    have hpoly : ‖aeval (toEuclideanLin T) p x‖ ≤
        (2 * ((Real.sqrt (b / a) - 1) / (Real.sqrt (b / a) + 1)) ^ Nat.dist i j) * ‖x‖ :=
      norm_aeval_shifted_le ha hab hB (Nat.dist i j) x
    calc |x i| = ‖(x - z) i‖ := by simp [PiLp.sub_apply, hzi, Real.norm_eq_abs]
      _ ≤ ‖x - z‖ := PiLp.norm_apply_le _ _
      _ = ‖aeval (toEuclideanLin T) p x‖ := congrArg norm herror
      _ ≤ _ := hpoly
  · by_cases hi : (Nat.dist i j) = 0
    · simp only [hi, pow_zero, mul_one]
      exact (show |x i| ≤ ‖x‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i).trans
        (by nlinarith [norm_nonneg x])
    · have hscalar := hB.apply_eq_smul x
      rw [hx] at hscalar
      have he : x = a⁻¹ • (c • EuclideanSpace.single j 1) := by
        simpa only [RCLike.ofReal_real_eq_id, id_eq, smul_smul,
          inv_mul_cancel₀ ha.ne', one_smul] using (congrArg (fun v => a⁻¹ • v) hscalar).symm
      have hi0 : i ≠ j := by intro h; subst j; simp at hi
      simp [he, PiLp.smul_apply, hi0,
        div_self ha.ne', Real.sqrt_one, zero_pow hi]

/-- Every inverse entry obeys the Chebyshev distance estimate for any positive
spectral enclosure. No inverse approximation or decay conclusion is assumed. -/
theorem IsTridiagonal.inv_entry_le (hT : T.IsTridiagonal)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hB : (toEuclideanLin T).IsSymmetricBoundedBy a b) (i j : Fin N) :
    |T⁻¹ i j| ≤ (2 / a) *
      ((Real.sqrt (b / a) - 1) / (Real.sqrt (b / a) + 1)) ^ Nat.dist i j := by
  have hunit : IsUnit T := mulVec_injective_iff_isUnit.mp (by
    intro x y hxy
    have he : toEuclideanLin T (WithLp.toLp 2 x) =
        toEuclideanLin T (WithLp.toLp 2 y) := congrArg (WithLp.toLp 2) hxy
    exact congrArg WithLp.ofLp ((hB.isSymmetricCoercive ha).isCoercive.injective he))
  let x := toEuclideanLin T⁻¹ (EuclideanSpace.single j 1)
  have hx : toEuclideanLin T x = EuclideanSpace.single j 1 :=
    toEuclideanLin_mul_nonsing_inv_apply hunit _
  have hxj : x i = T⁻¹ i j := by
    simp [x, Matrix.toEuclideanLin_apply]
  have hn : ‖x‖ ≤ 1 / a := by
    have he := hB.isCoerciveWith.norm_le_norm_apply x
    simp only [hx, EuclideanSpace.single, PiLp.norm_single, norm_one] at he
    exact (le_div_iff₀ ha).mpr (by nlinarith)
  have hκ : 1 ≤ b / a := (one_le_div ha).mpr hab
  have hs : 1 ≤ Real.sqrt (b / a) := Real.one_le_sqrt.mpr hκ
  have hr : 0 ≤ (Real.sqrt (b / a) - 1) / (Real.sqrt (b / a) + 1) := by positivity
  have hd := hT.solution_coordinate_le ha hab hB
    (show toEuclideanLin T x = 1 • EuclideanSpace.single j 1 by simpa using hx) i
  rw [hxj] at hd
  calc |T⁻¹ i j| ≤ 2 * ((Real.sqrt (b / a) - 1) /
      (Real.sqrt (b / a) + 1)) ^ Nat.dist i j * ‖x‖ := hd
    _ ≤ 2 * ((Real.sqrt (b / a) - 1) /
      (Real.sqrt (b / a) + 1)) ^ Nat.dist i j * (1 / a) := by gcongr
    _ = _ := by ring

/-- The source spectral interval can be chosen to be the actual smallest and largest
eigenvalues of the positive definite matrix. Empty dimensions have no entry indices. -/
theorem PosDef.tridiagonal_inv_entry_le (hP : T.PosDef) (hT : T.IsTridiagonal)
    (i j : Fin N) :
    |T⁻¹ i j| ≤ (2 / (⨅ k, hP.1.eigenvalues k)) *
      ((Real.sqrt ((⨆ k, hP.1.eigenvalues k) / (⨅ k, hP.1.eigenvalues k)) - 1) /
        (Real.sqrt ((⨆ k, hP.1.eigenvalues k) / (⨅ k, hP.1.eigenvalues k)) + 1)) ^
          Nat.dist i j := by
  let : Nonempty (Fin N) := ⟨i⟩
  have hb := (Set.finite_range hP.1.eigenvalues).bddBelow
  have ha := (Set.finite_range hP.1.eigenvalues).bddAbove
  obtain ⟨imin, hmin⟩ := exists_eq_ciInf_of_finite (f := hP.1.eigenvalues)
  have hp : 0 < ⨅ k, hP.1.eigenvalues k := hmin ▸ hP.eigenvalues_pos imin
  have he (k : Fin N) : hP.1.eigenvalues k ∈
      Set.Icc (⨅ l, hP.1.eigenvalues l) (⨆ l, hP.1.eigenvalues l) :=
    ⟨ciInf_le hb k, le_ciSup ha k⟩
  exact hT.inv_entry_le hp ((he i).1.trans (he i).2)
    (hP.1.isSymmetricBoundedBy_toEuclideanLin he) i j

end Matrix
