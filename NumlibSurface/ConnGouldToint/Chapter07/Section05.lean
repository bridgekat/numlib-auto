import Mathlib.Algebra.Order.Star.Real
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Eigen.Sturm
import Numlib.Optimization.Subproblem.Krylov
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The Lanczos trust-region subproblem

Section 7.5 of [conn2000trust].
-/

namespace ConnGouldToint.Chapter07

open Matrix

/-- Theorem 7.5.10. The preconditioned Lanczos relation and the shifted reduced
system give the full residual and its inverse-preconditioner energy norm. The next
dual Lanczos vector has unit energy norm whenever its coefficient is nonzero. -/
theorem theorem_7_5_10 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (H M Minv : E →ₗ[ℝ] E) (hMinv : Minv.IsSymmetricCoercive)
    (Q : (Fin (n + 1) → ℝ) →ₗ[ℝ] E) (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (g w : E) (γ β μ : ℝ) (hβ : 0 ≤ β)
    (hw : β ≠ 0 → energyNorm Minv w = 1)
    (hgrad : M (Q (Pi.single 0 γ)) = g)
    (hrel : ∀ y : Fin (n + 1) → ℝ,
      H (Q y) = M (Q (T *ᵥ y)) + (β * y (Fin.last n)) • w)
    (y : Fin (n + 1) → ℝ)
    (hsolve : (T + μ • 1) *ᵥ y = -(Pi.single 0 γ : Fin (n + 1) → ℝ)) :
    H (Q y) + μ • M (Q y) + g = (β * y (Fin.last n)) • w ∧
      energyNorm Minv (H (Q y) + μ • M (Q y) + g) = β * |y (Fin.last n)| := by
  have hsys : T *ᵥ y + μ • y = -(Pi.single 0 γ : Fin (n + 1) → ℝ) := by
    simpa only [add_mulVec, smul_mulVec, one_mulVec] using hsolve
  have hres : H (Q y) + μ • M (Q y) + g = (β * y (Fin.last n)) • w := calc
    _ = M (Q (T *ᵥ y + μ • y)) + g + (β * y (Fin.last n)) • w := by
      rw [hrel, map_add, map_smul, map_add, map_smul]
      abel
    _ = _ := by rw [hsys, map_neg, map_neg, hgrad]; abel
  refine ⟨hres, ?_⟩
  rw [hres]
  by_cases hb : β = 0
  · simp [hb, energyNorm]
  · rw [← WithEnergy.norm_equiv Minv hMinv, map_smul, norm_smul,
      WithEnergy.norm_equiv, hw hb, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg hβ]

/-- Lemma 7.5.11. An eigenvector of an irreducible tridiagonal matrix has nonzero first
component. Only the nonvanishing of the superdiagonal is needed. -/
theorem lemma_7_5_11 {n : ℕ} {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hT : T.IsTridiagonal) (hsup : ∀ i : Fin n, T i.castSucc i.succ ≠ 0) {θ : ℝ}
    {v : Fin (n + 1) → ℝ} (hv : T *ᵥ v = θ • v) (hv₀ : v ≠ 0) :
    v 0 ≠ 0 :=
  hT.apply_zero_ne_zero_of_superdiag_ne_zero
    (fun i hi => hsup ⟨i, by omega⟩) hv hv₀ (Nat.succ_pos _)

/-- Theorem 7.5.12. The right-hand side of the reduced subproblem has a nonzero pairing
with every eigenvector of the irreducible Lanczos tridiagonal, including those for its
smallest eigenvalue. The Lanczos starting coefficient is nonzero, as in the construction
from a nonzero starting gradient. -/
theorem theorem_7_5_12 {n : ℕ} {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hT : T.IsUnreducedUpperHessenberg) (hS : T.IsSymm) {γ : ℝ} (hγ : γ ≠ 0)
    {θ : ℝ} {v : Fin (n + 1) → ℝ} (hv : T *ᵥ v = θ • v) (hv₀ : v ≠ 0) :
    (Pi.single (0 : Fin (n + 1)) γ) ⬝ᵥ v ≠ 0 := by
  have hfirst : v 0 ≠ 0 :=
    hT.apply_zero_ne_zero_of_isSymm hS hv hv₀ (Nat.succ_pos _)
  rw [single_dotProduct]
  exact mul_ne_zero hγ hfirst

/-- Corollary 7.5.13. An irreducible full Lanczos tridiagonal rules out the hard
case in the original problem. In full coordinates every nonzero generalized
eigenvector has a nonzero pairing with the original gradient. -/
theorem corollary_7_5_13 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (H M : E →ₗ[ℝ] E) (hM : Function.Injective M)
    (Q : (Fin (n + 1) → ℝ) ≃ₗ[ℝ] E) {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hT : T.IsUnreducedUpperHessenberg) (hS : T.IsSymm)
    (hrel : ∀ y : Fin (n + 1) → ℝ, H (Q y) = M (Q (T *ᵥ y)))
    {g : E} {γ : ℝ} (hγ : γ ≠ 0)
    (hgrad : ∀ y : Fin (n + 1) → ℝ, inner ℝ g (Q y) = (Pi.single 0 γ) ⬝ᵥ y)
    {θ : ℝ} {v : E} (hv : H v = θ • M v) (hv₀ : v ≠ 0) :
    inner ℝ g v ≠ 0 := by
  obtain ⟨y, rfl⟩ := Q.surjective v
  have hy : T *ᵥ y = θ • y := by
    apply Q.injective
    apply hM
    rwa [← hrel, map_smul, map_smul]
  rw [hgrad]
  exact theorem_7_5_12 hT hS hγ hy (fun hz => hv₀ (by simp [hz]))

/-- Theorem 7.5.14. A positive semidefinite shift of the irreducible Lanczos
tridiagonal is positive definite if the shifted system has the prescribed right-hand
side with a nonzero starting coefficient. -/
theorem theorem_7_5_14 {n : ℕ} {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hT : T.IsUnreducedUpperHessenberg) (hS : T.IsSymm) {γ μ : ℝ} (hγ : γ ≠ 0)
    {h : Fin (n + 1) → ℝ}
    (hh : (T + μ • 1) *ᵥ h = Pi.single 0 (-γ))
    (hpos : (T + μ • 1).PosSemidef) :
    (T + μ • 1).PosDef := by
  let A := T + μ • 1
  have hsymm : A.IsSymm := isHermitian_iff_isSymm.mp hpos.isHermitian
  have hker (v : Fin (n + 1) → ℝ) (hv : A *ᵥ v = 0) : v = 0 := by
    by_contra hv₀
    have hev : T *ᵥ v = (-μ) • v := by
      have heq : T *ᵥ v + μ • v = 0 := by
        simpa only [A, add_mulVec, smul_mulVec, one_mulVec] using hv
      rw [neg_smul, eq_neg_iff_add_eq_zero]
      exact heq
    have hdot := dotProduct_transpose_mulVec A h v
    rw [hsymm.eq, hv, hh, dotProduct_zero, dotProduct_single] at hdot
    exact (mul_ne_zero (hT.apply_zero_ne_zero_of_isSymm hS hev hv₀ (Nat.succ_pos _)) (neg_ne_zero.mpr hγ)) hdot.symm
  refine (hpos.posDef_iff_mulVec_injective).mpr fun u v huv => sub_eq_zero.mp ?_
  exact hker (u - v) (by rw [mulVec_sub, huv, sub_self])

/-- Theorem 7.5.15. If the last coordinate of the shifted-system solution vanishes,
a subdiagonal entry of the tridiagonal matrix vanishes. For a symmetric matrix
this means it is reducible. -/
theorem theorem_7_5_15 {n : ℕ} {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (htri : T.IsTridiagonal) {γ μ : ℝ} (hγ : γ ≠ 0) {h : Fin (n + 1) → ℝ}
    (hh : (T + μ • 1) *ᵥ h = Pi.single 0 (-γ)) (hlast : h (Fin.last n) = 0) :
    ∃ i : Fin n, T i.succ i.castSucc = 0 := by
  by_contra! hsub
  have hT : T.IsUnreducedUpperHessenberg := (isUnreducedUpperHessenberg_iff_fin.2
    ⟨htri.isUpperHessenberg, fun i hi => hsub ⟨i, by omega⟩⟩)
  let A := T + μ • 1
  have hoff {i j : Fin (n + 1)} (hij : i ≠ j) : A i j = T i j := by
    simp [A, one_apply_ne hij]
  have hbackward : ∀ j (hj : j ≤ n), h ⟨n - j, by omega⟩ = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      cases j with
      | zero => simpa [Fin.last] using hlast
      | succ j =>
        let row : Fin (n + 1) := ⟨n - j, by omega⟩
        let col : Fin (n + 1) := ⟨n - (j + 1), by omega⟩
        have hr : 0 < (row : ℕ) := by dsimp [row]; omega
        have hcr : (col : ℕ) + 1 = (row : ℕ) := by dsimp [row, col]; omega
        have hrc : row ≠ col := fun he => by have := congrArg Fin.val he; omega
        have hrow := congrFun hh row
        change ∑ a, A row a * h a = (Pi.single 0 (-γ) : Fin (n + 1) → ℝ) row at hrow
        have hr₀ : row ≠ 0 := fun he => by have := congrArg Fin.val he; simpa using hr.ne' this
        rw [Pi.single_eq_of_ne hr₀] at hrow
        rw [Finset.sum_eq_single col] at hrow
        · have hne : T row col ≠ 0 := by
            have he : row = ⟨(col : ℕ) + 1, by omega⟩ := Fin.ext hcr.symm
            rw [he]
            exact (isUnreducedUpperHessenberg_iff_fin.1 hT).2 (col : ℕ) (by omega)
          exact (mul_eq_zero.mp hrow).resolve_left (by simpa [hoff hrc] using hne)
        · intro a _ hac
          rcases lt_or_gt_of_ne (fun he => hac (Fin.ext he)) with hal | hla
          · have har : a ≠ row := fun he => by have := congrArg Fin.val he; omega
            rw [hoff har.symm, htri row a (Or.inl ⟨col, Fin.lt_def.2 hal,
              Fin.lt_def.2 (by omega)⟩), zero_mul]
          · have hz := ih (n - (a : ℕ)) (by dsimp [col] at hla; omega) (by omega)
            have he : (⟨n - (n - (a : ℕ)), by omega⟩ : Fin (n + 1)) = a :=
              Fin.ext (by simp; omega)
            rw [he] at hz
            rw [hz, mul_zero]
        · simp
  have hzero : h = 0 := by
    funext a
    change h a = 0
    have hz := hbackward (n - (a : ℕ)) (by omega)
    have he : (⟨n - (n - (a : ℕ)), by omega⟩ : Fin (n + 1)) = a :=
      Fin.ext (by simp; omega)
    rwa [he] at hz
  have hfirst := congrFun hh (0 : Fin (n + 1))
  simp [hzero, hγ] at hfirst

/-- Theorem 7.5.16. In the easy case, a Lanczos breakdown makes the reduced trust-region
solution global. For a preconditioned problem, the ambient space carries the preconditioner
inner product, `H` represents the preconditioned Hessian and `g` the preconditioned gradient. -/
theorem theorem_7_5_16 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {H : E →L[ℝ] E} (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    {g : E} {n : ℕ} (hbreak : Lanczos.beta (H : E →ₗ[ℝ] E) g n = 0)
    (heasy : ∃ v, H v = Subproblem.leftmost hH • v ∧ inner ℝ v g ≠ 0)
    {Δ : ℝ} (hΔ : 0 < Δ) {s : E} (hsΔ : ‖s‖ ≤ Δ)
    (hs : s ∈ Krylov.subspace (H : E →ₗ[ℝ] E) g (n + 1))
    (hmin : IsMinOn (Subproblem.quadModel g H)
      ((Krylov.subspace (H : E →ₗ[ℝ] E) g (n + 1) : Set E) ∩ Metric.closedBall 0 Δ) s) :
    IsMinOn (Subproblem.quadModel g H) (Metric.closedBall 0 Δ) s := by
  have hgrade := (Lanczos.beta_eq_zero_iff g n).mp hbreak
  apply Subproblem.isMinOn_closedBall_of_isMinOn_invariant_subspace hH _
    (Subproblem.mem_krylov H g (Nat.succ_pos n)) heasy hΔ hs hsΔ hmin
  rw [Krylov.subspace_eq_of_grade_le _ _ hgrade]
  exact Krylov.subspace_grade_mem_invtSubmodule _ _

end ConnGouldToint.Chapter07
