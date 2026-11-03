import Mathlib.Algebra.Order.Star.Real
import Numlib.Eigen.Sturm
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The Lanczos trust-region subproblem

Section 7.5 of [conn2000trust].
-/

namespace ConnGouldToint.Chapter07

open Matrix

/-- Lemma 7.5.11. An eigenvector of an irreducible symmetric tridiagonal matrix has
nonzero first component. The unreduced upper Hessenberg condition, together with symmetry,
expresses tridiagonality and nonzero entries on both adjacent diagonals. -/
theorem lemma_7_5_11 {n : ℕ} {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hT : T.IsUnreducedUpperHessenberg) (hS : T.IsSymm) {θ : ℝ}
    {v : Fin (n + 1) → ℝ} (hv : T *ᵥ v = θ • v) (hv₀ : v ≠ 0) :
    v 0 ≠ 0 :=
  hT.apply_zero_ne_zero_of_isSymm hS hv hv₀ (Nat.succ_pos _)

/-- Theorem 7.5.12. The right-hand side of the reduced subproblem has a nonzero pairing
with every eigenvector of the irreducible Lanczos tridiagonal, including those for its
smallest eigenvalue. The Lanczos starting coefficient is nonzero, as in the construction
from a nonzero starting gradient. -/
theorem theorem_7_5_12 {n : ℕ} {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hT : T.IsUnreducedUpperHessenberg) (hS : T.IsSymm) {γ : ℝ} (hγ : γ ≠ 0)
    {θ : ℝ} {v : Fin (n + 1) → ℝ} (hv : T *ᵥ v = θ • v) (hv₀ : v ≠ 0) :
    (Pi.single (0 : Fin (n + 1)) γ) ⬝ᵥ v ≠ 0 := by
  simpa only [single_dotProduct] using
    mul_ne_zero hγ (lemma_7_5_11 hT hS hv hv₀)

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
    exact (mul_ne_zero (lemma_7_5_11 hT hS hev hv₀) (neg_ne_zero.mpr hγ)) hdot.symm
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

end ConnGouldToint.Chapter07
