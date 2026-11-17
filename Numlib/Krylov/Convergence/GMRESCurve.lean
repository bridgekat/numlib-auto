/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Convergence.GMRES
import Numlib.LinearAlgebra.Matrix.Companion

/-!
# Prescribed GMRES convergence curves

A companion matrix in a basis formed by the right-hand side and the first standard
coordinate vectors realizes a prescribed characteristic polynomial. In this basis
the mapped Krylov spaces are coordinate prefixes, so the squared GMRES residual
norms are sums of the squared coordinates outside these prefixes.
-/

open Finset Polynomial

namespace Matrix

variable {R : Type*} [CommRing R]

/-- A companion matrix with the negated coefficients in the last column
and ones on the subdiagonal. It is the transpose of the first-row
companion matrix with the row and column order both reversed. -/
def companionLastColumn (n : ℕ) (p : R[X]) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.reindex Fin.revPerm Fin.revPerm (Matrix.companion p (n + 1)).transpose

/-- Each column before the last shifts a standard coordinate vector to its successor. -/
theorem companionLastColumn_castSucc (n : ℕ) (p : R[X]) (i : Fin (n + 1)) (j : Fin n) :
    companionLastColumn n p i j.castSucc = if i = j.succ then 1 else 0 := by
  change Matrix.companion p (n + 1) j.castSucc.rev i.rev = _
  rw [Fin.rev_castSucc, Matrix.companion_apply]
  have hindex : j.rev.val + 1 = i.rev.val + 1 ↔ i = j.succ := by
    rw [Nat.add_right_cancel_iff, ← Fin.val_castSucc j.rev, ← Fin.rev_succ,
      ← Fin.ext_iff, Fin.rev_inj, eq_comm]
  simp only [Fin.val_succ, Nat.add_one_ne_zero, ↓reduceIte, hindex]

/-- The last column of the companion matrix lists the negated coefficients in ascending order. -/
theorem companionLastColumn_last (n : ℕ) (p : R[X]) (i : Fin (n + 1)) :
    companionLastColumn n p i (Fin.last n) = -p.coeff i.val := by
  change Matrix.companion p (n + 1) (Fin.last n).rev i.rev = _
  rw [Fin.rev_last, Matrix.companion_zero_apply]
  congr 2
  have hi := Fin.rev_add_cast i
  omega

/-- The last-column companion matrix of a monic polynomial has that characteristic polynomial. -/
theorem charpoly_companionLastColumn (n : ℕ) (p : R[X]) (hp : p.Monic)
    (hd : p.natDegree = n + 1) :
    (companionLastColumn n p).charpoly = p := by
  rw [companionLastColumn, Matrix.charpoly_reindex, Matrix.charpoly_transpose,
    Matrix.charpoly_companion hp hd]

end Matrix

namespace Krylov

private abbrev Space (n : ℕ) := EuclideanSpace ℂ (Fin (n + 1))

private theorem finCons_linearIndependent {n : ℕ} {b : Space n} (hb : b (Fin.last n) ≠ 0) :
    LinearIndependent ℂ (Fin.cons b (fun j : Fin n =>
      EuclideanSpace.basisFun (Fin (n + 1)) ℂ j.castSucc)) := by
  let w := EuclideanSpace.basisFun (Fin (n + 1)) ℂ
  apply LinearIndependent.finCons
  · exact w.toBasis.linearIndependent.comp Fin.castSucc (Fin.castSucc_injective n)
  · intro h
    apply hb
    have ho : w (Fin.last n) ∈
        (Submodule.span ℂ (Set.range fun j : Fin n => w j.castSucc))ᗮ := by
      apply Submodule.mem_orthogonal_span.2
      rintro _ ⟨j, rfl⟩
      have hj : j.castSucc ≠ Fin.last n := by
        intro e
        have he := congrArg Fin.val e
        have hj := j.isLt
        simp only [Fin.val_castSucc, Fin.val_last] at he
        omega
      rw [orthonormal_iff_ite.mp w.orthonormal, ite_eq_right hj]
    have he := (Submodule.mem_orthogonal' _ _).1 ho b h
    rw [← OrthonormalBasis.repr_apply_apply] at he
    exact he

private theorem map_krylov_eq_span_prefix {n : ℕ} {A : Module.End ℂ (Space n)}
    {b : Space n} {w : Fin (n + 1) → Space n}
    (hshift : ∀ j : Fin n, A ((A ^ j.val) b) = w j.castSucc) (k : Fin (n + 1)) :
    (subspace A b k.val).map A = Submodule.span ℂ (w '' {j | j.val < k.val}) := by
  rw [subspace, Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    have hj := j.isLt
    have hk := k.isLt
    let j' : Fin n := ⟨j.val, by omega⟩
    exact ⟨j'.castSucc, hj, (hshift j').symm⟩
  · rintro ⟨j, hj, rfl⟩
    have hj' : j.val < k.val := hj
    have hk := k.isLt
    let j' : Fin n := ⟨j.val, by omega⟩
    refine ⟨(A ^ j.val) b, ⟨⟨j.val, hj'⟩, rfl⟩, ?_⟩
    exact (hshift j').trans (congrArg w (Fin.ext rfl))

/-- The squared norm after removing the first $k$ standard coordinates is the sum
of the squares of the remaining coordinate norms. -/
theorem norm_sq_sub_coordinate_prefix {n : ℕ} (b : EuclideanSpace ℂ (Fin (n + 1))) (k : ℕ) :
    ‖b - ∑ i : Fin (n + 1) with i.val < k,
        (b i) • EuclideanSpace.basisFun (Fin (n + 1)) ℂ i‖ ^ 2 =
      ∑ i : Fin (n + 1) with k ≤ i.val, ‖b i‖ ^ 2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  have he : (∑ j : Fin (n + 1) with j.val < k,
      (b j) • EuclideanSpace.basisFun (Fin (n + 1)) ℂ j) i =
        if i.val < k then b i else 0 := by
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    simp only [PiLp.smul_apply, EuclideanSpace.basisFun_apply, PiLp.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hi : i.val < k
    · rw [ite_eq_left hi, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Ne.symm hj]
      · exact fun ho => (ho (by simpa using hi)).elim
    · rw [ite_eq_right hi]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hji : j ≠ i := by
        rintro rfl
        exact hi (by simpa using hj)
      simp [Ne.symm hji]
  rw [PiLp.sub_apply, he]
  by_cases hi : i.val < k
  · simp [hi, not_le.mpr hi]
  · simp [hi, le_of_not_gt hi]

private def curveExtension {n : ℕ} (f : Fin (n + 1) → ℝ) (k : ℕ) : ℝ :=
  if h : k < n + 1 then f ⟨k, h⟩ else 0

private theorem curveExtension_coe {n : ℕ} (f : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    curveExtension f i.val = f i := dite_eq_left i.isLt

private theorem curveExtension_end {n : ℕ} (f : Fin (n + 1) → ℝ) :
    curveExtension f (n + 1) = 0 := dite_eq_right (Nat.lt_irrefl _)

/-- The nonnegative coordinates associated with a GMRES residual curve $f$ are
$g_i=\sqrt{f_i^2-f_{i+1}^2}$, where the extended last value $f_{n+1}$ is zero. -/
noncomputable def gmresCurveCoordinates {n : ℕ} (f : Fin (n + 1) → ℝ) :
    EuclideanSpace ℂ (Fin (n + 1)) :=
  WithLp.toLp 2 fun i =>
    (Real.sqrt (curveExtension f i.val ^ 2 - curveExtension f (i.val + 1) ^ 2) : ℂ)

/-- Before the last index, the coordinate is the square root of the difference
of the two successive squared residual norms. -/
theorem gmresCurveCoordinates_castSucc {n : ℕ} (f : Fin (n + 1) → ℝ) (i : Fin n) :
    gmresCurveCoordinates f i.castSucc =
      (Real.sqrt (f i.castSucc ^ 2 - f i.succ ^ 2) : ℂ) := by
  change (Real.sqrt (curveExtension f i.castSucc.val ^ 2 -
    curveExtension f i.succ.val ^ 2) : ℂ) = _
  rw [curveExtension_coe, curveExtension_coe]

/-- The final coordinate is the final residual norm when it is nonnegative. -/
theorem gmresCurveCoordinates_last {n : ℕ} (f : Fin (n + 1) → ℝ)
    (hf : 0 ≤ f (Fin.last n)) : gmresCurveCoordinates f (Fin.last n) = (f (Fin.last n) : ℂ) := by
  change (Real.sqrt (curveExtension f (Fin.last n).val ^ 2 -
    curveExtension f (n + 1) ^ 2) : ℂ) = _
  rw [curveExtension_coe, curveExtension_end, zero_pow (by decide), sub_zero, Real.sqrt_sq hf]

/-- The sum of the squared coordinate norms from index $k$ onward equals $f_k^2$. -/
theorem sum_norm_sq_gmresCurveCoordinates {n : ℕ} (f : Fin (n + 1) → ℝ)
    (hf : Antitone f) (hpos : 0 ≤ f (Fin.last n)) (k : Fin (n + 1)) :
    (∑ i : Fin (n + 1) with k.val ≤ i.val, ‖gmresCurveCoordinates f i‖ ^ 2) = f k ^ 2 := by
  let q := curveExtension f
  have hqnonneg (k : ℕ) : 0 ≤ q k := by
    dsimp only [q, curveExtension]
    split
    · exact hpos.trans (hf (Fin.le_last _))
    · exact le_rfl
  have hqanti : Antitone q := by
    intro i j hij
    by_cases hj : j < n + 1
    · rw [show q j = f ⟨j, hj⟩ from dite_eq_left hj,
        show q i = f ⟨i, hij.trans_lt hj⟩ from dite_eq_left (hij.trans_lt hj)]
      exact hf hij
    · rw [show q j = 0 from dite_eq_right hj]
      exact hqnonneg i
  have hb (i : Fin (n + 1)) :
      ‖gmresCurveCoordinates f i‖ ^ 2 = q i.val ^ 2 - q (i.val + 1) ^ 2 := by
    change ‖(Real.sqrt _ : ℂ)‖ ^ 2 = _
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt]
    exact sub_nonneg.mpr (pow_le_pow_left₀ (hqnonneg _) (hqanti (Nat.le_succ _)) _)
  simp_rw [hb]
  rw [Finset.sum_filter]
  let g (i : ℕ) := if k.val ≤ i then q i ^ 2 - q (i + 1) ^ 2 else 0
  change (∑ i : Fin (n + 1), g i.val) = _
  rw [Fin.sum_univ_eq_sum_range g, show g = _ from rfl, ← Finset.sum_filter]
  have hIco : (Finset.range (n + 1)).filter (fun i => k.val ≤ i) =
      Finset.Ico k.val (n + 1) := by
    ext i
    simp [and_comm]
  rw [hIco, Finset.sum_Ico_eq_sub _ k.isLt.le, Finset.sum_range_sub' (fun i => q i ^ 2),
    Finset.sum_range_sub' (fun i => q i ^ 2),
    show q (n + 1) = 0 from curveExtension_end f, show q k.val = f k from curveExtension_coe f k]
  ring

/-- Every positive nonincreasing GMRES residual norm curve up to step $n$ can
occur for a linear system of dimension $n+1$ with any prescribed nonzero
complex eigenvalues, including repetitions. The initial iterate is zero. -/
theorem exists_gmres_curve_and_charpoly (n : ℕ) (f : Fin (n + 1) → ℝ)
    (hf : Antitone f) (hpos : 0 < f (Fin.last n))
    (μ : Fin (n + 1) → ℂ) (hμ : ∀ i, μ i ≠ 0) :
    ∃ (A : Module.End ℂ (EuclideanSpace ℂ (Fin (n + 1))))
      (b : EuclideanSpace ℂ (Fin (n + 1)))
      (x : ℕ → EuclideanSpace ℂ (Fin (n + 1))),
      A.charpoly = (∏ i, (X - C (μ i))) ∧ Function.Injective A ∧ ‖b‖ = f 0 ∧
      (∀ k, IsMinResidualIterate A b 0 k (x k)) ∧
      ∀ k : Fin (n + 1), ‖b - A (x k.val)‖ = f k := by
  classical
  have hfpos (i : Fin (n + 1)) : 0 < f i :=
    hpos.trans_le (hf (Fin.le_last i))
  let b := gmresCurveCoordinates f
  have hblast : b (Fin.last n) ≠ 0 := by
    exact (gmresCurveCoordinates_last f hpos.le).symm ▸ Complex.ofReal_ne_zero.mpr hpos.ne'
  let w := EuclideanSpace.basisFun (Fin (n + 1)) ℂ
  let V := basisOfLinearIndependentOfCardEqFinrank (finCons_linearIndependent hblast)
    (by simp)
  have hV : ⇑V = Fin.cons b (fun j : Fin n => w j.castSucc) :=
    coe_basisOfLinearIndependentOfCardEqFinrank _ _
  let p : ℂ[X] := ∏ i, (X - C (μ i))
  have hp : p.Monic := by
    exact monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (μ i)
  have hdeg : p.natDegree = n + 1 := by
    simp [p, natDegree_finsetProd_X_sub_C_eq_card]
  let A := Matrix.toLin V V (Matrix.companionLastColumn n p)
  have hchar : A.charpoly = p := by
    rw [← LinearMap.charpoly_toMatrix A V, show
      LinearMap.toMatrix V V A = Matrix.companionLastColumn n p from LinearMap.toMatrix_toLin V V _]
    exact Matrix.charpoly_companionLastColumn n p hp hdeg
  have hinj : Function.Injective A := by
    have hconst : p.eval 0 ≠ 0 := by
      simp only [p, eval_prod, eval_sub, eval_X, eval_C, zero_sub]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => neg_ne_zero.mpr (hμ i)
    rw [← hchar, LinearMap.eval_charpoly, map_zero, zero_sub] at hconst
    have hu : IsUnit (-A) :=
      (LinearMap.isUnit_iff_isUnit_det (-A)).2 (isUnit_iff_ne_zero.2 hconst)
    exact ((Module.End.isUnit_iff A).1 (by simpa using hu)).injective
  have hAV (i : Fin n) : A (V i.castSucc) = V i.succ := by
    rw [Matrix.toLin_self]
    simp only [Matrix.companionLastColumn_castSucc, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_eq_single i.succ]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  have hpower (i : Fin (n + 1)) : (A ^ i.val) b = V i := by
    induction i using Fin.induction with
    | zero => simp [hV]
    | succ i hi =>
      rw [Fin.val_succ, pow_succ', Module.End.mul_apply, ← Fin.val_castSucc i, hi, hAV]
  have hshift (i : Fin n) : A ((A ^ i.val) b) = w i.castSucc := by
    rw [← Fin.val_castSucc i, hpower, hAV, hV, Fin.cons_succ]
  have hnorm (k : Fin (n + 1)) :
      ‖b - ∑ i : Fin (n + 1) with i.val < k.val, (b i) • w i‖ = f k := by
    apply (sq_eq_sq₀ (norm_nonneg _) (hfpos _).le).mp
    exact (norm_sq_sub_coordinate_prefix b k.val).trans
      (sum_norm_sq_gmresCurveCoordinates f hf hpos.le k)
  choose x hx using fun k : ℕ => exists_isMinResidualIterate A b 0 k
  refine ⟨A, b, x, hchar, hinj, ?_, hx, ?_⟩
  · simpa using hnorm (0 : Fin (n + 1))
  · intro k
    have hs := (map_krylov_eq_span_prefix hshift k).symm
    have hr := (hx k.val).residual_eq_sub_sum_prefix w.orthonormal (by simpa using hs)
    simp only [map_zero, sub_zero, ← OrthonormalBasis.repr_apply_apply] at hr
    rw [hr]
    exact hnorm k

end Krylov
