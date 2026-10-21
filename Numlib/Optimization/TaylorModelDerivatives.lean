import Numlib.Analysis.Calculus.IteratedFDerivSymmetry
import Numlib.Optimization.RegularizedTaylorModel
import Mathlib.Logic.Equiv.Fintype

/-!
# Derivatives of canonical Taylor models

The unrestricted derivative formula is a sum over injections selecting multilinear slots.
Finite smoothness makes the coefficients symmetric and collects these terms into the
contracted tensor formula. In particular, differentiating a degree-`p + 1` model gives
the degree-`p` model of the derivative.
-/

open scoped Nat ContDiff

namespace Optimization.RegularizedTaylorModel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every order of derivative of a Taylor model, expressed by differentiating each
multilinear coefficient after composition with the diagonal linear map. This formula
does not require any smoothness of the original function. -/
theorem iteratedFDeriv_taylorModel_apply (f : E → F) (p j : ℕ) (x s : E) (v : Fin j → E) :
    iteratedFDeriv ℝ j (taylorModel f p x) s v =
      ∑ k ∈ Finset.range (p + 1), (k ! : ℝ)⁻¹ •
        (iteratedFDeriv ℝ j (iteratedFDeriv ℝ k f x) (fun _ ↦ s))
          (fun i _ ↦ v i) := by
  unfold taylorModel
  have hcoeff (k : ℕ) : ContDiff ℝ j (fun z : E ↦
      (k ! : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ ↦ z)) :=
    ((iteratedFDeriv ℝ k f x).contDiff.comp
      (contDiff_pi.mpr fun _ : Fin k ↦ contDiff_id)).const_smul _
  rw [iteratedFDeriv_fun_sum_apply (f := fun k z ↦
      (k ! : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ ↦ z))
    (fun k _ ↦ (hcoeff k).contDiffAt)]
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [iteratedFDeriv_const_smul_apply' (f := fun z : E ↦
      iteratedFDeriv ℝ k f x (fun _ ↦ z))
    (((iteratedFDeriv ℝ k f x).contDiff.comp
      (contDiff_pi.mpr fun _ : Fin k ↦ contDiff_id)).contDiffAt), smul_apply]
  congr 1
  let Δ : E →L[ℝ] (Fin k → E) := ContinuousLinearMap.pi (fun _ ↦ ContinuousLinearMap.id ℝ E)
  change (iteratedFDeriv ℝ j ((iteratedFDeriv ℝ k f x) ∘ Δ) s) v = _
  rw [Δ.iteratedFDeriv_comp_right (iteratedFDeriv ℝ k f x).contDiff s (le_refl (j : ℕ∞ω))]
  rfl

/-- The all-orders slot formula for model derivatives, summed over the injections that
select distinct multilinear slots. It works without symmetry assumptions. -/
theorem iteratedFDeriv_taylorModel_slot_sum (f : E → F) (p j : ℕ) (x s : E)
    (v : Fin j → E) :
    iteratedFDeriv ℝ j (taylorModel f p x) s v =
      ∑ k ∈ Finset.range (p + 1), (k ! : ℝ)⁻¹ •
        ∑ e : Fin j ↪ Fin k, iteratedFDeriv ℝ k f x
          (fun l ↦ if h : l ∈ Set.range e then v (e.toEquivRange.symm ⟨l, h⟩) else s) := by
  classical
  rw [iteratedFDeriv_taylorModel_apply]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [(iteratedFDeriv ℝ k f x).iteratedFDeriv_eq]
  simp only [ContinuousMultilinearMap.iteratedFDeriv, sum_apply,
    ContinuousMultilinearMap.iteratedFDerivComponent_apply, Pi.compRightL_apply, Set.mem_range]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  funext l
  split_ifs with h
  · congr 1
    apply e.injective
    exact congrArg Subtype.val ((@Equiv.apply_symm_apply _ _
      (@Function.Embedding.toEquivRange (Fin j) (Fin k) _
        (fun a b ↦ Classical.propDecidable (a = b)) e)
        ⟨l, h⟩).trans ((e.toEquivRange.apply_symm_apply ⟨l, h⟩).symm))
  · rfl

end Optimization.RegularizedTaylorModel

open scoped Nat ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Symmetry makes the terms of the injection formula for a diagonal homogeneous
polynomial equal. The unselected slots contain the fixed displacement. -/
theorem ContinuousMultilinearMap.sum_embedding_apply_eq_descFactorial {j k : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) F)
    (hA : ∀ (σ : Equiv.Perm (Fin k)) (m : Fin k → E), A (m ∘ σ) = A m)
    (hjk : j ≤ k) (s : E) (v : Fin j → E) :
    (∑ e : Fin j ↪ Fin k, A
      (fun l ↦ if h : l ∈ Set.range e then v (e.toEquivRange.symm ⟨l, h⟩) else s)) =
      (Nat.descFactorial k j) • A (fun l ↦ if h : (l : ℕ) < j then v ⟨l, h⟩ else s) := by
  classical
  have he (e : Fin j ↪ Fin k) : A
      (fun l ↦ if h : l ∈ Set.range e then v (e.toEquivRange.symm ⟨l, h⟩) else s) =
      A (fun l ↦ if h : (l : ℕ) < j then v ⟨l, h⟩ else s) := by
    let c : Fin j ↪ Fin k := Fin.castLEEmb hjk
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair c e c.injective e.injective
    rw [← hA σ]
    congr 1
    funext l
    dsimp only [Function.comp_def]
    by_cases hl : (l : ℕ) < j
    · let a : Fin j := ⟨l, hl⟩
      have hla : c a = l := rfl
      have hσl : σ l = e a := by rw [← hla]; exact hσ a
      simp only [hσl, Set.mem_range_self, ↓reduceDIte, hl]
      congr 1
      exact Function.Embedding.toEquivRange_symm_apply_self e a
    · have hnot : σ l ∉ Set.range e := by
        rintro ⟨a, ha⟩
        have : c a = l := σ.injective ((hσ a).trans ha)
        have hv := congrArg Fin.val this
        exact hl (hv ▸ a.isLt)
      simp only [hnot, ↓reduceDIte, hl]
  simp_rw [he]
  simp
namespace Optimization.RegularizedTaylorModel

/-- All derivatives of a Taylor model are contractions of the original derivative tensors.
Finite smoothness supplies exactly the symmetry needed to collect the slot sum. -/
theorem iteratedFDeriv_taylorModel_contraction {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {p j : ℕ} {x : E} (hf : ContDiffAt ℝ p f x)
    (s : E) (v : Fin j → E) :
    iteratedFDeriv ℝ j (taylorModel f p x) s v =
      ∑ k ∈ Finset.range (p + 1), if _h : j ≤ k then
        ((k - j)! : ℝ)⁻¹ • iteratedFDeriv ℝ k f x
          (fun l ↦ if h : (l : ℕ) < j then v ⟨l, h⟩ else s)
        else 0 := by
  classical
  rw [iteratedFDeriv_taylorModel_slot_sum]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hjk : j ≤ k
  · have hfk : ContDiffAt ℝ k f x :=
      hf.of_le (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    rw [dite_eq_left hjk, (iteratedFDeriv ℝ k f x).sum_embedding_apply_eq_descFactorial
      (fun σ m ↦ hfk.iteratedFDeriv_comp_perm_of_nat σ m)
      hjk s v, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    have hfac : ((k - j)! : ℝ) * (Nat.descFactorial k j : ℝ) = (k ! : ℝ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial hjk
    have hk0 : (k ! : ℝ) ≠ 0 := by positivity
    have hkj0 : ((k - j)! : ℝ) ≠ 0 := by positivity
    field_simp
    nlinarith
  · rw [dite_eq_right hjk]
    have : IsEmpty (Fin j ↪ Fin k) := ⟨fun e ↦ hjk (by
      simpa using Fintype.card_le_of_injective e e.injective)⟩
    simp

end Optimization.RegularizedTaylorModel

namespace Optimization.RegularizedTaylorModel

/-- Differentiating a Taylor model gives the Taylor model of the derivative, with one
less degree. The only hypothesis is finite smoothness at the expansion point. -/
theorem fderiv_taylorModel_eq_taylorModel_fderiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {p : ℕ} {x : E} (hf : ContDiffAt ℝ (p + 1) f x) (s : E) :
    fderiv ℝ (taylorModel f (p + 1) x) s = taylorModel (fderiv ℝ f) p x s := by
  ext v
  have h := iteratedFDeriv_taylorModel_contraction (j := 1) hf s (fun _ ↦ v)
  simp only [iteratedFDeriv_one_apply] at h
  rw [h, Finset.sum_range_succ']
  simp only [show ¬(1 ≤ (0 : ℕ)) by omega, ↓reduceDIte, add_zero, Nat.succ_le_succ_iff,
    Nat.zero_le, Nat.add_sub_cancel]
  unfold taylorModel
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [smul_apply]
  congr 1
  have hr : iteratedFDeriv ℝ (k + 1) f x (Fin.snoc (fun _ : Fin k ↦ s) v) =
      iteratedFDeriv ℝ k (fderiv ℝ f) x (fun _ ↦ s) v := by
    rw [iteratedFDeriv_succ_apply_right]
    simp
  rw [← hr]
  have hs := (hf.of_le (by exact_mod_cast (Nat.succ_le_succ
    (Nat.le_of_lt_succ (Finset.mem_range.mp hk))))).iteratedFDeriv_comp_perm_of_nat
      Fin.revPerm (Fin.snoc (fun _ : Fin k ↦ s) v)
  rw [← hs]
  congr 1
  funext l
  by_cases hl : (l : ℕ) < 1
  · have hl0 : l = 0 := Fin.ext (by simpa using Nat.lt_one_iff.mp hl)
    subst l
    simp
  · have hl0 : l ≠ 0 := by intro he; simp [he] at hl
    have hr : Fin.rev l ≠ Fin.last k := by
      intro he
      have he' := congrArg Fin.rev he
      simp only [Fin.rev_rev, Fin.rev_last] at he'
      exact hl0 he'
    simp only [hl, ↓reduceDIte, Function.comp_def, Fin.revPerm_apply]
    rw [← Fin.castSucc_castPred (Fin.rev l) hr, Fin.snoc_castSucc]

end Optimization.RegularizedTaylorModel
