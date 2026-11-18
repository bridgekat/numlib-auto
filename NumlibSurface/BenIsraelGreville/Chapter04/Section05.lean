/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter04.Section02
import NumlibSurface.BenIsraelGreville.Chapter04.Section03
import NumlibSurface.BenIsraelGreville.Chapter04.Section04
import Mathlib.RingTheory.Nilpotent.Basic
import Numlib.LinearAlgebra.Eigenspace.Spectral

/-!
# Spectral properties of the group inverse

Section 4.5 of [benIsrael2003generalized] relates generalized
eigenvectors and their grades at reciprocal eigenvalues.
-/

namespace BenIsraelGreville.Chapter04

open Matrix Module

variable {n : Type*} [Fintype n] [DecidableEq n]

private abbrev matrixEnd (A : Matrix n n ℂ) : End ℂ (n → ℂ) := A.mulVecLin

/-- A generalized eigenvector of grade `p` belongs to the `p`th generalized
eigenspace and fails to belong to the preceding one. -/
def IsVectorOfGrade (A : Matrix n n ℂ) (μ : ℂ) (v : n → ℂ) (p : ℕ) : Prop :=
  0 < p ∧ v ∈ (matrixEnd A).genEigenspace μ p ∧ v ∉ (matrixEnd A).genEigenspace μ (p - 1 : ℕ)

/-- At zero, the grade compares consecutive powers of the matrix. -/
@[simp] theorem isVectorOfGrade_zero_iff (A : Matrix n n ℂ) (v : n → ℂ) (p : ℕ) :
    IsVectorOfGrade A 0 v p ↔ IsZeroVectorOfGrade A v p := by
  simp only [IsVectorOfGrade, IsZeroVectorOfGrade, End.mem_genEigenspace_nat,
    zero_smul, sub_zero, matrixEnd, ← toLin'_apply', ← toLin'_pow, LinearMap.mem_ker, toLin'_apply]

private theorem genEigenspace_pow_surj {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : End ℂ V) {μ : ℂ} (hμ : μ ≠ 0) (p l : ℕ)
    {v : V} (hv : v ∈ f.genEigenspace μ p) :
    ∃ w ∈ f.genEigenspace μ p, (f ^ l) w = v := by
  let S := f.genEigenspace μ p
  have hF : Set.MapsTo f S S := End.mapsTo_genEigenspace_of_comm (Commute.refl f) μ p
  let g := f.restrict hF
  have hshift : IsNilpotent (g - μ • 1) := by
    have hn := f.isNilpotent_restrict_genEigenspace_nat μ p
    have hFS : Set.MapsTo (f - μ • (1 : End ℂ V)) S S :=
      End.mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ p
    have he : (f - μ • 1).restrict hFS = (g - μ • 1 : End ℂ S) := by
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      rfl
    exact he ▸ hn
  have hu : IsUnit (μ • (1 : End ℂ S)) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (isUnit_iff_ne_zero.mpr hμ).map (algebraMap ℂ _)
  have hg : IsUnit g := by
    have hc : Commute (g - μ • 1) (μ • 1) := by
      rw [← Algebra.algebraMap_eq_smul_one]
      exact Algebra.commute_algebraMap_right _ _
    rw [← sub_add_cancel g (μ • 1)]
    exact hshift.isUnit_add_right_of_commute hu hc
  have ht : Function.Surjective (g ^ l : End ℂ S) :=
    LinearMap.range_eq_top.mp ((LinearMap.isUnit_iff_range_eq_top _).mp (hg.pow l))
  obtain ⟨w, hw⟩ := ht ⟨v, hv⟩
  refine ⟨w, w.property, ?_⟩
  change ((f.restrict hF) ^ l) w = _ at hw
  rw [End.pow_restrict l hF] at hw
  exact congrArg Subtype.val hw

/-- **Lemma 3** of [benIsrael2003generalized], Chapter 4.
The generalized eigenspace for a nonzero eigenvalue is contained in the
range of every power of the matrix. -/
theorem lemma_4_3 (A : Matrix n n ℂ) {μ : ℂ} (hμ : μ ≠ 0) (p l : ℕ) :
    (matrixEnd A).genEigenspace μ p ≤ LinearMap.range (A ^ l).mulVecLin := by
  intro v hv
  obtain ⟨w, _, hw⟩ := genEigenspace_pow_surj A.mulVecLin hμ p l hv
  exact ⟨w, by simpa only [← toLin'_apply', toLin'_pow] using hw⟩

private theorem shift_power_transfer {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {f g : End ℂ V} {μ : ℂ} (hμ : μ ≠ 0) {l : ℕ}
    (h : g * f ^ (l + 1) = f ^ l) (p : ℕ) {v : V} (hv : v ∈ f.genEigenspace μ p) (k : ℕ) :
    ((g - μ⁻¹ • 1) ^ k) v = 0 ↔ ((f - μ • 1) ^ k) v = 0 := by
  let S := f.genEigenspace μ p
  let F : End ℂ V := f - μ • 1
  let G : End ℂ V := g - μ⁻¹ • 1
  have hF : Set.MapsTo F S S :=
    End.mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ p
  have hgf (u : V) (hu : u ∈ S) : g (f u) = u := by
    obtain ⟨w, _, hw⟩ := genEigenspace_pow_surj f hμ p l hu
    have hh := DFunLike.congr_fun h w
    change g ((f ^ (l + 1)) w) = (f ^ l) w at hh
    rw [pow_succ', End.mul_apply, hw] at hh
    exact hh
  have hg₁ (u : V) (hu : u ∈ S) : g u ∈ S ∧ f (g u) = u := by
    obtain ⟨w, hw, he⟩ := genEigenspace_pow_surj f hμ p 1 hu
    rw [pow_one] at he
    rw [← he, hgf w hw]
    exact ⟨hw, rfl⟩
  have hshift (u : V) (hu : u ∈ S) : G u = -μ⁻¹ • g (F u) := by
    change g u - μ⁻¹ • u = -μ⁻¹ • g (f u - μ • u)
    rw [map_sub, map_smul, hgf u hu, smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hμ,
      neg_one_smul, neg_smul]
    abel
  have hcomm : Commute G g :=
    (Commute.refl g).sub_left (Algebra.commute_algebraMap_left μ⁻¹ g)
  have hFx (j : ℕ) : (F ^ j) v ∈ S := by
    induction j with
    | zero => simpa only [pow_zero, End.one_apply] using hv
    | succ j ih => rw [pow_succ', End.mul_apply]; exact hF ih
  have hpows (j : ℕ) : (G ^ j) v = (-μ⁻¹) ^ j • (g ^ j) ((F ^ j) v) := by
    induction j with
    | zero => simp [End.one_apply]
    | succ j ih =>
      rw [pow_succ' G, End.mul_apply, ih, map_smul, ← End.mul_apply, (hcomm.pow_right j).eq,
        End.mul_apply, hshift _ (hFx j), map_smul, smul_smul,
        ← pow_succ, ← End.mul_apply, ← pow_succ g]
      simp only [pow_succ' F, End.mul_apply]
  have hgzero (j : ℕ) (u : V) (hu : u ∈ S) : (g ^ j) u = 0 ↔ u = 0 := by
    induction j generalizing u with
    | zero => simp [End.one_apply]
    | succ j ih =>
      rw [pow_succ, End.mul_apply, ih _ (hg₁ u hu).1]
      constructor
      · intro h0
        calc u = f (g u) := (hg₁ u hu).2.symm
          _ = 0 := by rw [h0, map_zero]
      · intro h0
        rw [h0, map_zero]
  change (G ^ k) v = 0 ↔ (F ^ k) v = 0
  rw [hpows, smul_eq_zero, or_iff_right (pow_ne_zero k (neg_ne_zero.mpr (inv_ne_zero hμ)))]
  exact hgzero k _ (hFx k)

/-- **Lemma 4** of [benIsrael2003generalized], Chapter 4.
A solution of the left power equation preserves nonzero generalized
eigenvectors at reciprocal eigenvalues, with their exact grades. -/
theorem lemma_4_4 (A X : Matrix n n ℂ) {l : ℕ} (h : X * A ^ (l + 1) = A ^ l)
    {μ : ℂ} (hμ : μ ≠ 0) {v : n → ℂ} {p : ℕ} (hv : IsVectorOfGrade A μ v p) :
    IsVectorOfGrade X μ⁻¹ v p := by
  have h' : matrixEnd X * matrixEnd A ^ (l + 1) = matrixEnd A ^ l := by
    let e : Matrix n n ℂ ≃ₐ[ℂ] End ℂ (n → ℂ) := toLinAlgEquiv'
    have he := congrArg e h
    have he' (M : Matrix n n ℂ) : e M = matrixEnd M := by ext v; rfl
    rw [map_mul, map_pow, map_pow] at he
    simpa only [he'] using he
  obtain ⟨hp, hv, hn⟩ := hv
  refine ⟨hp, ?_, ?_⟩
  · rw [End.mem_genEigenspace_nat, LinearMap.mem_ker, shift_power_transfer hμ h' p hv]
    exact LinearMap.mem_ker.mp (End.mem_genEigenspace_nat.mp hv)
  · rw [End.mem_genEigenspace_nat, LinearMap.mem_ker, shift_power_transfer hμ h' p hv]
    exact fun he => hn (End.mem_genEigenspace_nat.mpr (LinearMap.mem_ker.mpr he))

/-- **Definition 2** of [benIsrael2003generalized], Chapter 4.
Spectral inverses match all generalized eigenvectors and their grades
at reciprocal eigenvalues, including zero. -/
def IsSInverse (A X : Matrix n n ℂ) : Prop :=
  ∀ μ v p, IsVectorOfGrade A μ v p ↔ IsVectorOfGrade X μ⁻¹ v p

omit [DecidableEq n] in
/-- Spectral inversion is symmetric. -/
theorem IsSInverse.symm {A X : Matrix n n ℂ} (h : IsSInverse A X) : IsSInverse X A := by
  intro μ v p
  simpa only [inv_inv] using (h μ⁻¹ v p).symm

omit [DecidableEq n] in
/-- Maximal generalized eigenspace membership consists of zero and
the generalized eigenvectors of some finite positive grade. -/
theorem mem_maxGenEigenspace_iff_exists_grade (A : Matrix n n ℂ) (μ : ℂ) (v : n → ℂ) :
    v ∈ End.maxGenEigenspace A.mulVecLin μ ↔ v = 0 ∨ ∃ p, IsVectorOfGrade A μ v p := by
  classical
  constructor
  · intro hv
    by_cases hzero : v = 0
    · exact Or.inl hzero
    let f := matrixEnd A
    have h : ∃ p : ℕ, v ∈ f.genEigenspace μ p := by
      obtain ⟨p, hp⟩ := (End.mem_maxGenEigenspace f μ v).mp hv
      exact ⟨p, End.mem_genEigenspace_nat.mpr (LinearMap.mem_ker.mpr hp)⟩
    refine Or.inr ⟨Nat.find h, ?_, Nat.find_spec h, ?_⟩
    · by_contra! hh
      have hs := Nat.find_spec h
      rw [Nat.eq_zero_of_le_zero hh, Nat.cast_zero, End.genEigenspace_zero,
        Submodule.mem_bot] at hs
      exact hzero hs
    · intro hp
      have hpos : 0 < Nat.find h := by
        by_contra! hh
        have hs := Nat.find_spec h
        rw [Nat.eq_zero_of_le_zero hh, Nat.cast_zero, End.genEigenspace_zero,
          Submodule.mem_bot] at hs
        exact hzero hs
      have hn := Nat.find_min' h hp
      omega
  · rintro (rfl | ⟨p, _, hv, _⟩)
    · exact Submodule.zero_mem _
    · exact End.genEigenspace_le_maximal _ _ _ hv

omit [DecidableEq n] in
/-- Matching all exact grades is enough to match the maximal generalized eigenspaces. -/
theorem maxGenEigenspace_eq_of_grade_iff {A X : Matrix n n ℂ} {μ ν : ℂ}
    (h : ∀ v p, IsVectorOfGrade A μ v p ↔ IsVectorOfGrade X ν v p) :
    End.maxGenEigenspace A.mulVecLin μ = End.maxGenEigenspace X.mulVecLin ν := by
  ext v
  simp only [mem_maxGenEigenspace_iff_exists_grade, h]

/-- The maximal zero-eigenspace is the kernel of any power at or
above the stabilization index. -/
theorem maxGenEigenspace_zero_eq_stableKer (A : Matrix n n ℂ) {l : ℕ} (hl : matrixIndex A ≤ l) :
    End.maxGenEigenspace A.mulVecLin 0 = (A ^ l).mulVecLin.ker := by
  ext v
  have hmem (k : ℕ) : ((matrixEnd A - (0 : ℂ) • 1) ^ k) v = 0 ↔
      v ∈ (A ^ k).mulVecLin.ker := by
    simp only [zero_smul, sub_zero, matrixEnd, ← toLin'_apply', ← toLin'_pow, LinearMap.mem_ker]
  change v ∈ (matrixEnd A).maxGenEigenspace 0 ↔ _
  rw [End.mem_maxGenEigenspace]
  simp only [hmem]
  constructor
  · rintro ⟨k, hk⟩
    by_cases hkl : k ≤ l
    · exact A.monotone_ker_mulVecLin_pow hkl hk
    · have hl' : 0 < l := A.rankStabilizationIndex_spec.1.trans_le hl
      have hls := (A.rank_pow_eq_succ_iff hl').mpr hl
      have heq := (A.rank_pow_eq_iff_ker_eq (le_of_not_ge hkl)).mp
        (A.rank_pow_eq_of_eq_succ hls (le_of_not_ge hkl))
      exact heq.symm ▸ hk
  · exact fun h => ⟨l, h⟩

/-- The stable range is the sum of the maximal generalized eigenspaces at
nonzero eigenvalues. -/
theorem stableRange_eq_nonzeroSpectralSubspace (A : Matrix n n ℂ) {l : ℕ}
    (hl : matrixIndex A ≤ l) :
    (A ^ l).mulVecLin.range = End.spectralSubspace A.mulVecLin (· ≠ 0) := by
  let f := matrixEnd A
  let R := (A ^ l).mulVecLin.range
  let K := (A ^ l).mulVecLin.ker
  let S := f.spectralSubspace (· ≠ 0)
  have hle : S ≤ R := by
    apply iSup₂_le
    intro μ hμ v hv
    obtain ⟨p, hp⟩ := (End.mem_maxGenEigenspace f μ v).mp hv
    have hv' : v ∈ f.genEigenspace μ p := End.mem_genEigenspace_nat.mpr (LinearMap.mem_ker.mpr hp)
    exact lemma_4_3 A hμ p l hv'
  have hdis : Disjoint R K :=
    ((A.isCompl_range_ker_pow_iff (A.rankStabilizationIndex_spec.1.trans_le hl)).mpr hl).disjoint
  have htop : S ⊔ K = ⊤ := by
    have h := (f.isCompl_spectralSubspace (· ≠ 0)).sup_eq_top
    simp only [ne_eq, not_not, End.spectralSubspace_eq] at h
    change S ⊔ (matrixEnd A).maxGenEigenspace 0 = ⊤ at h
    rw [show (matrixEnd A).maxGenEigenspace 0 = K from maxGenEigenspace_zero_eq_stableKer A hl] at h
    exact h
  refine le_antisymm ?_ hle
  intro v hv
  have hv' : v ∈ S ⊔ K := by rw [htop]; trivial
  obtain ⟨u, hu, w, hw, hsum⟩ := Submodule.mem_sup.mp hv'
  have hw' : w ∈ R := by
    have he : v - u = w := by rw [← hsum, add_sub_cancel_left]
    exact he ▸ R.sub_mem hv (hle hu)
  have hz := Submodule.disjoint_def.mp hdis _ hw' hw
  rw [hz, add_zero] at hsum
  exact hsum ▸ hu

omit [DecidableEq n] in
/-- Spectral inverses have the same kernel. -/
theorem IsSInverse.ker_eq {A X : Matrix n n ℂ} (h : IsSInverse A X) :
    A.mulVecLin.ker = X.mulVecLin.ker := by
  classical
  ext v
  by_cases hv : v = 0
  · simp [hv]
  have he := h 0 v 1
  rw [_root_.inv_zero, isVectorOfGrade_zero_iff, isVectorOfGrade_zero_iff] at he
  simpa only [IsZeroVectorOfGrade, Nat.one_pos, pow_one, Nat.sub_self, pow_zero,
    one_mulVec, ne_eq, hv, not_false_eq_true, and_true, true_and, LinearMap.mem_ker,
    mulVecLin_apply] using he

/-- Absence of generalized zero-eigenvectors of grade two forces index one. -/
theorem matrixIndex_eq_one_of_no_grade_two (A : Matrix n n ℂ)
    (h : ∀ v, ¬ IsVectorOfGrade A 0 v 2) : matrixIndex A = 1 := by
  have hk : (A ^ 1).mulVecLin.ker = (A ^ (1 + 1)).mulVecLin.ker := by
    refine le_antisymm (A.monotone_ker_mulVecLin_pow (by decide)) ?_
    intro v hv
    by_contra hn
    apply h v
    apply (isVectorOfGrade_zero_iff A v 2).mpr
    exact ⟨by decide, hv, hn⟩
  exact le_antisymm ((A.rank_pow_eq_succ_iff Nat.one_pos).mp
    ((A.rank_pow_eq_iff_ker_eq (Nat.le_succ 1)).mpr hk)) A.rankStabilizationIndex_spec.1

/-- An S-inverse that satisfies either Penrose inverse equation has index
one, and so does the original matrix. -/
theorem IsSInverse.matrixIndex_eq_one {A X : Matrix n n ℂ} (h : IsSInverse A X)
    (hi : A.IsInnerInverse X ∨ A.IsOuterInverse X) :
    matrixIndex A = 1 ∧ matrixIndex X = 1 := by
  have innerCase {B Y : Matrix n n ℂ} (hS : IsSInverse B Y) (hI : B.IsInnerInverse Y) :
      matrixIndex B = 1 ∧ matrixIndex Y = 1 := by
    have hn (v : n → ℂ) (hv : IsVectorOfGrade B 0 v 2) : False := by
      obtain ⟨_, h0, h1⟩ := (isVectorOfGrade_zero_iff B v 2).mp hv
      have h0' : B *ᵥ v ∈ B.mulVecLin.ker := by
        change B *ᵥ (B *ᵥ v) = 0
        rwa [mulVec_mulVec, ← pow_two]
      rw [hS.ker_eq] at h0'
      change Y *ᵥ (B *ᵥ v) = 0 at h0'
      have he : B *ᵥ v = 0 := by
        rw [← isInnerInverse_iff.mp hI, ← mulVec_mulVec, ← mulVec_mulVec, h0', mulVec_zero]
      exact h1 (by simpa only [show 2 - 1 = 1 by decide, pow_one] using he)
    refine ⟨matrixIndex_eq_one_of_no_grade_two B hn, matrixIndex_eq_one_of_no_grade_two Y ?_⟩
    intro v hv
    exact hn v ((hS 0 v 2).mpr (by simpa only [_root_.inv_zero] using hv))
  rcases hi with hi | hi
  · exact innerCase h hi
  · exact (innerCase h.symm hi).symm

private theorem groupInverse_ker_eq {A G : Matrix n n ℂ} (h : IsGroupInverse A G) :
    A.mulVecLin.ker = G.mulVecLin.ker := by
  obtain ⟨hc, ha, hg⟩ := _root_.isGroupInverse_iff.mp h
  ext v
  simp only [LinearMap.mem_ker, mulVecLin_apply]
  constructor
  · intro hv
    calc
      G *ᵥ v = (G * G * A) *ᵥ v := by rw [mul_assoc, hc.eq.symm, ← mul_assoc, hg]
      _ = 0 := by rw [← mulVec_mulVec, hv, mulVec_zero]
  · intro hv
    calc
      A *ᵥ v = (A * A * G) *ᵥ v := by rw [mul_assoc, hc.eq, ← mul_assoc, ha]
      _ = 0 := by rw [← mulVec_mulVec, hv, mulVec_zero]

/-- Every group inverse matches the exact grades at reciprocal eigenvalues. -/
theorem isSInverse_of_isGroupInverse {A G : Matrix n n ℂ} (h : IsGroupInverse A G) :
    IsSInverse A G := by
  obtain ⟨hc, ha, hg⟩ := _root_.isGroupInverse_iff.mp h
  have h' : IsGroupInverse G A := _root_.isGroupInverse_iff.mpr ⟨hc.symm, hg, ha⟩
  have hA := (theorem_4_2 A).mp ⟨G, h, fun _ h₁ => h₁.unique h⟩
  have hG := (theorem_4_2 G).mp ⟨A, h', fun _ h₁ => h₁.unique h'⟩
  intro μ v p
  by_cases hz : μ = 0
  · subst μ
    rw [_root_.inv_zero]
    have hpow (B : Matrix n n ℂ) (hB : matrixIndex B = 1) (r : ℕ) (hr : 1 ≤ r) :
        (matrixEnd B).genEigenspace 0 r = B.mulVecLin.ker := by
      have hb : (matrixEnd B).genEigenspace 0 r = (B ^ r).mulVecLin.ker := by
        rw [End.genEigenspace_nat, zero_smul, sub_zero]
        simp only [matrixEnd, ← toLin'_apply', ← toLin'_pow]
      calc
        _ = _ := hb
        _ = End.maxGenEigenspace B.mulVecLin 0 :=
          (maxGenEigenspace_zero_eq_stableKer B (hB.symm ▸ hr)).symm
        _ = _ := by
          simpa only [pow_one] using maxGenEigenspace_zero_eq_stableKer B hB.le
    by_cases hp : 0 < p
    · have hp' : 1 ≤ p := hp
      unfold IsVectorOfGrade
      rw [hpow A hA _ hp', hpow G hG _ hp', groupInverse_ker_eq h]
      by_cases hp₁ : p = 1
      · simp only [hp₁, Nat.sub_self, Nat.cast_zero, End.genEigenspace_zero]
      · have hp₂ : 1 ≤ p - 1 := by omega
        rw [hpow A hA _ hp₂, hpow G hG _ hp₂, groupInverse_ker_eq h]
    · simp [IsVectorOfGrade, hp]
  · refine ⟨lemma_4_4 A G (l := 1) h.stable_left hz, ?_⟩
    intro hv
    simpa only [inv_inv] using lemma_4_4 G A (l := 1) h'.stable_left (inv_ne_zero hz) hv

omit [DecidableEq n] in
private theorem rank_eq_of_same_ker {A X : Matrix n n ℂ} (h : A.mulVecLin.ker = X.mulVecLin.ker) :
    A.rank = X.rank := by
  have hA := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hX := LinearMap.finrank_range_add_finrank_ker X.mulVecLin
  rw [h] at hA
  exact Nat.add_right_cancel (hA.trans hX.symm)

omit [DecidableEq n] in
private theorem outerInverse_eq_of_same_range_and_ker {A X G : Matrix n n ℂ}
    (hX : A.IsOuterInverse X) (hG : A.IsOuterInverse G)
    (hR : X.mulVecLin.range = G.mulVecLin.range) (hK : X.mulVecLin.ker = G.mulVecLin.ker) :
    X = G := by
  rw [ext_iff_mulVec]
  intro v
  obtain ⟨w, hw⟩ := hR ▸ X.mulVecLin.mem_range_self v
  change G *ᵥ w = X *ᵥ v at hw
  have h₁ : G *ᵥ (A *ᵥ (X *ᵥ v)) = X *ᵥ v := by
    rw [← hw, mulVec_mulVec, mulVec_mulVec, isOuterInverse_iff.mp hG]
  have h₂ : A *ᵥ (X *ᵥ v) - v ∈ X.mulVecLin.ker := by
    change X *ᵥ (A *ᵥ (X *ᵥ v) - v) = 0
    rw [mulVec_sub, mulVec_mulVec, mulVec_mulVec, isOuterInverse_iff.mp hX, sub_self]
  rw [hK] at h₂
  change G *ᵥ (A *ᵥ (X *ᵥ v) - v) = 0 at h₂
  rw [mulVec_sub, h₁, sub_eq_zero] at h₂
  exact h₂

/-- **Theorem 6** of [benIsrael2003generalized], Chapter 4.
For an index-one matrix the group inverse is an S-inverse and is unique
among S-inverses satisfying either Penrose inverse equation. -/
theorem theorem_4_6 (A : Matrix n n ℂ) (hA : matrixIndex A = 1) :
    ∃ G, IsGroupInverse A G ∧ IsSInverse A G ∧
      ∀ X, IsSInverse A X → (A.IsInnerInverse X ∨ A.IsOuterInverse X) → X = G := by
  obtain ⟨G, hG, _⟩ := (theorem_4_2 A).mpr hA
  have hSG := isSInverse_of_isGroupInverse hG
  refine ⟨G, hG, hSG, ?_⟩
  intro X hS hi
  have hX := (hS.matrixIndex_eq_one hi).2
  have hGidx := (hSG.matrixIndex_eq_one (Or.inr hG.outer)).2
  have hmax (μ : ℂ) :
      End.maxGenEigenspace X.mulVecLin μ = End.maxGenEigenspace G.mulVecLin μ :=
    maxGenEigenspace_eq_of_grade_iff fun v p => by
      simpa only [inv_inv] using (hS μ⁻¹ v p).symm.trans (hSG μ⁻¹ v p)
  have hR : X.mulVecLin.range = G.mulVecLin.range := by
    have hXr := stableRange_eq_nonzeroSpectralSubspace X hX.le
    have hGr := stableRange_eq_nonzeroSpectralSubspace G hGidx.le
    rw [pow_one] at hXr hGr
    rw [hXr, hGr, End.spectralSubspace, End.spectralSubspace]
    simp only [hmax]
  have hK := hS.ker_eq.symm.trans hSG.ker_eq
  have hRank := (rank_eq_of_same_ker hS.ker_eq).symm
  have hXo : A.IsOuterInverse X := hi.elim
    (fun h => h.isOuterInverse_iff_rank_eq.mpr hRank) id
  exact outerInverse_eq_of_same_range_and_ker hXo hG.outer hR hK

/-- **Theorem 6**, diagonalizable case. If the eigenspaces of a square
matrix span the whole space, its group inverse is its only S-inverse. -/
theorem theorem_4_6_diagonalizable {A G X : Matrix n n ℂ}
    (hA : (⨆ μ : ℂ, End.eigenspace A.mulVecLin μ) = ⊤)
    (hG : IsGroupInverse A G) (hX : IsSInverse A X) : X = G := by
  let f := matrixEnd A
  let g := matrixEnd G
  let x := matrixEnd X
  have hSG := isSInverse_of_isGroupInverse hG
  have hle : (⨆ μ : ℂ, f.eigenspace μ) ≤ (x - g).ker := by
    apply iSup_le
    intro μ v hv
    by_cases hn : v = 0
    · simpa only [hn] using Submodule.zero_mem (x - g).ker
    have hg : IsVectorOfGrade A μ v 1 := by
      refine ⟨Nat.one_pos, hv, ?_⟩
      simpa only [Nat.sub_self, Nat.cast_zero, End.genEigenspace_zero, Submodule.mem_bot] using hn
    have hx := End.mem_eigenspace_iff.mp ((hX μ v 1).mp hg).2.1
    have hg' := End.mem_eigenspace_iff.mp ((hSG μ v 1).mp hg).2.1
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact hx.trans hg'.symm
  change ⨆ μ : ℂ, f.eigenspace μ = ⊤ at hA
  rw [hA] at hle
  rw [ext_iff_mulVec]
  intro v
  have hv : v ∈ (x - g).ker := hle (Submodule.mem_top)
  exact sub_eq_zero.mp hv

end BenIsraelGreville.Chapter04
