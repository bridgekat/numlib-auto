import Numlib.Optimization.OracleSimulation

/-!
# Minimax comparison by uniform oracle rotations

Finite-horizon history simulation gives the minimax comparison on a class closed under
rectangular rotations. The transformed method is selected before the worst-case objective.
A separate statement transfers a singleton lower bound to all rotations in the precise
ambient dimension `n + K`. Extended-natural complexity includes nontermination.
-/

noncomputable section

namespace Optimization.DerivativeOracle
open ZeroChains

/-- A finite bound on first attainment is equivalent to a successful query by that index. -/
theorem firstStationaryTime_le_natCast_iff {n N : ℕ} (f : Space n → ℝ)
    (x : ℕ → Space n) (ε : ℝ) :
    firstStationaryTime f x ε ≤ N ↔ ∃ k ≤ N, ‖gradient f (x k)‖ ≤ ε := by
  constructor
  · intro h
    obtain ⟨k, hk, hkN⟩ := ENat.le_natCast_iff.mp h
    exact ⟨k, hkN, ((firstStationaryTime_eq_natCast_iff f x ε).mp hk).1⟩
  · rintro ⟨k, hkN, hk⟩
    exact (iInf_le_of_le ⟨k, hk⟩ le_rfl).trans (by exact_mod_cast hkN)

/-- All rectangular rotations of a fixed objective in dimension `n + K`. -/
def rotationOrbit {n : ℕ} (f : Space n → ℝ) (K : ℕ) : Set Objective :=
  {g | ∃ U : Space n →ₗᵢ[ℝ] Space (n + K), g = ⟨n + K, rotate U f⟩}

/-- A rotation belongs to its objective's prescribed ambient-dimension orbit. -/
theorem rotate_mem_rotationOrbit {n : ℕ} (f : Space n → ℝ) (K : ℕ)
    (U : Space n →ₗᵢ[ℝ] Space (n + K)) :
    (⟨n + K, rotate U f⟩ : Objective) ∈ rotationOrbit f K := ⟨U, rfl⟩

/-- A singleton zero-respecting lower bound transfers to unrestricted methods on all
rectangular rotations, with exactly `K` additional coordinates. -/
theorem le_minimax_rotationOrbit {n p K : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ (max p 1) f) (ε : ℝ)
    (hbound : (K : ℕ∞) ≤ minimax (zeroRespectingMethods p) {⟨n, f⟩} ε) :
    (K : ℕ∞) ≤ minimax (Set.univ : Set (Method p)) (rotationOrbit f K) ε := by
  have hfp : ContDiff ℝ p f := hf.of_le (le_max_left _ _)
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  apply le_iInf
  intro M
  obtain ⟨T, hT, hsim⟩ := M.val.exists_uniform_zeroRespecting_simulation K
  have hTbound : (K : ℕ∞) ≤ firstStationaryTime f (T.iterate f) ε := by
    apply hbound.trans
    apply iInf_le_of_le ⟨T, hT⟩
    apply iSup_le
    rintro ⟨g, hg⟩
    have : g = (⟨n, f⟩ : Objective) := Set.mem_singleton_iff.mp hg
    subst g
    exact le_rfl
  obtain ⟨U, hU⟩ := hsim n f hfp
  apply le_iSup_of_le ⟨⟨n + K, rotate U f⟩, rotate_mem_rotationOrbit f K U⟩
  apply (le_firstStationaryTime_iff _ _ _).mpr
  intro j hj
  rw [norm_gradient_rotate U _ hfd.differentiableAt, hU j (by omega)]
  exact (le_firstStationaryTime_iff f (T.iterate f) ε).mp hTbound j hj

/-- On a class closed under rectangular rotations, zero-respecting minimax complexity is
bounded above by unrestricted minimax complexity. The finite horizon is chosen from each
method's worst-case bound before its uniform transformed method and worst-case objective. -/
theorem minimax_zeroRespecting_le_all {p : ℕ} (functions : Set Objective)
    (hsmooth : ∀ f ∈ functions, ContDiff ℝ (max p 1) f.2)
    (hrotate : ∀ {n m : ℕ} {f : Space n → ℝ}, (⟨n, f⟩ : Objective) ∈ functions →
      ∀ U : Space n →ₗᵢ[ℝ] Space m, (⟨m, rotate U f⟩ : Objective) ∈ functions)
    (ε : ℝ) :
    minimax (zeroRespectingMethods p) functions ε ≤
      minimax (Set.univ : Set (Method p)) functions ε := by
  apply le_iInf
  intro M
  let W : ℕ∞ := ⨆ f : functions, firstStationaryTime f.val.2 (M.val.iterate f.val.2) ε
  change minimax (zeroRespectingMethods p) functions ε ≤ W
  by_cases htop : W = ⊤
  · rw [htop]
    exact le_top
  obtain ⟨K, hK⟩ := ENat.ne_top_iff_exists.mp htop
  obtain ⟨T, hT, hsim⟩ := M.val.exists_uniform_zeroRespecting_simulation K
  apply iInf_le_of_le ⟨T, hT⟩
  apply iSup_le
  intro f
  have hf := hsmooth f.val f.property
  have hfp : ContDiff ℝ p f.val.2 := hf.of_le (le_max_left _ _)
  have hfd : Differentiable ℝ f.val.2 :=
    hf.differentiable (by simp)
  obtain ⟨U, hU⟩ := hsim f.val.1 f.val.2 hfp
  have hmem := hrotate f.property U
  have hM : firstStationaryTime (rotate U f.val.2) (M.val.iterate (rotate U f.val.2)) ε ≤ K :=
    (le_iSup (fun g : functions =>
      firstStationaryTime g.val.2 (M.val.iterate g.val.2) ε)
      ⟨⟨f.val.1 + K, rotate U f.val.2⟩, hmem⟩).trans_eq hK.symm
  obtain ⟨j, hjK, hj⟩ := (firstStationaryTime_le_natCast_iff _ _ _).mp hM
  rw [norm_gradient_rotate U _ hfd.differentiableAt, hU j hjK] at hj
  apply le_trans ((firstStationaryTime_le_natCast_iff _ _ _).mpr ⟨j, hjK, hj⟩)
  exact hK.le

end Optimization.DerivativeOracle
