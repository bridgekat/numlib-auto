import Numlib.Krylov.PreconditionedLanczos

/-!
# Correctness of the raw preconditioned Lanczos recurrence

A legal raw recurrence is the existing Lanczos process in the preconditioner's energy space.
The proof follows the actual cached residual and previous dual vector, including breakdown.
-/

noncomputable section
open scoped InnerProductSpace
namespace Krylov.PreconditionedLanczos
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {M Minv H : E →ₗ[ℝ] E} (hM : Krylov.IsPreconditioner M Minv)
variable {g : E} {states : ℕ → State E} {trials : ℕ → Trial E} {N : ℕ}

/-- A symmetric Hessian becomes a symmetric operator in the metric geometry. -/
theorem isSymmetric_energyEnd (hH : H.IsSymmetric) :
    (hM.energyEnd (Minv ∘ₗ H)).IsSymmetric := by
  intro x y
  obtain ⟨x, rfl⟩ := hM.toEnergy.surjective x
  obtain ⟨y, rfl⟩ := hM.toEnergy.surjective y
  rw [hM.inner_energyEnd_left, hM.inner_energyEnd_right]
  exact hH x y

private theorem primal_eq_of_residual (h : Prefix H Minv g states trials N) {k : ℕ}
    (hk : k < N)
    (hr : hM.toEnergy (Minv (states k).residual) =
      if k = 0 then hM.toEnergy (Minv g) else
        Arnoldi.w (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g)) (k - 1)) :
    hM.toEnergy (trials k).primal =
      Arnoldi.vec (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g)) k := by
  have hgamma : (trials k).gamma = ‖hM.toEnergy (Minv (states k).residual)‖ := by
    rw [h.oracle k hk, gamma_eq_norm hM]
  have hq : hM.toEnergy (trials k).primal =
      (trials k).gamma⁻¹ • hM.toEnergy (Minv (states k).residual) := by
    rw [h.oracle k hk]
    exact map_smul hM.toEnergy _ _
  rw [hq, hgamma, hr]
  cases k with
  | zero =>
    simp only [ite_true] at *
    have hb : hM.toEnergy (Minv g) ≠ 0 := by
      intro hz
      exact h.active 0 hk (by rw [hgamma, hr, hz, norm_zero])
    exact (Arnoldi.vec_zero _ _ hb).symm
  | succ k =>
    simpa using (Arnoldi.vec_succ_eq
        (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g)) k).symm

/-- The transformed raw residual and previous dual vector are exactly the canonical
unnormalized Arnoldi residual and preceding Arnoldi vector, throughout a legal prefix. -/
theorem Prefix.energy_state (h : Prefix H Minv g states trials N) (hH : H.IsSymmetric)
    {k : ℕ} (hk : k ≤ N) :
    (hM.toEnergy (Minv (states k).residual) =
      if k = 0 then hM.toEnergy (Minv g) else
        Arnoldi.w (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g)) (k - 1)) ∧
    (hM.toEnergy (Minv (states k).previous) =
      if k = 0 then 0 else
        Arnoldi.vec (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g)) (k - 1)) := by
  induction k with
  | zero => simp [h.initial]
  | succ k ih =>
    have hk' : k < N := by omega
    obtain ⟨hr, hp⟩ := ih (by omega)
    have hq := primal_eq_of_residual hM h hk' hr
    have hd : Minv (trials k).dual = (trials k).primal := by
      rw [h.oracle k hk', inverse_dual]
    have hgamma : (trials k).gamma =
        ‖if k = 0 then hM.toEnergy (Minv g) else
          Arnoldi.w (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g)) (k - 1)‖ := by
      rw [h.oracle k hk', gamma_eq_norm hM, hr]
    have hrho : (trials k).rho =
        Lanczos.alpha (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g)) k := by
      rw [h.oracle k hk', rho_eq_energy_inner hM, ← h.oracle k hk', hq]
      rfl
    constructor
    · rw [h.update k hk']
      change hM.toEnergy (Minv ((trials k).hessian -
        (trials k).rho • (trials k).dual - (trials k).gamma • (states k).previous)) = _
      simp only [map_sub, map_smul, h.hessian_oracle hk', hd, hp, hrho]
      have hAp : hM.toEnergy (Minv (H (trials k).primal)) =
          hM.energyEnd (Minv ∘ₗ H)
            (Arnoldi.vec (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g)) k) := by
        rw [← hq]
        rfl
      rw [hAp, hq, hgamma]
      cases k with
      | zero => simp [Arnoldi.w, Arnoldi.coeff, Lanczos.alpha]
      | succ k =>
        simpa [Lanczos.beta] using
          (Lanczos.w_succ_eq (hM.toEnergy (Minv g))
            (isSymmetric_energyEnd hM hH) k).symm
    · rw [h.update k hk']
      change hM.toEnergy (Minv (trials k).dual) = _
      simpa using hd ▸ hq

/-- Every actual primal query equals the existing energy-space Arnoldi vector. -/
theorem Prefix.primal_eq_vec (h : Prefix H Minv g states trials N) (hH : H.IsSymmetric)
    {k : ℕ} (hk : k < N) :
    hM.toEnergy (trials k).primal =
      Arnoldi.vec (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g)) k :=
  primal_eq_of_residual hM h hk (h.energy_state hM hH (Nat.le_of_lt hk)).1

/-- The actual cached diagonal coefficient is the canonical Lanczos coefficient. -/
theorem Prefix.rho_eq_alpha (h : Prefix H Minv g states trials N) (hH : H.IsSymmetric)
    {k : ℕ} (hk : k < N) :
    (trials k).rho =
      Lanczos.alpha (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g)) k := by
  rw [h.oracle k hk, rho_eq_energy_inner hM, ← h.oracle k hk, h.primal_eq_vec hM hH hk]
  rfl

/-- Initial normalization is the norm of the preconditioned initial residual. -/
theorem Prefix.gamma_zero (h : Prefix H Minv g states trials N) (hN : 0 < N) :
    (trials 0).gamma = ‖hM.toEnergy (Minv g)‖ := by
  rw [h.oracle 0 hN, gamma_eq_norm hM, h.initial]

/-- Successive raw normalization coefficients are precisely the Lanczos off-diagonals. -/
theorem Prefix.gamma_succ (h : Prefix H Minv g states trials N) (hH : H.IsSymmetric)
    {k : ℕ} (hk : k + 1 < N) :
    (trials (k + 1)).gamma =
      Lanczos.beta (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g)) k := by
  rw [h.oracle (k + 1) hk, gamma_eq_norm hM,
    (h.energy_state hM hH (Nat.le_of_lt hk)).1]
  simp [Lanczos.beta]

/-- The final transformed residual is the canonical unnormalized Lanczos residual. -/
theorem Prefix.residual_eq_w (h : Prefix H Minv g states trials N) (hH : H.IsSymmetric)
    (hN : 0 < N) :
    hM.toEnergy (Minv (states N).residual) =
      Arnoldi.w (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g)) (N - 1) := by
  simpa only [ite_eq_right (Nat.ne_of_gt hN)] using (h.energy_state hM hH (le_refl N)).1

/-- A legal prefix cannot normalize the zero vector at or beyond the Krylov grade. -/
theorem Prefix.length_le_grade [FiniteDimensional ℝ E]
    (h : Prefix H Minv g states trials N) (hH : H.IsSymmetric) :
    N ≤ Krylov.grade (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g)) := by
  by_contra hn
  have hk : Krylov.grade (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g)) < N :=
    Nat.lt_of_not_ge hn
  have hq := h.primal_eq_vec hM hH hk
  have hz := (Arnoldi.vec_eq_zero_iff (hM.energyEnd (Minv ∘ₗ H))
    (hM.toEnergy (Minv g)) _).2 (le_refl _)
  have hone := norm_primal_eq_one hM H (states _) (by
    rw [← h.oracle _ hk]
    exact h.active _ hk)
  rw [← h.oracle _ hk, hq, hz, norm_zero] at hone
  exact zero_ne_one hone

include hM in
/-- An early endpoint has zero raw residual; it is tested before attempting normalization. -/
theorem Execution.residual_eq_zero_of_lt_budget {budget : ℕ}
    (h : Execution H Minv g states trials budget N) (hN : N < budget) :
    (states N).residual = 0 := by
  rcases h.endpoint with heq | ⟨hi, hg, hz⟩
  · omega
  · apply (gamma_eq_zero_iff hM H (states N)).1
    change Real.sqrt ⟪(states N).residual, Minv (states N).residual⟫_ℝ = 0
    rw [← hi, ← hg, hz]

/-- At breakdown the canonical Lanczos coefficient vanishes, including the zero initial case. -/
theorem Prefix.grade_le_of_residual_eq_zero [FiniteDimensional ℝ E]
    (h : Prefix H Minv g states trials N) (hH : H.IsSymmetric)
    (hz : (states N).residual = 0) :
    Krylov.grade (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g)) ≤ N := by
  have hr := (h.energy_state hM hH (le_refl N)).1
  rw [hz, map_zero, map_zero] at hr
  cases N with
  | zero =>
    simp only [ite_true] at hr
    rw [← hr, Krylov.grade_zero]
  | succ k =>
    have hw : Arnoldi.w (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g)) k = 0 := by
      simpa using hr.symm
    exact (Lanczos.beta_eq_zero_iff (A := hM.energyEnd (Minv ∘ₗ H))
      (hM.toEnergy (Minv g)) k).1 (by simp [Lanczos.beta, hw])

/-- A completed execution with a budget covering the grade ends exactly at the grade. -/
theorem Execution.length_eq_grade_of_grade_le_budget [FiniteDimensional ℝ E] {budget : ℕ}
    (h : Execution H Minv g states trials budget N) (hH : H.IsSymmetric)
    (hbudget : Krylov.grade (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g)) ≤ budget) :
    N = Krylov.grade (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g)) := by
  apply le_antisymm (h.toPrefix.length_le_grade hM hH)
  by_cases hN : N < budget
  · exact h.toPrefix.grade_le_of_residual_eq_zero hM hH
      (h.residual_eq_zero_of_lt_budget hM hN)
  · have hNb : N = budget := by have := h.within_budget; omega
    simpa [hNb] using hbudget

/-- The ambient-dimension budget suffices, so a full raw execution stops at the Krylov grade. -/
theorem Execution.length_eq_grade [FiniteDimensional ℝ E]
    (h : Execution H Minv g states trials (Module.finrank ℝ E) N) (hH : H.IsSymmetric) :
    N = Krylov.grade (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g)) := by
  apply h.length_eq_grade_of_grade_le_budget hM hH
  have hdim : Module.finrank ℝ hM.EnergySpace = Module.finrank ℝ E :=
    hM.toEnergy.finrank_eq.symm
  simpa only [hdim] using Krylov.grade_le_finrank
    (hM.energyEnd (Minv ∘ₗ H)) (hM.toEnergy (Minv g))

end Krylov.PreconditionedLanczos
