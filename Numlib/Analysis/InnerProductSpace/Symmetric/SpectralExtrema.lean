import Numlib.Analysis.InnerProductSpace.Coercive

/-!
# The genuine largest eigenvalue of a finite-dimensional symmetric operator

The leading sorted spectral value is an actual eigenvalue and bounds the
Rayleigh quadratic form, including negative definite operators.
-/

namespace LinearMap.IsSymmetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {A : E →ₗ[ℝ] E}
/-- The first actual sorted eigenvalue of a symmetric operator on a nonempty space. -/
noncomputable def greatestEigenvalue (hA : A.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (hpos : 0 < n) : ℝ :=
  hA.eigenvalues hn ⟨0, hpos⟩
/-- The greatest actual eigenvalue bounds the entire Rayleigh quadratic form. -/
theorem inner_apply_le_greatestEigenvalue (hA : A.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (hpos : 0 < n) (v : E) :
    inner ℝ (A v) v ≤ hA.greatestEigenvalue hn hpos * ‖v‖ ^ 2 := by
  let last : Fin n := ⟨n - 1, by omega⟩
  have hb : A.IsSymmetricBoundedBy (hA.eigenvalues hn last)
      (hA.greatestEigenvalue hn hpos) := by
    apply (hA.isSymmetricBoundedBy_iff_forall_hasEigenvalue _ _).mpr
    intro μ hμ
    obtain ⟨i, hi⟩ := hA.exists_eigenvalues_eq hn hμ
    rw [←hi]
    constructor
    · exact hA.eigenvalues_antitone hn (show i ≤ last from by
        apply Fin.le_iff_val_le_val.mpr
        dsimp [last]
        omega)
    · exact hA.eigenvalues_antitone hn (show (⟨0, hpos⟩ : Fin n) ≤ i from
        Fin.le_iff_val_le_val.mpr (Nat.zero_le _))
  exact hb.re_inner_le v
end LinearMap.IsSymmetric
