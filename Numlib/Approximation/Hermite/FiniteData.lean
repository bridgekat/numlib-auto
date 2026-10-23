import Numlib.Approximation.Hermite.Global

/-!
# Arbitrary finite scalar jets have globally bounded interpolants

Finite strictly increasing interpolation sites place no compatibility
restriction on finitely many prescribed scalar jets. Bounding their finite
residual ratios reduces to the uniform Hermite theorem. The resulting global
objective and all prescribed derivative orders are bounded, and its highest
derivative is genuinely Lipschitz.
-/

namespace Hermite
open Set Polynomial

private theorem finite_nonneg_bound {ι : Type*} [Finite ι] (v : ι → ℝ) :
    ∃ K ≥ 0, ∀ i, v i ≤ K := by
  obtain ⟨K,hK⟩ := (Set.finite_range v).bddAbove
  exact ⟨max K 0,le_max_right _ _,fun i => (hK ⟨i,rfl⟩).trans (le_max_left _ _)⟩

/-- Every finite strictly increasing real grid with arbitrary scalar jets has
a globally bounded Cp interpolant, all lower derivatives globally bounded and
the highest derivative globally Lipschitz. The bounds may depend on the data. -/
theorem exists_bounded_finite_interpolant (p n : ℕ) (hn : 0 < n)
    (x : ℕ → ℝ) (a : ℕ → ℕ → ℝ)
    (hx : ∀ i j, i < j → j ≤ n → x i < x j) :
    ∃ (f : ℝ → ℝ) (L : NNReal) (B : ℝ), 0 < B ∧ ContDiff ℝ p f ∧
      LipschitzWith L (iteratedDeriv p f) ∧
      (∀ k ≤ n, ∀ j ≤ p, iteratedDeriv j f (x k) = a k j) ∧
      ∀ j ≤ p, ∀ t, |iteratedDeriv j f t| ≤ B := by
  obtain ⟨R,hR,hres⟩ := finite_nonneg_bound (fun z : Fin n × Fin (p + 1) =>
    |a (z.1.val + 1) z.2.val -
      (derivative^[z.2.val] (initialPolynomial p (a z.1.val))).eval
        (x (z.1.val + 1) - x z.1.val)| /
      (x (z.1.val + 1) - x z.1.val) ^ (p - z.2.val + 1))
  obtain ⟨J,hJ,hjets⟩ := finite_nonneg_bound
    (fun z : Fin n × Fin (p + 1) => |a z.1.val z.2.val|)
  obtain ⟨S,hS,hsteps⟩ := finite_nonneg_bound (fun k : Fin n => x (k.val + 1) - x k.val)
  let K := max R (max J S)
  have hK : 0 ≤ K := hR.trans (le_max_left _ _)
  obtain ⟨L,hL,B,hB,H⟩ := exists_uniform_interpolant p K hK
  have hres' : ∀ k < n, ∀ j ≤ p,
      |a (k + 1) j - (derivative^[j] (initialPolynomial p (a k))).eval
        (x (k + 1) - x k)| ≤ K * (x (k + 1) - x k) ^ (p - j + 1) := by
    intro k hk j hj
    have hh := hres (⟨k,hk⟩,⟨j,by omega⟩)
    have hs : 0 < x (k + 1) - x k := sub_pos.mpr (hx k (k + 1) (by omega) (by omega))
    exact (div_le_iff₀ (pow_pos hs _)).mp (hh.trans (le_max_left _ _))
  obtain ⟨f,hf,hLip,hmatch,hbound⟩ := H n hn x a hx hres'
  refine ⟨f,⟨L,hL.le⟩,B,hB,hf,hLip,hmatch,hbound ⟨?_,?_⟩⟩
  · intro k hk j hj
    exact (hjets (⟨k,hk⟩,⟨j,by omega⟩)).trans
      ((le_max_left J S).trans (le_max_right R (max J S)))
  · intro k hk
    exact (hsteps ⟨k,hk⟩).trans ((le_max_right J S).trans (le_max_right R (max J S)))

end Hermite
