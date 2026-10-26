import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Numlib.Analysis.Calculus.TaylorModel.Linearity
import Numlib.Analysis.Calculus.IteratedDeriv.SquaredNorm
import Numlib.Optimization.Constrained.TargetPerturbation
import Numlib.Optimization.Constrained.TargetCriticality

/-!
# TargetTransfer

Corrected target-merit to Lagrangian certificates retain the actual squared residual-increment
term. Its first derivative vanishes, and its directional jets through order three vanish when
both actual first objective and constraint derivatives vanish.
-/

namespace Constrained
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- At a base point x, the actual function R_x(z)=norm(c(z)-c(x))^2/2+(f(z)-f(x))^2/2. -/
noncomputable def residualIncrementMerit (f : E → ℝ) (c : E → F) (x : E) (z : E) : ℝ :=
  ‖c z - c x‖ ^ 2 / 2 + (f z - f x) ^ 2 / 2

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- For nonzero target gap a=f(x)-t and actual multiplier -c(x)/a, the true merit equals a times
the actual Lagrangian plus R_x plus a constant. Derive by the actual inner-product squared-
norm identity. -/
theorem targetMerit_decomposition (f : E → ℝ) (c : E → F) {x : E} {t : ℝ}
    (ht : f x - t ≠ 0) :
    targetMerit f c t =
      (f x - t) • vectorLagrangian f c (targetMultiplier f c t x) +
        residualIncrementMerit f c x +
          fun _ => targetMerit f c t x - (f x - t) *
            vectorLagrangian f c (targetMultiplier f c t x) x := by
  funext z
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, targetMerit,
    vectorLagrangian, targetMultiplier, residualIncrementMerit, inner_smul_left,
    RCLike.conj_to_real, norm_sub_sq_real]
  field_simp
  rw [real_inner_comm (c z) (c x), real_inner_self_eq_norm_sq]
  ring
end Constrained

namespace Constrained
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Actual finite smoothness of f and c gives actual finite smoothness of R_x. -/
theorem contDiffAt_residualIncrementMerit {f : E → ℝ} {c : E → F} {x : E} {p : ℕ}
    (hf : ContDiffAt ℝ p f x) (hc : ContDiffAt ℝ p c x) :
    ContDiffAt ℝ p (residualIncrementMerit f c x) x := by
  have hfs : ContDiffAt ℝ p (fun z => f z - f x) x := hf.sub contDiffAt_const
  have hcs : ContDiffAt ℝ p (fun z => c z - c x) x := hc.sub contDiffAt_const
  unfold residualIncrementMerit
  exact ((hcs.norm_sq (𝕜 := ℝ)).div_const 2).add ((hfs.pow 2).div_const 2)

/-- Every actual finite Taylor decrement of the merit is a times the Lagrangian decrement plus
the actual decrement of R_x, with the constant canceled. -/
theorem decrement_targetMerit_decomposition {f : E → ℝ} {c : E → F} {x : E}
    {p : ℕ} (hf : ContDiffAt ℝ p f x) (hc : ContDiffAt ℝ p c x)
    {t : ℝ} (ht : f x - t ≠ 0) (d : E) :
    TaylorModel.decrement (targetMerit f c t) p x d = (f x - t) *
      TaylorModel.decrement (vectorLagrangian f c (targetMultiplier f c t x)) p x d +
        TaylorModel.decrement (residualIncrementMerit f c x) p x d := by
  have hL : ContDiffAt ℝ p (vectorLagrangian f c (targetMultiplier f c t x)) x :=
    hf.sub ((innerSL ℝ _).contDiff.contDiffAt.comp x hc)
  have hR := contDiffAt_residualIncrementMerit hf hc
  have ha : ContDiffAt ℝ p ((f x - t) •
      vectorLagrangian f c (targetMultiplier f c t x)) x := hL.const_smul (f x - t)
  have hK : ContDiffAt ℝ p (fun _ : E => targetMerit f c t x - (f x - t) *
      vectorLagrangian f c (targetMultiplier f c t x) x) x := contDiffAt_const
  have hab : ContDiffAt ℝ p ((f x - t) •
      vectorLagrangian f c (targetMultiplier f c t x) + residualIncrementMerit f c x) x :=
    ha.add hR
  rw [targetMerit_decomposition f c ht,
    TaylorModel.decrement_add_of_contDiffAt hab hK,
    TaylorModel.decrement_add_of_contDiffAt ha hR,
    TaylorModel.decrement_smul_of_contDiffAt hL,
    TaylorModel.decrement_const, add_zero]

variable [ProperSpace E]

/-- For positive a, bound the actual constrained Lagrangian criticality by (merit
criticality+sum of actual R_x tensor norm terms)/a. Preserve all finite orders, feasible set
and radius. -/
theorem constrainedCriticality_lagrangian_le_with_increment {f : E → ℝ} {c : E → F}
    {p : ℕ} {x : E} (hf : ContDiffAt ℝ p f x) (hc : ContDiffAt ℝ p c x)
    {t δ : ℝ} (ht : 0 < f x - t) {X : Set E} (hX : IsClosed X)
    (hx : x ∈ X) (hδ : 0 ≤ δ) :
    TaylorModel.constrainedCriticality
      (vectorLagrangian f c (targetMultiplier f c t x)) p X x δ ≤
        (TaylorModel.constrainedCriticality (targetMerit f c t) p X x δ +
          targetTaylorBound (residualIncrementMerit f c x) p x δ) / (f x - t) := by
  obtain ⟨d, hfeas, hd, he⟩ := TaylorModel.exists_decrement_eq_constrainedCriticality
    (vectorLagrangian f c (targetMultiplier f c t x)) p hX hx hδ
  have hmerit := TaylorModel.decrement_le_constrainedCriticality
    (targetMerit f c t) p hX hfeas hd
  have herror := abs_decrement_le_targetTaylorBound (residualIncrementMerit f c x) p x hd
  have hid := decrement_targetMerit_decomposition hf hc ht.ne' d
  rw [←he]
  apply (le_div_iff₀ ht).mpr
  nlinarith [(abs_le.mp herror).1]

end Constrained

namespace Constrained
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [ProperSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A normalized true merit certificate transfers to the source scaled multiplier bound with the
explicit residual-increment Taylor error divided by the positive target gap. The error is
not silently omitted. -/
theorem lagrangian_bound_of_merit_certificate_with_increment
    {f : E → ℝ} {c : E → F} {p : ℕ} {x : E}
    (hf : ContDiffAt ℝ p f x) (hc : ContDiffAt ℝ p c x)
    {t δ ε : ℝ} (ht : 0 < f x - t) {X : Set E} (hX : IsClosed X)
    (hx : x ∈ X) (hδ : 0 ≤ δ)
    (hcrit : TaylorModel.constrainedCriticality (targetMerit f c t) p X x δ ≤
      ε * Real.sqrt (‖c x‖ ^ 2 + (f x - t) ^ 2) * δ ^ p / p.factorial) :
    TaylorModel.constrainedCriticality
      (vectorLagrangian f c (targetMultiplier f c t x)) p X x δ ≤
        ε * multiplierNorm (targetMultiplier f c t x) * δ ^ p / p.factorial +
          targetTaylorBound (residualIncrementMerit f c x) p x δ / (f x - t) := by
  have hbound := constrainedCriticality_lagrangian_le_with_increment hf hc ht hX hx hδ
  have hid := targetMultiplier_norm_identity f c ht
  rw [←hid] at hcrit
  apply hbound.trans
  apply (div_le_iff₀ ht).mpr
  have hfac : (0 : ℝ) < p.factorial := by positivity
  field_simp
  have hscale := mul_le_mul_of_nonneg_right hcrit hfac.le
  field_simp at hscale
  nlinarith

omit [ProperSpace E] in
/-- The actual derivative of R_x at x is zero, so the first-order source certificate needs no
correction term. -/
theorem hasFDerivAt_residualIncrementMerit {f : E → ℝ} {c : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x) :
    HasFDerivAt (residualIncrementMerit f c x) (0 : E →L[ℝ] ℝ) x := by
  have hfs : DifferentiableAt ℝ (fun z => f z - f x) x := hf.sub_const _
  have hcs : DifferentiableAt ℝ (fun z => c z - c x) x := hc.sub_const _
  have hd := hasFDerivAt_targetMerit hfs hcs 0
  have he : targetMerit (fun z => f z - f x) (fun z => c z - c x) 0 =
      residualIncrementMerit f c x := by
    funext z
    simp only [targetMerit, residualIncrementMerit, sub_zero]
  rw [he] at hd
  simpa using hd

end Constrained

namespace Constrained
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- For 1<=j<=3, the actual diagonal derivative of R_x vanishes on directions annihilated by the
actual first derivatives of both f and c. Use finite scalar chain rules and actual affine
restrictions. -/
theorem residualIncrementMerit_diagonal_zero {f : E → ℝ} {c : E → F} {x d : E}
    {j : ℕ} (hj : j ≤ 3) (hj0 : 0 < j)
    (hf : ContDiffAt ℝ j f x) (hc : ContDiffAt ℝ j c x)
    (hdf : fderiv ℝ f x d = 0) (hdc : fderiv ℝ c x d = 0) :
    iteratedFDeriv ℝ j (residualIncrementMerit f c x) x (fun _ => d) = 0 := by
  let rf : ℝ → ℝ := fun t => f (x + t • d) - f x
  let rc : ℝ → F := fun t => c (x + t • d) - c x
  have hline : ContDiffAt ℝ j (fun t : ℝ => x + t • d) 0 := by fun_prop
  have hfs : ContDiffAt ℝ j rf 0 := by
    apply (show ContDiffAt ℝ j f (x + (0 : ℝ) • d) by simpa using hf).comp 0 hline |>.sub
      contDiffAt_const
  have hcs : ContDiffAt ℝ j rc 0 := by
    apply (show ContDiffAt ℝ j c (x + (0 : ℝ) • d) by simpa using hc).comp 0 hline |>.sub
      contDiffAt_const
  have hdfline : deriv rf 0 = 0 := by
    have hd : HasDerivAt (fun t : ℝ => f (x + t • d)) (fderiv ℝ f x d) 0 :=
      (hf.differentiableAt (by exact_mod_cast hj0.ne')).hasFDerivAt.hasLineDerivAt d
    have hh := (hd.sub_const (f x)).deriv
    simpa only [rf, hdf] using hh
  have hdcline : deriv rc 0 = 0 := by
    have hd : HasDerivAt (fun t : ℝ => c (x + t • d)) (fderiv ℝ c x d) 0 :=
      (hc.differentiableAt (by exact_mod_cast hj0.ne')).hasFDerivAt.hasLineDerivAt d
    have hh := (hd.sub_const (c x)).deriv
    simpa only [rc, hdc] using hh
  have hfn := iteratedDeriv_norm_sq_eq_zero_of_value_deriv_zero hj hfs (by simp [rf]) hdfline
  have hcn := iteratedDeriv_norm_sq_eq_zero_of_value_deriv_zero hj hcs (by simp [rc]) hdcline
  have he : (fun t : ℝ => residualIncrementMerit f c x (x + t • d)) =
      fun t => (1 / 2 : ℝ) • ‖rc t‖ ^ 2 + (1 / 2 : ℝ) • ‖rf t‖ ^ 2 := by
    funext t
    simp only [residualIncrementMerit, rf, rc, smul_eq_mul, Real.norm_eq_abs, sq_abs]
    ring
  rw [←TaylorModel.iteratedDeriv_affineLine_at (contDiffAt_residualIncrementMerit hf hc)
    le_rfl d, he, iteratedDeriv_fun_add ((hcs.norm_sq (𝕜 := ℝ)).const_smul (1 / 2 : ℝ))
      ((hfs.norm_sq (𝕜 := ℝ)).const_smul (1 / 2 : ℝ)),
    iteratedDeriv_fun_const_smul (hcs.norm_sq (𝕜 := ℝ)),
    iteratedDeriv_fun_const_smul (hfs.norm_sq (𝕜 := ℝ)), hcn, hfn]
  simp
end Constrained

namespace Constrained
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Through order three, all actual finite R_x decrements vanish on the source common critical
directions, restoring the unchanged M-direction certificates. -/
theorem residualIncrementMerit_decrement_zero {f : E → ℝ} {c : E → F} {x d : E}
    {j : ℕ} (hj : j ≤ 3) (hf : ContDiffAt ℝ j f x) (hc : ContDiffAt ℝ j c x)
    (hdf : fderiv ℝ f x d = 0) (hdc : fderiv ℝ c x d = 0) :
    TaylorModel.decrement (residualIncrementMerit f c x) j x d = 0 := by
  change TaylorModel.jetDecrement (ftaylorSeries ℝ (residualIncrementMerit f c x) x) j d = 0
  rw [TaylorModel.jetDecrement_eq_sum]
  apply neg_eq_zero.mpr
  apply Finset.sum_eq_zero
  intro i hi
  have hin : i + 1 ≤ j := by simpa using hi
  change (((i + 1).factorial : ℝ)⁻¹) •
    iteratedFDeriv ℝ (i + 1) (residualIncrementMerit f c x) x (fun _ => d) = 0
  rw [residualIncrementMerit_diagonal_zero (hin.trans hj) (by omega)
    (hf.of_le (by exact_mod_cast hin)) (hc.of_le (by exact_mod_cast hin)) hdf hdc]
  simp

variable [ProperSpace E]

/-- On common first-order kernels and actual feasible displacements, normalized merit
certificates imply the exact unchanged source higher Lagrangian bounds through order three.
No Hessian or higher identity is assumed. -/
theorem lagrangian_restricted_bound_of_merit_certificate
    {f : E → ℝ} {c : E → F} {j : ℕ} {x : E} (hj : j ≤ 3)
    (hf : ContDiffAt ℝ j f x) (hc : ContDiffAt ℝ j c x)
    {t δ ε : ℝ} (ht : 0 < f x - t) {X V : Set E} (hX : IsClosed X)
    (h0 : (0 : E) ∈ V) (hδ : 0 ≤ δ)
    (hV : ∀ d ∈ V, x + d ∈ X ∧ fderiv ℝ f x d = 0 ∧ fderiv ℝ c x d = 0)
    (hcrit : TaylorModel.constrainedCriticality (targetMerit f c t) j X x δ ≤
      ε * Real.sqrt (‖c x‖ ^ 2 + (f x - t) ^ 2) * δ ^ j / j.factorial) :
    TaylorModel.restrictedCriticality
      (vectorLagrangian f c (targetMultiplier f c t x)) j V x δ ≤
        ε * multiplierNorm (targetMultiplier f c t x) * δ ^ j / j.factorial := by
  unfold TaylorModel.restrictedCriticality
  apply csSup_le
  · exact ⟨_, ⟨0, ⟨h0, by simp [hδ]⟩, rfl⟩⟩
  · rintro b ⟨d, ⟨hdV, hdδ⟩, rfl⟩
    have hd : ‖d‖ ≤ δ := by simpa using hdδ
    obtain ⟨hfeas, hdf, hdc⟩ := hV d hdV
    have hR := residualIncrementMerit_decrement_zero hj hf hc hdf hdc
    have hb := (TaylorModel.decrement_le_constrainedCriticality
      (targetMerit f c t) j hX hfeas hd).trans hcrit
    rw [decrement_targetMerit_decomposition hf hc ht.ne' d, hR, add_zero,
      ←targetMultiplier_norm_identity f c ht] at hb
    apply le_of_mul_le_mul_left (a := f x - t) _ ht
    convert hb using 1
    ring
end Constrained
