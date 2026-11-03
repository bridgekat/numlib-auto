import Mathlib.Analysis.Normed.Ring.Units
import Numlib.Nonlinear.Newton
import Numlib.Optimization.Subproblem.Model
import NumlibSurface.ConnGouldToint.Chapter03.Section02
import NumlibSurface.ConnGouldToint.Chapter03.Section03

/-! # Sequential quadratic programming

The equality-constrained SQP equations of [conn2000trust], Section 15.2.
The operator uses the actual multiplier increment, so the upper right block
has the opposite sign from the displayed matrix (15.2.1), which takes its negation.
In Theorem 15.2.1(i), convergence of the supplied multipliers alone leaves open
the possibility of a singular subproblem at the first iteration.
-/

open Filter Topology Metric Asymptotics
open ConnGouldToint.Chapter03

namespace ConnGouldToint.Chapter15

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- **(15.2.1)** The signed KKT operator on the primal step and the multiplier increment. -/
def sqpKKT (H : E × Y → E →L[ℝ] E) (A : E → E →L[ℝ] Y)
    (AT : E → Y →L[ℝ] E) (z : E × Y) : E × Y →L[ℝ] E × Y :=
  ((H z).comp (ContinuousLinearMap.fst ℝ E Y) -
    (AT z.1).comp (ContinuousLinearMap.snd ℝ E Y)).prod
      ((A z.1).comp (ContinuousLinearMap.fst ℝ E Y))

/-- **(15.2.2)** Stationarity and equality-constraint residuals. -/
def sqpResidual (g : E → E) (c : E → Y) (AT : E → Y →L[ℝ] E) (z : E × Y) : E × Y :=
  (g z.1 - AT z.1 z.2, c z.1)

/-- Differentiating the stationarity and feasibility residuals gives the signed
KKT operator. The derivative of the stationarity residual with the multiplier
fixed is the upper left block. -/
theorem hasFDerivAt_sqpResidual {g : E → E} {c : E → Y} {AT : E → Y →L[ℝ] E}
    {z : E × Y} (hg : DifferentiableAt ℝ g z.1) (hc : DifferentiableAt ℝ c z.1)
    (hAT : DifferentiableAt ℝ AT z.1) :
    HasFDerivAt (sqpResidual g c AT)
      (sqpKKT (fun w => fderiv ℝ (fun x => g x - AT x w.2) w.1)
        (fderiv ℝ c) AT z) z := by
  let P := ContinuousLinearMap.fst ℝ E Y
  let Q := ContinuousLinearMap.snd ℝ E Y
  have hp : HasFDerivAt (fun w : E × Y => w.1) P z := P.hasFDerivAt
  have hq : HasFDerivAt (fun w : E × Y => w.2) Q z := Q.hasFDerivAt
  have hpartial := hg.hasFDerivAt.fun_sub
    (hAT.hasFDerivAt.clm_apply (hasFDerivAt_const z.2 z.1))
  have hfull := ((hg.hasFDerivAt.comp z hp).fun_sub
    ((hAT.hasFDerivAt.comp z hp).clm_apply hq)).prodMk (hc.hasFDerivAt.comp z hp)
  convert hfull using 1
  · rfl
  · rw [sqpKKT, hpartial.fderiv]
    apply ContinuousLinearMap.ext
    intro w
    apply Prod.ext
    · simp [P, Q]
      abel
    · rfl

/-- **(15.2.5)** The stationary equations for the quadratic subproblem, using
the new multiplier rather than its increment. -/
def IsSQPCorrection (g : E → E) (c : E → Y) (H : E × Y → E →L[ℝ] E)
    (A : E → E →L[ℝ] Y) (AT : E → Y →L[ℝ] E) (z : E × Y) (s : E) (y' : Y) : Prop :=
  H z s - AT z.1 y' = -g z.1 ∧ A z.1 s = -c z.1

/-- **(15.2.3)–(15.2.5)** The Newton equation and the SQP stationary equations
are equivalent after adding the multiplier increment to the old multiplier. -/
theorem isSQPCorrection_iff_newton (g : E → E) (c : E → Y) (H : E × Y → E →L[ℝ] E)
    (A : E → E →L[ℝ] Y) (AT : E → Y →L[ℝ] E) (z : E × Y) (s : E) (dy : Y) :
    IsSQPCorrection g c H A AT z s (z.2 + dy) ↔
      sqpKKT H A AT z (s, dy) = -sqpResidual g c AT z := by
  change (H z s - AT z.1 (z.2 + dy) = -g z.1 ∧ A z.1 s = -c z.1) ↔
    (H z s - AT z.1 dy, A z.1 s) = -(g z.1 - AT z.1 z.2, c z.1)
  simp only [Prod.neg_mk, Prod.mk.injEq, map_add]
  constructor <;> rintro ⟨h, hc⟩ <;> refine ⟨?_, hc⟩
  · rw [show H z s - AT z.1 dy =
      (H z s - (AT z.1 z.2 + AT z.1 dy)) + AT z.1 z.2 by abel, h]
    abel
  · rw [show H z s - (AT z.1 z.2 + AT z.1 dy) =
      (H z s - AT z.1 dy) - AT z.1 z.2 by abel, h]
    abel

section Convergence

variable [CompleteSpace E] [CompleteSpace Y]

omit [CompleteSpace E] [CompleteSpace Y] in
private theorem sqpCorrection_of_inverse
    (g : E → E) (c : E → Y) (H : E × Y → E →L[ℝ] E)
    (A : E → E →L[ℝ] Y) (AT : E → Y →L[ℝ] E) (x : E) (y yref : Y)
    (B : (E × Y) ≃L[ℝ] (E × Y))
    (hB : (B : E × Y →L[ℝ] E × Y) = sqpKKT H A AT (x, y)) :
    let p := B.symm (sqpResidual g c AT (x, yref))
    IsSQPCorrection g c H A AT (x, y) (-p.1) (yref - p.2) := by
  let p := B.symm (sqpResidual g c AT (x, yref))
  have hstep : sqpKKT H A AT (x, y) (-p) = -sqpResidual g c AT (x, yref) := by
    rw [← hB, map_neg]
    exact congrArg Neg.neg (B.apply_symm_apply _)
  let H' : E × Y → E →L[ℝ] E := fun _ => H (x, y)
  have hN : sqpKKT H' A AT (x, yref) (-p.1, -p.2) = -sqpResidual g c AT (x, yref) := hstep
  simpa [IsSQPCorrection, H', sub_eq_add_neg] using
    (isSQPCorrection_iff_newton g c H' A AT (x, yref) (-p.1) (-p.2)).2 hN

private theorem sqp_newton_convergence_within
    (g : E → E) (c : E → Y) (H : E × Y → E →L[ℝ] E)
    (A : E → E →L[ℝ] Y) (AT : E → Y →L[ℝ] E) {zstar : E × Y}
    (hstar : sqpResidual g c AT zstar = 0)
    (e : (E × Y) ≃L[ℝ] (E × Y)) (he : (e : E × Y →L[ℝ] E × Y) = sqpKKT H A AT zstar)
    {r L ρ : ℝ} (hr : 0 < r) (hL : 0 ≤ L) (hρ : 0 < ρ)
    (hF : ∀ z ∈ ball zstar r, HasFDerivAt (sqpResidual g c AT) (sqpKKT H A AT z) z)
    (hLip : ∀ z ∈ ball zstar r, ∀ w ∈ ball zstar r,
      ‖sqpKKT H A AT z - sqpKKT H A AT w‖ ≤ L * ‖z - w‖) :
    ∃ δ > 0, ∀ z₀ ∈ ball zstar δ,
      let u := Newton.iterate (sqpResidual g c AT) (sqpKKT H A AT) z₀
      (∀ k, u k ∈ ball zstar ρ) ∧ ConvergesQQuadratically u zstar ∧
        ∀ k, IsSQPCorrection g c H A AT (u k) ((u (k + 1)).1 - (u k).1) (u (k + 1)).2 := by
  let K := ‖(e.symm : E × Y →L[ℝ] E × Y)‖ + 1
  let L' := L + 1
  let δ₀ := min r (1 / (2 * K * L'))
  let δ := min δ₀ ρ
  have hK : 0 < K := by dsimp [K]; positivity
  have hL' : 0 < L' := by dsimp [L']; linarith
  have hδ : 0 < δ := lt_min (lt_min hr (by positivity)) hρ
  have hLip' z hz w hw : ‖sqpKKT H A AT z - sqpKKT H A AT w‖ ≤ L' * ‖z - w‖ :=
    (hLip z hz w hw).trans (mul_le_mul_of_nonneg_right (by dsimp [L']; linarith) (norm_nonneg _))
  refine ⟨δ, hδ, fun z₀ hz₀ => ?_⟩
  let u := Newton.iterate (sqpResidual g c AT) (sqpKKT H A AT) z₀
  have hmain k := Newton.forall_norm_iterate_succ_sub_le_of_mem_ball hstar e he
    (show ‖(e.symm : E × Y →L[ℝ] E × Y)‖ ≤ K by dsimp [K]; linarith)
    hF hLip' (ball_subset_ball (min_le_left δ₀ ρ) hz₀) k
  have hhalf k : ‖u (k + 1) - zstar‖ ≤ ‖u k - zstar‖ / 2 := (hmain k).2.2.2
  have hgeom (k : ℕ) : ‖u k - zstar‖ ≤ (1 / 2 : ℝ) ^ k * ‖z₀ - zstar‖ := by
    induction k with
    | zero => simp [u, Newton.iterate]
    | succ k ih =>
      refine (hhalf k).trans ?_
      calc
        _ ≤ ((1 / 2 : ℝ) ^ k * ‖z₀ - zstar‖) / 2 := by gcongr
        _ = _ := by rw [pow_succ]; ring
  have hu : Tendsto u atTop (𝓝 zstar) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    refine squeeze_zero (fun _ => norm_nonneg _) hgeom ?_
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
        (by norm_num)).mul_const ‖z₀ - zstar‖
  have hstay (k : ℕ) : u k ∈ ball zstar ρ := by
    rw [mem_ball, dist_eq_norm]
    have hstart : ‖z₀ - zstar‖ < ρ := by
      have := ball_subset_ball (min_le_right δ₀ ρ) hz₀
      simpa [mem_ball, dist_eq_norm] using this
    exact ((hgeom k).trans (by
      have hp : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      simpa using mul_le_mul_of_nonneg_right hp (norm_nonneg (z₀ - zstar)))).trans_lt hstart
  refine ⟨hstay, ⟨hu, K * L', Eventually.of_forall fun k => (hmain k).2.2.1⟩, fun k => ?_⟩
  obtain ⟨B, hB, -⟩ := (hmain k).2.1
  have hu' : u (k + 1) = u k - B.symm (sqpResidual g c AT (u k)) := by
    change Newton.iterate (sqpResidual g c AT) (sqpKKT H A AT) z₀ (k + 1) = _
    rw [Newton.iterate_succ]
    change u k - (sqpKKT H A AT (u k)).inverse (sqpResidual g c AT (u k)) = _
    rw [← hB, ContinuousLinearMap.inverse_equiv]
    rfl
  change IsSQPCorrection g c H A AT (u k) ((u (k + 1)).1 - (u k).1) (u (k + 1)).2
  rw [hu']
  let p := B.symm (sqpResidual g c AT (u k))
  change IsSQPCorrection g c H A AT (u k) ((u k).1 - p.1 - (u k).1) ((u k).2 - p.2)
  rw [show (u k).1 - p.1 - (u k).1 = -p.1 by abel]
  exact sqpCorrection_of_inverse g c H A AT (u k).1 (u k).2 (u k).2 B hB

/-- **Theorem 15.2.1(ii).** When the multipliers are updated from the subproblem,
SQP is Newton's method for the KKT residual. A locally Lipschitz KKT derivative
and a nonsingular root give local quadratic convergence. -/
theorem theorem_15_2_1_ii
    (g : E → E) (c : E → Y) (H : E × Y → E →L[ℝ] E)
    (A : E → E →L[ℝ] Y) (AT : E → Y →L[ℝ] E) {zstar : E × Y}
    (hstar : sqpResidual g c AT zstar = 0)
    (e : (E × Y) ≃L[ℝ] (E × Y)) (he : (e : E × Y →L[ℝ] E × Y) = sqpKKT H A AT zstar)
    {r L : ℝ} (hr : 0 < r) (hL : 0 ≤ L)
    (hF : ∀ z ∈ ball zstar r, HasFDerivAt (sqpResidual g c AT) (sqpKKT H A AT z) z)
    (hLip : ∀ z ∈ ball zstar r, ∀ w ∈ ball zstar r,
      ‖sqpKKT H A AT z - sqpKKT H A AT w‖ ≤ L * ‖z - w‖) :
    ∃ δ > 0, ∀ z₀ ∈ ball zstar δ,
      let u := Newton.iterate (sqpResidual g c AT) (sqpKKT H A AT) z₀
      ConvergesQQuadratically u zstar ∧
        ∀ k, IsSQPCorrection g c H A AT (u k) ((u (k + 1)).1 - (u k).1) (u (k + 1)).2 := by
  obtain ⟨δ, hδ, h⟩ := sqp_newton_convergence_within g c H A AT hstar e he hr hL
    (zero_lt_one : (0 : ℝ) < 1) hF hLip
  exact ⟨δ, hδ, fun z₀ hz₀ ↦ (h z₀ hz₀).2⟩

/-- With an external multiplier, compute the primal step by freezing the
residual at the reference multiplier. The reference multiplier cancels from
the stationary subproblem equations, as in `sqpCorrection_of_inverse`. -/
noncomputable def sqpExternalStep (g : E → E) (c : E → Y) (H : E × Y → E →L[ℝ] E)
    (A : E → E →L[ℝ] Y) (AT : E → Y →L[ℝ] E) (yref : Y) (x : E) (y : Y) : E :=
  x - ((sqpKKT H A AT (x, y)).inverse (sqpResidual g c AT (x, yref))).1

omit [CompleteSpace E] [CompleteSpace Y] in
/-- At an invertible KKT operator, the arbitrary frozen reference multiplier
changes only the auxiliary multiplier increment. The primal step can therefore
be computed with reference zero, without knowing the root multiplier. -/
theorem sqpExternalStep_reference_independent
    (g : E → E) (c : E → Y) (H : E × Y → E →L[ℝ] E)
    (A : E → E →L[ℝ] Y) (AT : E → Y →L[ℝ] E) (x : E) (y v w : Y)
    (B : (E × Y) ≃L[ℝ] (E × Y))
    (hB : (B : E × Y →L[ℝ] E × Y) = sqpKKT H A AT (x, y)) :
    sqpExternalStep g c H A AT v x y = sqpExternalStep g c H A AT w x y := by
  let p := B.symm (sqpResidual g c AT (x, v))
  let q := B.symm (sqpResidual g c AT (x, w))
  have hpq : p - q = (0, v - w) := by
    apply B.injective
    calc
      B (p - q) = sqpResidual g c AT (x, v) - sqpResidual g c AT (x, w) := by
        rw [map_sub, B.apply_symm_apply, B.apply_symm_apply]
      _ = sqpKKT H A AT (x, y) (0, v - w) := by
        change (g x - AT x v - (g x - AT x w), c x - c x) =
          (H (x, y) 0 - AT x (v - w), A x 0)
        simp only [map_zero, map_sub, zero_sub, sub_self, Prod.mk.injEq, and_true]
        abel
      _ = B (0, v - w) := by rw [← hB]; rfl
  have hfst : p.1 - q.1 = 0 := congrArg Prod.fst hpq
  unfold sqpExternalStep
  rw [← hB, ContinuousLinearMap.inverse_equiv]
  change x - p.1 = x - q.1
  rw [sub_eq_zero.1 hfst]

private theorem sqp_external_estimate
    (g : E → E) (c : E → Y) (H : E × Y → E →L[ℝ] E)
    (A : E → E →L[ℝ] Y) (AT : E → Y →L[ℝ] E) {xstar : E} {ystar : Y}
    (hstar : sqpResidual g c AT (xstar, ystar) = 0)
    (e : (E × Y) ≃L[ℝ] (E × Y))
    (he : (e : E × Y →L[ℝ] E × Y) = sqpKKT H A AT (xstar, ystar))
    {r L : ℝ} (hr : 0 < r) (hL : 0 ≤ L)
    (hF : ∀ z ∈ ball (xstar, ystar) r, HasFDerivAt (sqpResidual g c AT) (sqpKKT H A AT z) z)
    (hLip : ∀ z ∈ ball (xstar, ystar) r, ∀ w ∈ ball (xstar, ystar) r,
      ‖sqpKKT H A AT z - sqpKKT H A AT w‖ ≤ L * ‖z - w‖) :
    ∃ δ > 0, ∃ M > 0, ∀ x ∈ ball xstar δ, ∀ y ∈ ball ystar δ,
      (∃ y', IsSQPCorrection g c H A AT (x, y)
        (sqpExternalStep g c H A AT ystar x y - x) y') ∧
      ‖sqpExternalStep g c H A AT ystar x y - xstar‖ ≤
        M * (L * ‖y - ystar‖ + L / 2 * ‖x - xstar‖) * ‖x - xstar‖ := by
  let K := ‖(e.symm : E × Y →L[ℝ] E × Y)‖ + 1
  let δ := min r (1 / (2 * (K * L + 1)))
  have hK : 0 < K := by dsimp [K]; positivity
  have hδ : 0 < δ := lt_min hr (by positivity)
  have hscale : K * L * δ ≤ 1 / 2 := by
    have hd := (le_div_iff₀ (by positivity : 0 < 2 * (K * L + 1))).1
      (min_le_right r (1 / (2 * (K * L + 1))))
    nlinarith
  refine ⟨δ, hδ, 2 * K, by positivity, fun x hx y hy => ?_⟩
  let z : E × Y := (x, y)
  let w : E × Y := (x, ystar)
  have hdist : ‖z - (xstar, ystar)‖ < δ := by
    rw [mem_ball, dist_eq_norm] at hx hy
    simpa [z, Prod.norm_def] using max_lt hx hy
  have hwDist : ‖w - (xstar, ystar)‖ = ‖x - xstar‖ := by simp [w, Prod.norm_def]
  have hz : z ∈ ball (xstar, ystar) r := by
    rw [mem_ball, dist_eq_norm]
    exact hdist.trans_le (min_le_left _ _)
  have hw : w ∈ ball (xstar, ystar) r := by
    rw [mem_ball, dist_eq_norm, hwDist]
    simpa only [dist_eq_norm] using (mem_ball.1 hx |>.trans_le (min_le_left _ _))
  let T := sqpKKT H A AT z - (e : E × Y →L[ℝ] E × Y)
  have hT : ‖(e.symm : E × Y →L[ℝ] E × Y)‖ * ‖T‖ ≤ 1 / 2 := by
    have hb : ‖T‖ ≤ L * ‖z - (xstar, ystar)‖ := by
      simpa [T, he] using hLip z hz _ (mem_ball_self hr)
    calc
      _ ≤ K * (L * ‖z - (xstar, ystar)‖) :=
        mul_le_mul (by dsimp [K]; linarith) hb (norm_nonneg _) hK.le
      _ ≤ K * L * δ := by rw [mul_assoc]; gcongr
      _ ≤ _ := hscale
  obtain ⟨B, hB', hBnorm, -⟩ := e.exists_symm_norm_le_of_add T (hT.trans_lt (by norm_num))
  have hB : (B : E × Y →L[ℝ] E × Y) = sqpKKT H A AT z := by rw [hB']; dsimp [T]; abel
  have hBnorm' : ‖(B.symm : E × Y →L[ℝ] E × Y)‖ ≤ 2 * K := by
    refine hBnorm.trans ((div_le_iff₀ (by linarith)).2 ?_)
    nlinarith [mul_nonneg hK.le (sub_nonneg.2 hT)]
  have hdiff : ‖(B : E × Y →L[ℝ] E × Y) - sqpKKT H A AT w‖ ≤ L * ‖y - ystar‖ := by
    rw [hB]
    simpa [z, w, Prod.norm_def] using hLip z hz w hw
  have hext : sqpExternalStep g c H A AT ystar x y =
      (w - B.symm (sqpResidual g c AT w)).1 := by
    unfold sqpExternalStep
    change x - ((sqpKKT H A AT z).inverse (sqpResidual g c AT w)).1 = _
    rw [← hB, ContinuousLinearMap.inverse_equiv]
    rfl
  constructor
  · let p := B.symm (sqpResidual g c AT w)
    have h := sqpCorrection_of_inverse g c H A AT x y ystar B hB
    refine ⟨ystar - p.2, ?_⟩
    rw [hext]
    change IsSQPCorrection g c H A AT (x, y) (x - p.1 - x) (ystar - p.2)
    rw [show x - p.1 - x = -p.1 by abel]
    exact h
  · rw [hext]
    calc
      _ ≤ ‖w - B.symm (sqpResidual g c AT w) - (xstar, ystar)‖ := norm_fst_le _
      _ ≤ ‖(B.symm : E × Y →L[ℝ] E × Y)‖ *
          ((L * ‖y - ystar‖) * ‖w - (xstar, ystar)‖ +
            L / 2 * ‖w - (xstar, ystar)‖ ^ 2) :=
        Newton.norm_approxStep_sub_le hstar hF hLip hw B hdiff
      _ ≤ 2 * K * ((L * ‖y - ystar‖) * ‖x - xstar‖ + L / 2 * ‖x - xstar‖ ^ 2) := by
        rw [hwDist]
        gcongr
      _ = _ := by ring

private theorem sqp_external_convergence_within
    (g : E → E) (c : E → Y) (H : E × Y → E →L[ℝ] E)
    (A : E → E →L[ℝ] Y) (AT : E → Y →L[ℝ] E) {xstar : E} {ystar : Y}
    (hstar : sqpResidual g c AT (xstar, ystar) = 0)
    (e : (E × Y) ≃L[ℝ] (E × Y))
    (he : (e : E × Y →L[ℝ] E × Y) = sqpKKT H A AT (xstar, ystar))
    {r L ρ : ℝ} (hr : 0 < r) (hL : 0 ≤ L) (hρ : 0 < ρ)
    (hF : ∀ z ∈ ball (xstar, ystar) r, HasFDerivAt (sqpResidual g c AT) (sqpKKT H A AT z) z)
    (hLip : ∀ z ∈ ball (xstar, ystar) r, ∀ w ∈ ball (xstar, ystar) r,
      ‖sqpKKT H A AT z - sqpKKT H A AT w‖ ≤ L * ‖z - w‖) :
    ∃ δ > 0, δ ≤ ρ ∧ ∀ (x : ℕ → E) (y : ℕ → Y), x 0 ∈ ball xstar δ →
      (∀ k, y k ∈ ball ystar δ) → Tendsto y atTop (𝓝 ystar) →
      (∀ k, x (k + 1) = sqpExternalStep g c H A AT ystar (x k) (y k)) →
      (∀ k, x k ∈ ball xstar ρ) ∧ ConvergesQSuperlinearly x xstar ∧
      (∀ k, ∃ y', IsSQPCorrection g c H A AT (x k, y k) (x (k + 1) - x k) y') ∧
      ((∃ D : ℝ, ∀ᶠ k in atTop, ‖y k - ystar‖ ≤ D * ‖x k - xstar‖) →
        ConvergesQQuadratically x xstar) := by
  obtain ⟨δ₀, hδ₀, M, hM, hlocal⟩ := sqp_external_estimate g c H A AT hstar e he hr hL hF hLip
  let d := min δ₀ (1 / (4 * (M * L + 1)))
  let δ := min d ρ
  have hδ : 0 < δ := lt_min (lt_min hδ₀ (by positivity)) hρ
  have hscale : 2 * M * L * δ ≤ 1 / 2 := by
    have hd := (le_div_iff₀ (by positivity : 0 < 4 * (M * L + 1))).1
      ((min_le_left d ρ).trans (min_le_right δ₀ (1 / (4 * (M * L + 1)))))
    nlinarith
  refine ⟨δ, hδ, min_le_right d ρ, fun x y hx₀ hy hyt hstep => ?_⟩
  have hsub : ball xstar δ ⊆ ball xstar δ₀ := ball_subset_ball ((min_le_left d ρ).trans (min_le_left _ _))
  have hsubY : ball ystar δ ⊆ ball ystar δ₀ := ball_subset_ball ((min_le_left d ρ).trans (min_le_left _ _))
  have hrec (k : ℕ) (hx : x k ∈ ball xstar δ) :
      ‖x (k + 1) - xstar‖ ≤ ‖x k - xstar‖ / 2 := by
    have hb := (hlocal _ (hsub hx) _ (hsubY (hy k))).2
    have hx' : ‖x k - xstar‖ < δ := by simpa [mem_ball, dist_eq_norm] using hx
    have hy' : ‖y k - ystar‖ < δ := by simpa [mem_ball, dist_eq_norm] using hy k
    rw [hstep]
    refine hb.trans ?_
    rw [show ‖x k - xstar‖ / 2 = (1 / 2) * ‖x k - xstar‖ by ring]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ ≤ M * (L * δ + L / 2 * δ) := by gcongr
      _ ≤ 2 * M * L * δ := by nlinarith [mul_nonneg (mul_nonneg hM.le hL) hδ.le]
      _ ≤ _ := hscale
  have hstay : ∀ k, x k ∈ ball xstar δ := by
    intro k
    induction k with
    | zero => exact hx₀
    | succ k ih =>
      rw [mem_ball, dist_eq_norm]
      have hk : ‖x k - xstar‖ < δ := by simpa [mem_ball, dist_eq_norm] using ih
      exact (hrec k ih).trans_lt (by linarith)
  have hgeom (k : ℕ) : ‖x k - xstar‖ ≤ (1 / 2 : ℝ) ^ k * ‖x 0 - xstar‖ := by
    induction k with
    | zero => simp
    | succ k ih =>
      refine (hrec k (hstay k)).trans ?_
      calc
        _ ≤ ((1 / 2 : ℝ) ^ k * ‖x 0 - xstar‖) / 2 := by gcongr
        _ = _ := by rw [pow_succ]; ring
  have hxt : Tendsto x atTop (𝓝 xstar) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    refine squeeze_zero (fun _ => norm_nonneg _) hgeom ?_
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
        (by norm_num)).mul_const ‖x 0 - xstar‖
  have hbound k : ‖x (k + 1) - xstar‖ ≤
      M * (L * ‖y k - ystar‖ + L / 2 * ‖x k - xstar‖) * ‖x k - xstar‖ := by
    rw [hstep]
    exact (hlocal _ (hsub (hstay k)) _ (hsubY (hy k))).2
  refine ⟨fun k ↦ ball_subset_ball (min_le_right d ρ) (hstay k), ⟨hxt, IsLittleO.of_bound fun ε hε => ?_⟩, fun k => ?_, fun hD => ?_⟩
  · have ht : Tendsto (fun k => M * (L * ‖y k - ystar‖ + L / 2 * ‖x k - xstar‖))
        atTop (𝓝 0) := by
      have hxerr := tendsto_iff_norm_sub_tendsto_zero.1 hxt
      have hyerr := tendsto_iff_norm_sub_tendsto_zero.1 hyt
      simpa using ((hyerr.const_mul L).add (hxerr.const_mul (L / 2))).const_mul M
    filter_upwards [ht.eventually_lt_const hε] with k hk
    exact (hbound k).trans (mul_le_mul_of_nonneg_right hk.le (norm_nonneg _))
  · rw [hstep]
    exact (hlocal _ (hsub (hstay k)) _ (hsubY (hy k))).1
  · obtain ⟨D, hD⟩ := hD
    refine ⟨hxt, M * (L * D + L / 2), ?_⟩
    filter_upwards [hD] with k hk
    calc
      _ ≤ M * (L * ‖y k - ystar‖ + L / 2 * ‖x k - xstar‖) * ‖x k - xstar‖ := hbound k
      _ ≤ M * (L * (D * ‖x k - xstar‖) + L / 2 * ‖x k - xstar‖) * ‖x k - xstar‖ := by
        gcongr
      _ = _ := by ring

/-- **Theorem 15.2.1(i), corrected.** Externally supplied multipliers must stay
uniformly near the root multiplier from the start. Their convergence gives
primal Q-superlinear convergence, and a multiplier error bounded by a constant
times the primal error gives primal Q-quadratic convergence. -/
theorem theorem_15_2_1_i
    (g : E → E) (c : E → Y) (H : E × Y → E →L[ℝ] E)
    (A : E → E →L[ℝ] Y) (AT : E → Y →L[ℝ] E) {xstar : E} {ystar : Y}
    (hstar : sqpResidual g c AT (xstar, ystar) = 0)
    (e : (E × Y) ≃L[ℝ] (E × Y))
    (he : (e : E × Y →L[ℝ] E × Y) = sqpKKT H A AT (xstar, ystar))
    {r L : ℝ} (hr : 0 < r) (hL : 0 ≤ L)
    (hF : ∀ z ∈ ball (xstar, ystar) r, HasFDerivAt (sqpResidual g c AT) (sqpKKT H A AT z) z)
    (hLip : ∀ z ∈ ball (xstar, ystar) r, ∀ w ∈ ball (xstar, ystar) r,
      ‖sqpKKT H A AT z - sqpKKT H A AT w‖ ≤ L * ‖z - w‖) :
    ∃ δ > 0, ∀ (x : ℕ → E) (y : ℕ → Y), x 0 ∈ ball xstar δ →
      (∀ k, y k ∈ ball ystar δ) → Tendsto y atTop (𝓝 ystar) →
      (∀ k, x (k + 1) = sqpExternalStep g c H A AT ystar (x k) (y k)) →
      ConvergesQSuperlinearly x xstar ∧
      (∀ k, ∃ y', IsSQPCorrection g c H A AT (x k, y k) (x (k + 1) - x k) y') ∧
      ((∃ D : ℝ, ∀ᶠ k in atTop, ‖y k - ystar‖ ≤ D * ‖x k - xstar‖) →
        ConvergesQQuadratically x xstar) := by
  obtain ⟨δ, hδ, -, h⟩ := sqp_external_convergence_within g c H A AT hstar e he hr hL
    (zero_lt_one : (0 : ℝ) < 1) hF hLip
  exact ⟨δ, hδ, fun x y hx hy hyt hs ↦ (h x y hx hy hyt hs).2⟩

end Convergence

section MixedSQP

open scoped RealInnerProductSpace
open Constrained ContinuousLinearMap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V] {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]

private def mixedSQPEquality (c : ActiveDual ι κ) (A : V →L[ℝ] ActiveDual ι κ)
    (i : ι) (s : V) : ℝ := c (.inl i) + A s (.inl i)

private def mixedSQPInequality (c : ActiveDual ι κ) (A : V →L[ℝ] ActiveDual ι κ)
    (b : ν → ℝ) (B : ν → V →L[ℝ] ℝ) (j : κ ⊕ ν) (s : V) : ℝ :=
  Sum.elim (fun k ↦ -(c (.inr k) + A s (.inr k))) (fun j ↦ -(b j + B j s)) j

/-- The affine feasible set of the mixed SQP subproblem (15.2.16b). The active
inequalities at the base solution are the indices in the left summand. -/
def mixedSQPFeasible (c : ActiveDual ι κ) (A : V →L[ℝ] ActiveDual ι κ)
    (b : ν → ℝ) (B : ν → V →L[ℝ] ℝ) : Set V :=
  feasible (mixedSQPEquality c A) (mixedSQPInequality c A b B)

set_option maxHeartbeats 1000000 in
/-- A stationary active-set correction is a strict mixed-QP local minimizer
when the inactive slacks and active inequality multipliers are positive and
the Hessian is positive on the active null space. -/
theorem mixedSQP_strict_minimizer_of_active_correction
    {g : V} {H : V →L[ℝ] V} {c : ActiveDual ι κ} {A : V →L[ℝ] ActiveDual ι κ}
    {b : ν → ℝ} {B : ν → V →L[ℝ] ℝ} {s : V} {y : ActiveDual ι κ}
    (hH : (H : V →ₗ[ℝ] V).IsSymmetric)
    (hpos : ∀ d, A d = 0 → d ≠ 0 → 0 < ⟪H d, d⟫)
    (hstat : g + H s - A.adjoint y = 0) (hfeas : c + A s = 0)
    (hmult : ∀ j : κ, 0 < y (.inr j)) (hslack : ∀ j : ν, 0 < b j + B j s) :
    s ∈ mixedSQPFeasible c A b B ∧
      Optimization.IsStrictLocalMinOn (Subproblem.quadModel g H) (mixedSQPFeasible c A b B) s ∧
      (∀ j : κ, c (.inr j) + A s (.inr j) = 0) ∧
      (∀ j : ν, 0 < b j + B j s) := by
  let f := Subproblem.quadModel g H
  let ce := mixedSQPEquality c A
  let ci := mixedSQPInequality c A b B
  let row (i : ι ⊕ κ) : V →L[ℝ] ℝ := (PiLp.proj _ _ i).comp A
  let ce' (i : ι) := row (.inl i)
  let ci' (j : κ ⊕ ν) : V →L[ℝ] ℝ := Sum.elim (fun k ↦ -row (.inr k)) (fun j ↦ -B j) j
  let l (i : ι) := -y (.inl i)
  let μ : κ ⊕ ν → ℝ := Sum.elim (fun j ↦ y (.inr j)) (fun _ ↦ 0)
  have hcoord (i : ι ⊕ κ) : c i + A s i = 0 := by
    exact congrArg (fun z : ActiveDual ι κ ↦ z i) hfeas
  have hce (i : ι) (u : V) : HasFDerivAt (ce i) (ce' i) u :=
    ((ce' i).hasFDerivAt.const_add (c (.inl i)))
  have hci (j : κ ⊕ ν) (u : V) : HasFDerivAt (ci j) (ci' j) u := by
    cases j with
    | inl j => exact ((row (.inr j)).hasFDerivAt.const_add (c (.inr j))).neg
    | inr j => exact ((B j).hasFDerivAt.const_add (b j)).neg
  have hcf : ContDiffAt ℝ 2 f s := by
    unfold f Subproblem.quadModel
    exact ((contDiff_const.inner ℝ contDiff_id).add
      (contDiff_const.mul (contDiff_id.inner ℝ H.contDiff))).contDiffAt
  have hce2 (i : ι) : ContDiffAt ℝ 2 (ce i) s :=
    (contDiff_const.add (ce' i).contDiff).contDiffAt
  have hci2 (j : κ ⊕ ν) : ContDiffAt ℝ 2 (ci j) s := by
    cases j with
    | inl j => exact ((contDiff_const.add (row (.inr j)).contDiff).neg).contDiffAt
    | inr j => exact ((contDiff_const.add (B j).contDiff).neg).contDiffAt
  have hfd (u : V) : HasFDerivAt f (innerSL ℝ (g + H u)) u :=
    Subproblem.hasFDerivAt_quadModel hH u
  have hgrad (u : V) :
      innerSL ℝ (g + H u) + ∑ i, l i • ce' i + ∑ j, μ j • ci' j =
        innerSL ℝ (g + H u - A.adjoint y) := by
    ext d
    rw [innerSL_apply_apply, inner_sub_left, adjoint_inner_left, PiLp.inner_apply,
      Fintype.sum_sum_type]
    simp only [add_apply, sum_apply, smul_apply, smul_eq_mul, Fintype.sum_sum_type,
      l, μ, ce', ci', row, Sum.elim_inl, Sum.elim_inr, neg_apply, neg_mul, zero_mul,
      ContinuousLinearMap.comp_apply, PiLp.proj_apply,
      innerSL_apply_apply, RCLike.inner_apply, conj_trivial, mul_neg]
    simp [← Finset.sum_neg_distrib, mul_comm, sub_eq_add_neg, add_assoc, add_comm]
  have hkkt : IsKKTPoint (fun u ↦ innerSL ℝ (g + H u)) ce (fun i _ ↦ ce' i)
      ci (fun j _ ↦ ci' j) s l μ := by
    refine ⟨fun i ↦ hcoord (.inl i), ?_, ?_, ?_, ?_⟩
    · intro j
      cases j with
      | inl j => exact neg_nonpos.mpr (hcoord (.inr j)).ge
      | inr j => exact neg_nonpos.mpr (hslack j).le
    · rw [hgrad, hstat, map_zero]
    · intro j
      cases j with
      | inl j => exact (hmult j).le
      | inr j => exact le_rfl
    · intro j
      cases j with
      | inl j =>
        change y (.inr j) * -(c (.inr j) + A s (.inr j)) = 0
        simp [hcoord]
      | inr j => exact zero_mul _
  refine ⟨hkkt.mem_feasible, ?_, fun j ↦ hcoord (.inr j), hslack⟩
  apply isStrictLocalMinOn_of_secondOrder_sufficient hkkt hcf hce2 hci2 (hfd s)
    (fun i ↦ hce i s) (fun j ↦ hci j s)
  intro d hd hdne
  have hker : A d = 0 := by
    ext i
    cases i with
    | inl i => exact hd.1 i
    | inr j =>
      have hz := hd.2.1 (.inl j) (show ci (.inl j) s = 0 by
        change -(c (.inr j) + A s (.inr j)) = 0
        simp [hcoord]) (hmult j)
      exact neg_eq_zero.mp hz
  let L := kktLagrangian f ce ci l μ
  have hLf (u : V) : fderiv ℝ L u = innerSL ℝ (g + H u - A.adjoint y) := by
    have hD : HasFDerivAt L
        (innerSL ℝ (g + H u) + ∑ i, l i • ce' i + ∑ j, μ j • ci' j) u :=
      hasFDerivAt_kktLagrangian (f := f) (h := ce) (g := ci) (l := l) (μ := μ)
        (f' := fun v ↦ innerSL ℝ (g + H v))
        (h' := fun i _ ↦ ce' i) (g' := fun j _ ↦ ci' j)
        (hfd u) (fun i ↦ hce i u) (fun j ↦ hci j u)
    exact hD.fderiv.trans (hgrad u)
  have hLf' : fderiv ℝ (fderiv ℝ L) s = (innerSL ℝ).comp H := by
    rw [show fderiv ℝ L = fun u ↦ innerSL ℝ (g + H u - A.adjoint y) from funext hLf]
    exact (((innerSL ℝ).hasFDerivAt).comp s
      ((H.hasFDerivAt.const_add g).sub_const (A.adjoint y))).fderiv
  change 0 < iteratedFDeriv ℝ 2 L s (fun _ ↦ d)
  rw [iteratedFDeriv_two_apply, hLf']
  exact hpos d hker hdne

private theorem mixed_sqp_kkt_invertible
    {H : V × ActiveDual ι κ → V →L[ℝ] V} {A : V → V →L[ℝ] ActiveDual ι κ}
    {z : V × ActiveDual ι κ} (hA : Function.Surjective (A z.1))
    (hH : ∀ d, A z.1 d = 0 → d ≠ 0 → 0 < ⟪H z d, d⟫) :
    (sqpKKT H A (fun x ↦ (A x).adjoint) z).IsInvertible := by
  let F : (V × ActiveDual ι κ) →L[ℝ] (V × ActiveDual ι κ) :=
    (fst ℝ V (ActiveDual ι κ)).prod (-snd ℝ V (ActiveDual ι κ))
  have hF : F.comp F = ContinuousLinearMap.id ℝ (V × ActiveDual ι κ) := by
    ext w <;> simp [F]
  have heq : sqpKKT H A (fun x ↦ (A x).adjoint) z =
      (activeKKTLinearization (A z.1) (H z)).comp F := by
    ext w <;> simp [sqpKKT, F, sub_eq_add_neg]
  rw [heq]
  exact (theorem_3_2_7_activeKKT_invertible hA hH).comp (IsInvertible.of_inverse hF hF)

/-- The active-constraint identification in Theorem 15.2.2(iii). A convergent
sequence of active equality corrections, with steps tending to zero and
correction multipliers tending to the strictly complementary multipliers,
eventually consists of strict mixed-QP local minimizers with exactly the
prescribed active inequalities. -/
theorem theorem_15_2_2_iii
    {g : V → V} {c : V → ActiveDual ι κ} {H : V × ActiveDual ι κ → V →L[ℝ] V}
    {A : V → V →L[ℝ] ActiveDual ι κ} {b : ν → V → ℝ} {B : ν → V → V →L[ℝ] ℝ}
    {xStar : V} {yStar : ActiveDual ι κ}
    (hA : ContinuousAt A xStar) (hH : ContinuousAt H (xStar, yStar))
    (hb : ∀ j, ContinuousAt (b j) xStar) (hB : ∀ j, ContinuousAt (B j) xStar)
    (honto : Function.Surjective (A xStar))
    (hpos : ∀ d, A xStar d = 0 → d ≠ 0 → 0 < ⟪H (xStar, yStar) d, d⟫)
    (hmult : ∀ j : κ, 0 < yStar (.inr j)) (hslack : ∀ j : ν, 0 < b j xStar)
    {α : Type*} {l : Filter α} {z : α → V × ActiveDual ι κ} {s : α → V} {y : α → ActiveDual ι κ}
    (hz : Tendsto z l (𝓝 (xStar, yStar))) (hs : Tendsto s l (𝓝 0))
    (hy : Tendsto y l (𝓝 yStar))
    (hcor : ∀ᶠ k in l, IsSQPCorrection g c H A (fun x ↦ (A x).adjoint) (z k) (s k) (y k))
    (hsym : ∀ᶠ k in l, (H (z k) : V →ₗ[ℝ] V).IsSymmetric) :
    ∀ᶠ k in l,
      Optimization.IsStrictLocalMinOn (Subproblem.quadModel (g (z k).1) (H (z k)))
        (mixedSQPFeasible (c (z k).1) (A (z k).1) (fun j ↦ b j (z k).1) (fun j ↦ B j (z k).1))
        (s k) ∧
      (∀ j : κ, c (z k).1 (.inr j) + A (z k).1 (s k) (.inr j) = 0) ∧
      ∀ j : ν, 0 < b j (z k).1 + B j (z k).1 (s k) := by
  have hx : Tendsto (fun k ↦ (z k).1) l (𝓝 xStar) := continuous_fst.continuousAt.tendsto.comp hz
  have hA' := hA.tendsto.comp hx
  have hH' := hH.tendsto.comp hz
  have hreg := (hA'.prodMk_nhds hH').eventually
    (theorem_3_2_7_activeKKT_conditions_open.mem_nhds ⟨honto, hpos⟩)
  have hm : ∀ᶠ k in l, ∀ j : κ, 0 < y k (.inr j) := by
    apply eventually_all.mpr
    intro j
    let proj : ActiveDual ι κ →L[ℝ] ℝ := PiLp.proj _ _ (.inr j)
    exact ((proj.continuous.tendsto yStar).comp hy).eventually (Ioi_mem_nhds (hmult j))
  have hb' : ∀ᶠ k in l, ∀ j : ν, 0 < b j (z k).1 + B j (z k).1 (s k) := by
    apply eventually_all.mpr
    intro j
    have hcont : Continuous (fun q : (V →L[ℝ] ℝ) × V ↦ q.1 q.2) :=
      continuous_fst.clm_apply continuous_snd
    have hlin := (hcont.tendsto (B j xStar, 0)).comp (((hB j).tendsto.comp hx).prodMk_nhds hs)
    have ht := ((hb j).tendsto.comp hx).add hlin
    simp only [map_zero, add_zero] at ht
    exact ht.eventually (Ioi_mem_nhds (hslack j))
  filter_upwards [hcor, hsym, hreg, hm, hb'] with k hk hks hkr hkm hkb
  have hstat : g (z k).1 + H (z k) (s k) - (A (z k).1).adjoint (y k) = 0 := by
    rw [add_sub_assoc, hk.1, add_neg_cancel]
  have hfeas : c (z k).1 + A (z k).1 (s k) = 0 := by rw [hk.2, add_neg_cancel]
  exact (mixedSQP_strict_minimizer_of_active_correction hks hkr.2 hstat hfeas hkm hkb).2

set_option maxHeartbeats 1000000 in
/-- The closest-to-origin selection in Theorem 15.2.2. For convergent active
corrections, every feasible mixed-QP local minimizer whose norm is at most that
of the correction equals the correction, for all sufficiently large indices. -/
theorem theorem_15_2_2_closest
    {g : V → V} {c : V → ActiveDual ι κ} {H : V × ActiveDual ι κ → V →L[ℝ] V}
    {A : V → V →L[ℝ] ActiveDual ι κ} {b : ν → V → ℝ} {B : ν → V → V →L[ℝ] ℝ}
    {xStar : V} {yStar : ActiveDual ι κ}
    (hG : ContinuousAt g xStar) (hA : ContinuousAt A xStar) (hH : ContinuousAt H (xStar, yStar))
    (hb : ∀ j, ContinuousAt (b j) xStar) (hB : ∀ j, ContinuousAt (B j) xStar)
    (honto : Function.Surjective (A xStar))
    (hpos : ∀ d, A xStar d = 0 → d ≠ 0 → 0 < ⟪H (xStar, yStar) d, d⟫)
    (hstar : g xStar - (A xStar).adjoint yStar = 0)
    (hmult : ∀ j : κ, 0 < yStar (.inr j)) (hslack : ∀ j : ν, 0 < b j xStar)
    {α : Type*} {l : Filter α} {z : α → V × ActiveDual ι κ} {s : α → V} {y : α → ActiveDual ι κ}
    (hz : Tendsto z l (𝓝 (xStar, yStar))) (hs : Tendsto s l (𝓝 0))
    (hy : Tendsto y l (𝓝 yStar))
    (hcor : ∀ᶠ k in l, IsSQPCorrection g c H A (fun x ↦ (A x).adjoint) (z k) (s k) (y k))
    (hsym : ∀ᶠ k in l, (H (z k) : V →ₗ[ℝ] V).IsSymmetric) :
    ∀ᶠ k in l,
      let C := mixedSQPFeasible (c (z k).1) (A (z k).1) (fun j ↦ b j (z k).1) (fun j ↦ B j (z k).1)
      let f := Subproblem.quadModel (g (z k).1) (H (z k))
      s k ∈ C ∧ Optimization.IsStrictLocalMinOn f C (s k) ∧
        ∀ t ∈ C, IsLocalMinOn f C t → ‖t‖ ≤ ‖s k‖ → t = s k := by
  let Q := (V × ActiveDual ι κ) × V
  let q₀ : Q := ((xStar, yStar), 0)
  let G (q : Q) := g q.1.1 + H q.1 q.2
  let J (q : Q) := -A q.1.1
  have hx : ContinuousAt (fun q : Q ↦ q.1.1) q₀ :=
    continuous_fst.continuousAt.comp continuous_fst.continuousAt
  have hZc : ContinuousAt (fun q : Q ↦ q.1) q₀ := continuous_fst.continuousAt
  have hTc : ContinuousAt (fun q : Q ↦ q.2) q₀ := continuous_snd.continuousAt
  have hHc : ContinuousAt (fun q : Q ↦ H q.1) q₀ := by
    have ht : Tendsto (fun q : Q ↦ q.1) (𝓝 q₀) (𝓝 (xStar, yStar)) := hZc.tendsto
    exact hH.tendsto.comp ht
  have hGc : ContinuousAt G q₀ := (hG.comp hx).add (hHc.clm_apply hTc)
  have hJc : ContinuousAt J q₀ := (hA.comp hx).neg
  have hJonto : Function.Surjective (J q₀) := by
    intro a
    obtain ⟨d, hd⟩ := honto (-a)
    exact ⟨d, by change -(A xStar d) = a; rw [hd, neg_neg]⟩
  have hbase : G q₀ + (J q₀).adjoint yStar = 0 := by
    simpa [G, J, q₀, sub_eq_add_neg] using hstar
  obtain ⟨m, hm, hm₀, hrec⟩ :=
    continuous_active_multiplier_recovery hJc hGc hJonto hbase
  have hstrict : ∀ᶠ q in 𝓝 q₀, ∀ j : κ, 0 < m q (.inr j) := by
    apply eventually_all.mpr
    intro j
    let proj : ActiveDual ι κ →L[ℝ] ℝ := PiLp.proj _ _ (.inr j)
    have ht := (proj.continuous.continuousAt.comp hm).tendsto
    exact ht.eventually (Ioi_mem_nhds (show 0 < proj (m q₀) by rw [hm₀]; exact hmult j))
  have hinactive : ∀ᶠ q : Q in 𝓝 q₀, ∀ j : ν, 0 < b j q.1.1 + B j q.1.1 q.2 := by
    apply eventually_all.mpr
    intro j
    have ht := ((hb j).comp hx).add (((hB j).comp hx).clm_apply hTc)
    exact ht.tendsto.eventually (Ioi_mem_nhds (show 0 < b j xStar + B j xStar 0 by simpa using hslack j))
  have hn := hstrict.and (hinactive.and hrec)
  change ∀ᶠ q in 𝓝 ((xStar, yStar), (0 : V)), _ at hn
  rw [nhds_prod_eq] at hn
  obtain ⟨U, hU, W, hW, hrect⟩ := Filter.mem_prod_iff.mp hn
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp hW
  have hs' := hs.eventually (ball_mem_nhds (0 : V) hε)
  have hreg := (((hA.tendsto.comp (continuous_fst.continuousAt.tendsto.comp hz))).prodMk_nhds
    (hH.tendsto.comp hz)).eventually
      (theorem_3_2_7_activeKKT_conditions_open.mem_nhds ⟨honto, hpos⟩)
  have hident := theorem_15_2_2_iii hA hH hb hB honto hpos hmult hslack hz hs hy hcor hsym
  filter_upwards [hz.eventually hU, hs', hreg, hident, hcor, hsym] with k hk hks hkr hki hkc hsymk
  let a := A (z k).1
  let ce (i : ι) (t : V) := -mixedSQPEquality (c (z k).1) a i t
  let ci := mixedSQPInequality (c (z k).1) a (fun j ↦ b j (z k).1) (fun j ↦ B j (z k).1)
  have hC : mixedSQPFeasible (c (z k).1) a (fun j ↦ b j (z k).1) (fun j ↦ B j (z k).1) =
      feasible ce ci := by
    ext t
    simp [mixedSQPFeasible, feasible, ce, ci]
  have hcoord (i : ι ⊕ κ) : c (z k).1 i + a (s k) i = 0 := by
    have he : c (z k).1 + a (s k) = 0 := by rw [show a (s k) = -c (z k).1 from hkc.2, add_neg_cancel]
    exact congrArg (fun v : ActiveDual ι κ ↦ v i) he
  refine ⟨?_, hki.1, ?_⟩
  · rw [hC]
    refine ⟨fun i ↦ neg_eq_zero.mpr (hcoord (.inl i)), ?_⟩
    intro j
    cases j with
    | inl j => exact neg_nonpos.mpr (hcoord (.inr j)).ge
    | inr j => exact neg_nonpos.mpr (hki.2.2 j).le
  · intro t ht htmin hnorm
    have htB : t ∈ ball (0 : V) ε := by
      rw [dist_zero_right] at hks
      simpa [mem_ball, dist_zero_right] using hnorm.trans_lt hks
    obtain ⟨hmp, hneg, hsurj, hrecover⟩ := hrect
      (show (z k, t) ∈ U ×ˢ W from ⟨hk, hεW htB⟩)
    rw [hC] at ht htmin
    let row (i : ι ⊕ κ) : V →L[ℝ] ℝ := (PiLp.proj _ _ i).comp a
    have he (i : ι) : HasStrictFDerivAt (ce i) (-row (.inl i)) t :=
      (((row (.inl i)).hasStrictFDerivAt.const_add (c (z k).1 (.inl i))).neg)
    have hi (j : κ ⊕ ν) : HasStrictFDerivAt (ci j)
        (Sum.elim (fun i ↦ -row (.inr i)) (fun i ↦ -B i (z k).1) j) t := by
      cases j with
      | inl i => exact (((row (.inr i)).hasStrictFDerivAt.const_add (c (z k).1 (.inr i))).neg)
      | inr i => exact (((B i (z k).1).hasStrictFDerivAt.const_add (b i (z k).1)).neg)
    have hjac (d : V) (i : ι ⊕ κ) :
        J (z k, t) d i = Sum.elim (fun i ↦ fderiv ℝ (ce i) t d)
          (fun j ↦ fderiv ℝ (ci (.inl j)) t d) i := by
      cases i with
      | inl i => rw [Sum.elim_inl, (he i).hasFDerivAt.fderiv]; rfl
      | inr j => rw [Sum.elim_inr, (hi (.inl j)).hasFDerivAt.fderiv]; rfl
    have hnneg (j : ν) : ci (.inr j) t < 0 := neg_lt_zero.mpr (hneg j)
    have hlicq := active_surjective_licq (h := ce) (g := ci) hjac hsurj hnneg ht
    have hfd := Subproblem.hasFDerivAt_quadModel (g := g (z k).1) hsymk t
    obtain ⟨l, μ, hKKT⟩ := exists_kkt_of_isLocalMinOn hlicq htmin hfd.differentiableAt.hasFDerivAt
      (fun i ↦ by rw [(he i).hasFDerivAt.fderiv]; exact he i)
      (fun j ↦ by rw [(hi j).hasFDerivAt.fderiv]; exact hi j)
    let mult : ActiveDual ι κ := WithLp.toLp 2 (Sum.elim l (fun j ↦ μ (.inl j)))
    have hμ : Sum.elim (fun j ↦ mult (.inr j)) (fun _ ↦ 0) = μ := by
      funext j
      cases j with
      | inl j => rfl
      | inr j => exact ((mul_eq_zero.mp (hKKT.complementary (.inr j))).resolve_right (hnneg j).ne).symm
    have hstat : G (z k, t) + (J (z k, t)).adjoint mult = 0 := by
      have h := (active_kkt_stationary_iff (f := Subproblem.quadModel (g (z k).1) (H (z k)))
        (h := ce) (g := ci) (mult := mult) hjac).mpr
      rw [hμ] at h
      have h' := h hKKT.stationary
      rw [(Subproblem.hasGradientAt_quadModel (g := g (z k).1) hsymk t).gradient] at h'
      exact h'
    have heq := hrecover mult hstat
    have hact (j : κ) : ci (.inl j) t = 0 := by
      have hp : 0 < μ (.inl j) := by
        change 0 < mult (.inr j)
        rw [heq]
        exact hmp j
      exact (mul_eq_zero.mp (hKKT.complementary (.inl j))).resolve_left hp.ne'
    have hkern : a (t - s k) = 0 := by
      ext i
      simp only [map_sub, PiLp.sub_apply, PiLp.zero_apply]
      cases i with
      | inl i =>
        have he := neg_eq_zero.mp (hKKT.feasible_eq i)
        change c (z k).1 (.inl i) + a t (.inl i) = 0 at he
        linarith [hcoord (.inl i)]
      | inr j =>
        have he := neg_eq_zero.mp (hact j)
        change c (z k).1 (.inr j) + a t (.inr j) = 0 at he
        linarith [hcoord (.inr j)]
    have horth : ⟪H (z k) (t - s k), t - s k⟫ = 0 := by
      have hst : g (z k).1 + H (z k) t - a.adjoint mult = 0 := by
        simpa [G, J, a, sub_eq_add_neg] using hstat
      have hdiff : H (z k) (t - s k) = a.adjoint (mult - y k) := by
        have h' : H (z k) (s k) - a.adjoint (y k) = -g (z k).1 := hkc.1
        simp only [map_sub]
        rw [show H (z k) t = a.adjoint mult - g (z k).1 from by
          apply eq_sub_of_add_eq
          have hh := sub_eq_zero.mp hst
          rwa [add_comm] at hh]
        rw [show H (z k) (s k) = a.adjoint (y k) - g (z k).1 from by
          rw [sub_eq_iff_eq_add] at h'
          rw [h', sub_eq_add_neg, add_comm]]
        abel
      rw [hdiff, adjoint_inner_left, hkern, inner_zero_right]
    by_contra hne
    exact (hkr.2 (t - s k) hkern (sub_ne_zero.mpr hne)).ne' horth

/-- A single neighborhood gives the mixed SQP selection rule uniformly. Any
stationary active correction in that neighborhood is the unique closest local
minimizer of the mixed quadratic program and has exactly the base-active set. -/
theorem mixedSQP_uniform_closest
    {g : V → V} {c : V → ActiveDual ι κ} {H : V × ActiveDual ι κ → V →L[ℝ] V}
    {A : V → V →L[ℝ] ActiveDual ι κ} {b : ν → V → ℝ} {B : ν → V → V →L[ℝ] ℝ}
    {xStar : V} {yStar : ActiveDual ι κ}
    (hG : ContinuousAt g xStar) (hA : ContinuousAt A xStar) (hH : ContinuousAt H (xStar, yStar))
    (hb : ∀ j, ContinuousAt (b j) xStar) (hB : ∀ j, ContinuousAt (B j) xStar)
    (honto : Function.Surjective (A xStar))
    (hpos : ∀ d, A xStar d = 0 → d ≠ 0 → 0 < ⟪H (xStar, yStar) d, d⟫)
    (hstar : g xStar - (A xStar).adjoint yStar = 0)
    (hmult : ∀ j : κ, 0 < yStar (.inr j)) (hslack : ∀ j : ν, 0 < b j xStar) :
    ∃ η > 0, ∀ (z : V × ActiveDual ι κ) (s : V) (y : ActiveDual ι κ),
      z ∈ ball (xStar, yStar) η → s ∈ ball 0 η → y ∈ ball yStar η →
      IsSQPCorrection g c H A (fun x ↦ (A x).adjoint) z s y →
      (H z : V →ₗ[ℝ] V).IsSymmetric →
      let C := mixedSQPFeasible (c z.1) (A z.1) (fun j ↦ b j z.1) (fun j ↦ B j z.1)
      let f := Subproblem.quadModel (g z.1) (H z)
      s ∈ C ∧ Optimization.IsStrictLocalMinOn f C s ∧
      (∀ j : κ, c z.1 (.inr j) + A z.1 s (.inr j) = 0) ∧
      (∀ j : ν, 0 < b j z.1 + B j z.1 s) ∧
      ∀ t ∈ C, IsLocalMinOn f C t → ‖t‖ ≤ ‖s‖ → t = s := by
  let X := (V × ActiveDual ι κ) × V × ActiveDual ι κ
  let a : X := ((xStar, yStar), 0, yStar)
  let S : Set X := {v | IsSQPCorrection g c H A (fun x ↦ (A x).adjoint) v.1 v.2.1 v.2.2 ∧
    (H v.1 : V →ₗ[ℝ] V).IsSymmetric}
  have hz : Tendsto (fun v : X ↦ v.1) (𝓝[S] a) (𝓝 (xStar, yStar)) :=
    continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun v : X ↦ v.2.1) (𝓝[S] a) (𝓝 0) :=
    (continuous_fst.comp continuous_snd).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hy : Tendsto (fun v : X ↦ v.2.2) (𝓝[S] a) (𝓝 yStar) :=
    (continuous_snd.comp continuous_snd).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hS : ∀ᶠ v in 𝓝[S] a, v ∈ S := self_mem_nhdsWithin
  have hc : ∀ᶠ v : X in 𝓝[S] a, IsSQPCorrection g c H A (fun x ↦ (A x).adjoint) v.1 v.2.1 v.2.2 :=
    hS.mono fun _ h ↦ h.1
  have hh : ∀ᶠ v : X in 𝓝[S] a, (H v.1 : V →ₗ[ℝ] V).IsSymmetric :=
    hS.mono fun _ h ↦ h.2
  have ht := theorem_15_2_2_closest hG hA hH hb hB honto hpos hstar hmult hslack hz hs hy hc hh
  have hi := theorem_15_2_2_iii hA hH hb hB honto hpos hmult hslack hz hs hy hc hh
  have hall := eventually_nhdsWithin_iff.mp (ht.and hi)
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨η, hη, fun z s y hz hs hy hc hh ↦ ?_⟩
  have hv : ((z, s, y) : X) ∈ ball a η := by
    simp only [mem_ball, dist_eq_norm, a, Prod.mk_sub_mk, Prod.norm_def, sub_zero] at hz hs hy ⊢
    exact max_lt hz (max_lt hs hy)
  obtain ⟨hc', hi'⟩ := hball hv ⟨hc, hh⟩
  exact ⟨hc'.1, hc'.2.1, hi'.2.1, hi'.2.2, hc'.2.2⟩

omit [FiniteDimensional ℝ V] in
private theorem sqpGradient_continuousAt {g : V → V} {c : V → ActiveDual ι κ}
    {A : V → V →L[ℝ] ActiveDual ι κ} {x : V} {y : ActiveDual ι κ}
    (hA : ContinuousAt A x)
    (hR : ContinuousAt (sqpResidual g c (fun v ↦ (A v).adjoint)) (x, y)) :
    ContinuousAt g x := by
  have hp : ContinuousAt (fun v : V ↦ (v, y)) x := continuousAt_id.prodMk continuousAt_const
  have ht : Tendsto (fun v : V ↦ (v, y)) (𝓝 x) (𝓝 (x, y)) := hp.tendsto
  have h₁ : ContinuousAt (fun v ↦ (sqpResidual g c (fun w ↦ (A w).adjoint) (v, y)).1) x :=
    continuous_fst.continuousAt.tendsto.comp (hR.tendsto.comp ht)
  have h₂ : ContinuousAt (fun v ↦ (A v).adjoint y) x :=
    (ContinuousLinearMap.adjoint.continuous.continuousAt.comp hA).clm_apply continuousAt_const
  convert h₁.add h₂ using 1
  funext v
  change g v = g v - (A v).adjoint y + (A v).adjoint y
  abel

/-- Theorem 15.2.2(ii), with the active equations made explicit. The Newton
iterates for the active KKT system converge Q-quadratically. Their corrections
are the unique closest mixed-QP local minimizers at every iteration and identify the active set. -/
theorem theorem_15_2_2_ii
    (g : V → V) (c : V → ActiveDual ι κ) (H : V × ActiveDual ι κ → V →L[ℝ] V)
    (A : V → V →L[ℝ] ActiveDual ι κ) (b : ν → V → ℝ) (B : ν → V → V →L[ℝ] ℝ)
    {xStar : V} {yStar : ActiveDual ι κ}
    (hstar : sqpResidual g c (fun x ↦ (A x).adjoint) (xStar, yStar) = 0)
    {r L : ℝ} (hr : 0 < r) (hL : 0 ≤ L)
    (hF : ∀ z ∈ ball (xStar, yStar) r,
      HasFDerivAt (sqpResidual g c (fun x ↦ (A x).adjoint))
        (sqpKKT H A (fun x ↦ (A x).adjoint) z) z)
    (hLip : ∀ z ∈ ball (xStar, yStar) r, ∀ w ∈ ball (xStar, yStar) r,
      ‖sqpKKT H A (fun x ↦ (A x).adjoint) z -
        sqpKKT H A (fun x ↦ (A x).adjoint) w‖ ≤ L * ‖z - w‖)
    (hA : ContinuousAt A xStar) (hH : ContinuousAt H (xStar, yStar))
    (hb : ∀ j, ContinuousAt (b j) xStar) (hB : ∀ j, ContinuousAt (B j) xStar)
    (honto : Function.Surjective (A xStar))
    (hpos : ∀ d, A xStar d = 0 → d ≠ 0 → 0 < ⟪H (xStar, yStar) d, d⟫)
    (hmult : ∀ j : κ, 0 < yStar (.inr j)) (hslack : ∀ j : ν, 0 < b j xStar)
    (hsym : ∀ z ∈ ball (xStar, yStar) r, (H z : V →ₗ[ℝ] V).IsSymmetric) :
    ∃ δ > 0, ∀ z₀ ∈ ball (xStar, yStar) δ,
      let u := Newton.iterate (sqpResidual g c (fun x ↦ (A x).adjoint))
        (sqpKKT H A (fun x ↦ (A x).adjoint)) z₀
      let s := fun k ↦ (u (k + 1)).1 - (u k).1
      ConvergesQQuadratically u (xStar, yStar) ∧
        ∀ k : ℕ,
          s k ∈ mixedSQPFeasible (c (u k).1) (A (u k).1)
            (fun j ↦ b j (u k).1) (fun j ↦ B j (u k).1) ∧
          Optimization.IsStrictLocalMinOn (Subproblem.quadModel (g (u k).1) (H (u k)))
            (mixedSQPFeasible (c (u k).1) (A (u k).1) (fun j ↦ b j (u k).1) (fun j ↦ B j (u k).1))
            (s k) ∧
          (∀ j : κ, c (u k).1 (.inr j) + A (u k).1 (s k) (.inr j) = 0) ∧
          (∀ j : ν, 0 < b j (u k).1 + B j (u k).1 (s k)) ∧
          ∀ t ∈ mixedSQPFeasible (c (u k).1) (A (u k).1) (fun j ↦ b j (u k).1) (fun j ↦ B j (u k).1),
            IsLocalMinOn (Subproblem.quadModel (g (u k).1) (H (u k)))
              (mixedSQPFeasible (c (u k).1) (A (u k).1) (fun j ↦ b j (u k).1) (fun j ↦ B j (u k).1))
              t → ‖t‖ ≤ ‖s k‖ → t = s k := by
  obtain ⟨e, he⟩ := mixed_sqp_kkt_invertible (H := H) (A := A) (z := (xStar, yStar)) honto hpos
  have hG := sqpGradient_continuousAt hA ((hF _ (mem_ball_self hr)).continuousAt)
  have hst : g xStar - (A xStar).adjoint yStar = 0 := congrArg Prod.fst hstar
  obtain ⟨η, hη, hselect⟩ := mixedSQP_uniform_closest hG hA hH hb hB honto hpos hst hmult hslack
  let ρ := min r (η / 3)
  have hρ : 0 < ρ := lt_min hr (by positivity)
  have hρη : ρ ≤ η / 3 := min_le_right _ _
  have hρη' : ρ ≤ η := hρη.trans (by linarith)
  obtain ⟨δ, hδ, hlocal⟩ := sqp_newton_convergence_within g c H A (fun x ↦ (A x).adjoint)
    hstar e he hr hL hρ hF hLip
  refine ⟨δ, hδ, fun z₀ hz₀ ↦ ?_⟩
  obtain ⟨hstay, hquad, hcor⟩ := hlocal z₀ hz₀
  let u := Newton.iterate (sqpResidual g c (fun x ↦ (A x).adjoint))
    (sqpKKT H A (fun x ↦ (A x).adjoint)) z₀
  have hdist (k : ℕ) : ‖(u k).1 - xStar‖ < ρ ∧ ‖(u k).2 - yStar‖ < ρ := by
    have h := hstay k
    rw [mem_ball, dist_eq_norm, Prod.norm_def] at h
    exact max_lt_iff.mp h
  refine ⟨hquad, fun k ↦ ?_⟩
  have hz : u k ∈ ball (xStar, yStar) η := ball_subset_ball hρη' (hstay k)
  have hy : (u (k + 1)).2 ∈ ball yStar η := by
    rw [mem_ball, dist_eq_norm]
    exact (hdist (k + 1)).2.trans_le hρη'
  have hs : (u (k + 1)).1 - (u k).1 ∈ ball (0 : V) η := by
    rw [mem_ball, dist_zero_right]
    have he := norm_sub_le_norm_sub_add_norm_sub (u (k + 1)).1 xStar (u k).1
    rw [norm_sub_rev xStar] at he
    exact he.trans_lt (by linarith [(hdist (k + 1)).1, (hdist k).1])
  have h := hselect (u k) _ _ hz hs hy (hcor k)
    (hsym _ (ball_subset_ball (min_le_left r (η / 3)) (hstay k)))
  exact h

/-- Theorem 15.2.2(i), with the external multiplier sequence confined to the
local neighborhood from the first step. Active-equation steps have the
stated convergence rates and give the unique closest mixed-QP local minimizers at every iteration
with the prescribed active set. -/
theorem theorem_15_2_2_i
    (g : V → V) (c : V → ActiveDual ι κ) (H : V × ActiveDual ι κ → V →L[ℝ] V)
    (A : V → V →L[ℝ] ActiveDual ι κ) (b : ν → V → ℝ) (B : ν → V → V →L[ℝ] ℝ)
    {xStar : V} {yStar : ActiveDual ι κ}
    (hstar : sqpResidual g c (fun x ↦ (A x).adjoint) (xStar, yStar) = 0)
    {r L : ℝ} (hr : 0 < r) (hL : 0 ≤ L)
    (hF : ∀ z ∈ ball (xStar, yStar) r,
      HasFDerivAt (sqpResidual g c (fun x ↦ (A x).adjoint))
        (sqpKKT H A (fun x ↦ (A x).adjoint) z) z)
    (hLip : ∀ z ∈ ball (xStar, yStar) r, ∀ w ∈ ball (xStar, yStar) r,
      ‖sqpKKT H A (fun x ↦ (A x).adjoint) z -
        sqpKKT H A (fun x ↦ (A x).adjoint) w‖ ≤ L * ‖z - w‖)
    (hA : ContinuousAt A xStar) (hH : ContinuousAt H (xStar, yStar))
    (hb : ∀ j, ContinuousAt (b j) xStar) (hB : ∀ j, ContinuousAt (B j) xStar)
    (honto : Function.Surjective (A xStar))
    (hpos : ∀ d, A xStar d = 0 → d ≠ 0 → 0 < ⟪H (xStar, yStar) d, d⟫)
    (hmult : ∀ j : κ, 0 < yStar (.inr j)) (hslack : ∀ j : ν, 0 < b j xStar)
    (hsym : ∀ z ∈ ball (xStar, yStar) r, (H z : V →ₗ[ℝ] V).IsSymmetric) :
    ∃ δ > 0, ∀ (x : ℕ → V) (y : ℕ → ActiveDual ι κ), x 0 ∈ ball xStar δ →
      (∀ k, y k ∈ ball yStar δ) → Tendsto y atTop (𝓝 yStar) →
      (∀ k, x (k + 1) = sqpExternalStep g c H A (fun v ↦ (A v).adjoint) yStar (x k) (y k)) →
      ConvergesQSuperlinearly x xStar ∧
      ((∃ D : ℝ, ∀ᶠ k in atTop, ‖y k - yStar‖ ≤ D * ‖x k - xStar‖) →
        ConvergesQQuadratically x xStar) ∧
      ∀ k : ℕ,
        let s := x (k + 1) - x k
        s ∈ mixedSQPFeasible (c (x k)) (A (x k)) (fun j ↦ b j (x k)) (fun j ↦ B j (x k)) ∧
        Optimization.IsStrictLocalMinOn (Subproblem.quadModel (g (x k)) (H (x k, y k)))
          (mixedSQPFeasible (c (x k)) (A (x k)) (fun j ↦ b j (x k)) (fun j ↦ B j (x k))) s ∧
        (∀ j : κ, c (x k) (.inr j) + A (x k) s (.inr j) = 0) ∧
        (∀ j : ν, 0 < b j (x k) + B j (x k) s) ∧
        ∀ t ∈ mixedSQPFeasible (c (x k)) (A (x k)) (fun j ↦ b j (x k)) (fun j ↦ B j (x k)),
          IsLocalMinOn (Subproblem.quadModel (g (x k)) (H (x k, y k)))
            (mixedSQPFeasible (c (x k)) (A (x k)) (fun j ↦ b j (x k)) (fun j ↦ B j (x k)))
            t → ‖t‖ ≤ ‖s‖ → t = s := by
  obtain ⟨e, he⟩ := mixed_sqp_kkt_invertible (H := H) (A := A) (z := (xStar, yStar)) honto hpos
  let AT (v : V) := (A v).adjoint
  let K := sqpKKT H A AT
  let R := sqpResidual g c AT
  let D (z : V × ActiveDual ι κ) := (K z).inverse (R (z.1, yStar))
  have hKC : ContinuousAt K (xStar, yStar) := by
    have hKL : LipschitzOnWith ⟨L, hL⟩ K (ball (xStar, yStar) r) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro v hv w hw
      rw [dist_eq_norm, dist_eq_norm]
      exact hLip v hv w hw
    exact hKL.continuousOn.continuousAt (ball_mem_nhds _ hr)
  have hinv : ContinuousAt (ContinuousLinearMap.inverse (R := ℝ)) (K (xStar, yStar)) := by
    have heK : (e : (V × ActiveDual ι κ) →L[ℝ] (V × ActiveDual ι κ)) =
        K (xStar, yStar) := he
    rw [← ringInverse_eq_inverse, ← heK]
    exact NormedRing.inverse_continuousAt ((ContinuousLinearEquiv.unitsEquiv ℝ _).symm e)
  have hRC := (hF _ (mem_ball_self hr)).continuousAt
  have hRfreeze : ContinuousAt (fun z : V × ActiveDual ι κ ↦ R (z.1, yStar)) (xStar, yStar) := by
    have hw : Tendsto (fun z : V × ActiveDual ι κ ↦ (z.1, yStar))
        (𝓝 (xStar, yStar)) (𝓝 (xStar, yStar)) :=
      continuous_fst.continuousAt.tendsto.prodMk_nhds tendsto_const_nhds
    exact hRC.tendsto.comp hw
  have hD : ContinuousAt D (xStar, yStar) := (hinv.comp hKC).clm_apply hRfreeze
  have hDzero : D (xStar, yStar) = 0 := by
    change (K (xStar, yStar)).inverse (R (xStar, yStar)) = 0
    rw [show R (xStar, yStar) = 0 from hstar, map_zero]
  have hG := sqpGradient_continuousAt hA hRC
  have hst : g xStar - (A xStar).adjoint yStar = 0 := congrArg Prod.fst hstar
  obtain ⟨η, hη, hselect⟩ := mixedSQP_uniform_closest hG hA hH hb hB honto hpos hst hmult hslack
  have hnear : ∀ᶠ z in 𝓝 (xStar, yStar), (K z).IsInvertible ∧ D z ∈ ball 0 η := by
    refine ((hKC.tendsto.eventually
      ((show (K (xStar, yStar)).IsInvertible from ⟨e, he⟩).eventually_nhds))).and ?_
    apply hD.tendsto.eventually
    rw [hDzero]
    exact ball_mem_nhds _ hη
  obtain ⟨ξ, hξ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let ρ := min ξ (min r η)
  have hρ : 0 < ρ := lt_min hξ (lt_min hr hη)
  obtain ⟨δ, hδ, hδρ, hlocal⟩ := sqp_external_convergence_within g c H A AT hstar e he hr hL hρ hF hLip
  refine ⟨δ, hδ, fun x y hx₀ hynear hy hstep ↦ ?_⟩
  obtain ⟨hstay, hsuper, -, hquad⟩ := hlocal x y hx₀ hynear hy hstep
  refine ⟨hsuper, hquad, fun k ↦ ?_⟩
  let z := (x k, y k)
  let d := D z
  let mult := yStar - d.2
  have hz : z ∈ ball (xStar, yStar) ρ := by
    have hx := hstay k
    have hy := ball_subset_ball hδρ (hynear k)
    rw [mem_ball, dist_eq_norm, Prod.norm_def]
    exact max_lt (by simpa [z, mem_ball, dist_eq_norm] using hx)
      (by simpa [z, mem_ball, dist_eq_norm] using hy)
  obtain ⟨⟨Ek, hEk⟩, hd⟩ := hball (ball_subset_ball (min_le_left ξ (min r η)) hz)
  have hstep₀ : x (k + 1) - x k = -d.1 := by
    rw [hstep k]
    change x k - d.1 - x k = _
    abel
  have hcor : IsSQPCorrection g c H A AT z (x (k + 1) - x k) mult := by
    rw [hstep₀]
    have hEq : d = Ek.symm (R (x k, yStar)) := by
      change (K z).inverse (R (x k, yStar)) = _
      rw [← hEk, inverse_equiv]
      rfl
    change IsSQPCorrection g c H A AT (x k, y k) (-d.1) (yStar - d.2)
    rw [hEq]
    exact sqpCorrection_of_inverse g c H A AT (x k) (y k) yStar Ek hEk
  have hd' : ‖d.1‖ < η ∧ ‖d.2‖ < η := by
    change d ∈ ball (0 : V × ActiveDual ι κ) η at hd
    rwa [mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff] at hd
  have hs : x (k + 1) - x k ∈ ball (0 : V) η := by
    rw [hstep₀, mem_ball, dist_zero_right, norm_neg]
    exact hd'.1
  have hm : mult ∈ ball yStar η := by
    rw [mem_ball, dist_eq_norm]
    change ‖yStar - d.2 - yStar‖ < η
    rw [show yStar - d.2 - yStar = -d.2 by abel, norm_neg]
    exact hd'.2
  have h := hselect z _ mult (ball_subset_ball ((min_le_right ξ (min r η)).trans (min_le_right r η)) hz)
    hs hm hcor (hsym z (ball_subset_ball ((min_le_right ξ (min r η)).trans (min_le_left r η)) hz))
  exact h

end MixedSQP

section Example

local notation "X" => ℝ × ℝ

private def exampleGrad (x : X) : X := (x.1, 0)
private noncomputable def exampleConstraint (x : X) : ℝ := x.2 + x.1 ^ 2 / 2

private def exampleJacobian (x : X) : X →L[ℝ] ℝ :=
  x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ

private def exampleTranspose (x : X) : ℝ →L[ℝ] X :=
  (x.1 • ContinuousLinearMap.id ℝ ℝ).prod (ContinuousLinearMap.id ℝ ℝ)

private def exampleHessian (z : X × ℝ) : X →L[ℝ] X :=
  ((1 - z.2) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod 0

private noncomputable def exampleObjective (x : X) : ℝ := x.1 ^ 2 / 2

private theorem exampleObjective_hasFDerivAt (x : X) :
    HasFDerivAt exampleObjective (x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) x := by
  have h : HasFDerivAt (fun p : X => p.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) x :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have hh := (h.mul h).const_mul (1 / 2 : ℝ)
  convert hh using 1
  · funext p
    dsimp [exampleObjective]
    ring
  · apply ContinuousLinearMap.ext
    intro p
    simp [smul_eq_mul]
    ring

private theorem exampleConstraint_hasFDerivAt (x : X) :
    HasFDerivAt exampleConstraint (exampleJacobian x) x := by
  change HasFDerivAt (fun p : X => p.2 + exampleObjective p)
    (x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ) x
  rw [add_comm]
  exact (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.fun_add (exampleObjective_hasFDerivAt x)

private theorem exampleLagrangianGrad_hasFDerivAt (x : X) (y : ℝ) :
    HasFDerivAt (fun p => exampleGrad p - exampleTranspose p y) (exampleHessian (x, y)) x := by
  have he : (fun p => exampleGrad p - exampleTranspose p y) =
      fun p => exampleHessian (x, y) p + (0, -y) := by
    funext p
    ext <;> simp [exampleGrad, exampleTranspose, exampleHessian, smul_eq_mul]; ring
  rw [he]
  exact (exampleHessian (x, y)).hasFDerivAt.add_const _

private theorem example_hessians_constant :
    ∃ D : X →L[ℝ] (X →L[ℝ] ℝ), ∀ x : X,
      HasFDerivAt (fun p : X => p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) D x ∧
      HasFDerivAt exampleJacobian D x := by
  let D := (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ)
  refine ⟨D, fun x => ?_⟩
  have h : HasFDerivAt (fun p : X => p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) D x := D.hasFDerivAt
  exact ⟨h, h.add_const (ContinuousLinearMap.snd ℝ ℝ ℝ)⟩

/-- For the equality constraint `w + z²/2 = 0` and objective `z²/2`, the root
has a nonsingular KKT operator. A first multiplier of one makes the stationary
equations inconsistent at every nearby point with nonzero first coordinate,
even if all subsequent supplied multipliers are zero. -/
theorem sqp_unrestricted_multiplier_counterexample :
    (∀ x : X, HasFDerivAt exampleObjective
      ((exampleGrad x).1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (exampleGrad x).2 • ContinuousLinearMap.snd ℝ ℝ ℝ) x ∧
      HasFDerivAt exampleConstraint (exampleJacobian x) x ∧
      ∀ y : ℝ, HasFDerivAt (fun p => exampleGrad p - exampleTranspose p y)
        (exampleHessian (x, y)) x) ∧
    (∃ D : X →L[ℝ] (X →L[ℝ] ℝ), ∀ x : X,
      HasFDerivAt (fun p : X => p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) D x ∧
      HasFDerivAt exampleJacobian D x) ∧
    (∀ (x s : X) (y : ℝ),
      (exampleTranspose x y).1 * s.1 + (exampleTranspose x y).2 * s.2 =
        y * exampleJacobian x s) ∧
    sqpResidual exampleGrad exampleConstraint exampleTranspose (0 : X × ℝ) = 0 ∧
    (∃ e : (X × ℝ) ≃L[ℝ] (X × ℝ),
      (e : (X × ℝ) →L[ℝ] (X × ℝ)) =
        sqpKKT exampleHessian exampleJacobian exampleTranspose 0) ∧
    ∃ y : ℕ → ℝ, Tendsto y atTop (𝓝 0) ∧
      ∀ r > 0, ∃ x : X, x ∈ ball (0 : X) r ∧
        ¬ ∃ (s : X) (y' : ℝ),
          IsSQPCorrection exampleGrad exampleConstraint exampleHessian
            exampleJacobian exampleTranspose (x, y 0) s y' := by
  refine ⟨fun x => ⟨by simpa [exampleGrad] using exampleObjective_hasFDerivAt x,
    exampleConstraint_hasFDerivAt x, exampleLagrangianGrad_hasFDerivAt x⟩,
    example_hessians_constant, ?_,
    by simp [sqpResidual, exampleGrad, exampleConstraint, exampleTranspose], ?_, ?_⟩
  · intro x s y
    simp [exampleTranspose, exampleJacobian, smul_eq_mul]
    ring
  · let e : (X × ℝ) ≃L[ℝ] (X × ℝ) :=
      { toFun := fun p => ((p.1.1, -p.2), p.1.2)
        invFun := fun p => ((p.1.1, p.2), -p.1.2)
        left_inv := by intro p; simp
        right_inv := by intro p; simp
        map_add' := by intro p q; simp [add_comm]
        map_smul' := by intro a p; simp [mul_neg]
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    refine ⟨e, ?_⟩
    apply ContinuousLinearMap.ext
    intro p
    ext <;> simp [e, sqpKKT, exampleHessian, exampleJacobian, exampleTranspose]
  · let y (k : ℕ) : ℝ := if k = 0 then 1 else 0
    refine ⟨y, ?_, fun r hr => ?_⟩
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
      simp [y, show k ≠ 0 by omega]
    · refine ⟨(r / 2, 0), ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        simpa [Prod.norm_def, Real.norm_of_nonneg (by positivity : 0 ≤ r / 2)] using half_lt_self hr
      · rintro ⟨s, y', h⟩
        have h₁ := congrArg Prod.fst h.1
        have h₂ := congrArg Prod.snd h.1
        simp [exampleGrad, exampleHessian, exampleTranspose, y, smul_eq_mul] at h₁ h₂
        nlinarith

end Example

end ConnGouldToint.Chapter15
