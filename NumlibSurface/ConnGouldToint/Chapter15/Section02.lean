import Numlib.Nonlinear.Newton
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
  let K := ‖(e.symm : E × Y →L[ℝ] E × Y)‖ + 1
  let L' := L + 1
  let δ := min r (1 / (2 * K * L'))
  have hK : 0 < K := by dsimp [K]; positivity
  have hL' : 0 < L' := by dsimp [L']; linarith
  have hδ : 0 < δ := lt_min hr (by positivity)
  have hLip' z hz w hw : ‖sqpKKT H A AT z - sqpKKT H A AT w‖ ≤ L' * ‖z - w‖ :=
    (hLip z hz w hw).trans (mul_le_mul_of_nonneg_right (by dsimp [L']; linarith) (norm_nonneg _))
  refine ⟨δ, hδ, fun z₀ hz₀ => ?_⟩
  let u := Newton.iterate (sqpResidual g c AT) (sqpKKT H A AT) z₀
  have hmain k := Newton.forall_norm_iterate_succ_sub_le_of_mem_ball hstar e he
    (show ‖(e.symm : E × Y →L[ℝ] E × Y)‖ ≤ K by dsimp [K]; linarith)
    hF hLip' hz₀ k
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
  refine ⟨⟨hu, K * L', Eventually.of_forall fun k => (hmain k).2.2.1⟩, fun k => ?_⟩
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
  obtain ⟨δ₀, hδ₀, M, hM, hlocal⟩ := sqp_external_estimate g c H A AT hstar e he hr hL hF hLip
  let δ := min δ₀ (1 / (4 * (M * L + 1)))
  have hδ : 0 < δ := lt_min hδ₀ (by positivity)
  have hscale : 2 * M * L * δ ≤ 1 / 2 := by
    have hd := (le_div_iff₀ (by positivity : 0 < 4 * (M * L + 1))).1
      (min_le_right δ₀ (1 / (4 * (M * L + 1))))
    nlinarith
  refine ⟨δ, hδ, fun x y hx₀ hy hyt hstep => ?_⟩
  have hsub : ball xstar δ ⊆ ball xstar δ₀ := ball_subset_ball (min_le_left _ _)
  have hsubY : ball ystar δ ⊆ ball ystar δ₀ := ball_subset_ball (min_le_left _ _)
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
  refine ⟨⟨hxt, IsLittleO.of_bound fun ε hε => ?_⟩, fun k => ?_, fun hD => ?_⟩
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

end Convergence

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
