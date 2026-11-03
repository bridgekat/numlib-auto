import Numlib.Analysis.Matrix.ToEuclideanLin
import NumlibSurface.ConnGouldToint.Chapter07.Section03
import NumlibSurface.ConnGouldToint.Chapter07.Section03Direction

/-!
# The Moré–Sorensen algorithm with matrix direction certificates

The hard-case recurrence in Section 7.3 of [conn2000trust], with the
curvature condition supplied by the corrected LINPACK back solve.
-/

namespace ConnGouldToint.Chapter07

open Matrix Subproblem Filter Set WithLp
open scoped RealInnerProductSpace Topology

/-- Normalize the LINPACK back-solve vector in Euclidean coordinates. -/
noncomputable def linpackEuclideanDirection {n : ℕ} (y : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  ‖(toLp 2 y : EuclideanSpace ℝ (Fin n))‖⁻¹ • toLp 2 y

/-- The certified back solve is nonzero. Its normalized Euclidean
curvature equals the matrix Rayleigh quotient. -/
theorem linpackEuclideanDirection_spec {n : ℕ} (hn : 0 < n)
    {L : Matrix (Fin n) (Fin n) ℝ} {v w y : Fin n → ℝ}
    (hw : L *ᵥ w = v) (hy : Lᵀ *ᵥ y = w)
    (hv : ∀ i, v i = linpackSign (v i - L i i * w i)) :
    ‖linpackEuclideanDirection y‖ = 1 ∧
      ⟪linpackEuclideanDirection y,
        toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (L * Lᵀ) (linpackEuclideanDirection y)⟫ =
        linpackCurvature (L * Lᵀ) y := by
  have hyne : y ≠ 0 := by
    intro h
    have hz : w = 0 := by simpa [h] using hy.symm
    have hvz : v = 0 := by simpa [hz] using hw.symm
    let i : Fin n := ⟨0, hn⟩
    have h := abs_linpackSign (v i - L i i * w i)
    rw [← hv i, hvz] at h
    norm_num at h
  have hpos : 0 < ‖(toLp 2 y : EuclideanSpace ℝ (Fin n))‖ := by
    apply norm_pos_iff.mpr
    intro h
    exact hyne (congrArg ofLp h)
  let c := ‖(toLp 2 y : EuclideanSpace ℝ (Fin n))‖⁻¹
  have hdir : linpackEuclideanDirection y = toLp 2 (c • y) := by
    rw [WithLp.toLp_smul]
    rfl
  have hnorm : ‖linpackEuclideanDirection y‖ = 1 := by
    unfold linpackEuclideanDirection
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hpos.le), inv_mul_cancel₀ hpos.ne']
  have hunit : (c • y) ⬝ᵥ (c • y) = 1 := by
    rw [← EuclideanSpace.inner_toLp_toLp_real, ← hdir, real_inner_self_eq_norm_sq, hnorm, one_pow]
  refine ⟨hnorm, ?_⟩
  rw [hdir, Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp_real]
  exact (linpackCurvature_eq_of_normalization _ rfl hunit).symm

private theorem det_shift_leftmost_eq_zero {n : ℕ} (hn : 0 < n)
    {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric) :
    (M + (-leftmost hM) • 1).det = 0 := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_leftmost (hH := hM)
  let z : EuclideanSpace ℝ (Fin n) := hM.eigenvectorBasis rfl i
  have hnorm : ‖z‖ = 1 := (hM.eigenvectorBasis rfl).orthonormal.norm_eq_one i
  have hz : (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M + (-leftmost hM) • 1) z = 0 := by
    change toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M z + (-leftmost hM) • z = 0
    have he : toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M z = leftmost hM • z := by
      rw [← hi]
      exact apply_eigenvectorBasis' (hH := hM) i
    simp [he, neg_smul]
  by_contra hdet
  have hunit : IsUnit (M + (-leftmost hM) • 1) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hvec : (M + (-leftmost hM) • 1) *ᵥ ofLp z = 0 := by
    rw [← Matrix.toEuclideanCLM_add_smul_one, ← WithLp.toLp_ofLp 2 z,
      Matrix.toEuclideanCLM_toLp] at hz
    exact congrArg ofLp hz
  have hzero : ofLp z = 0 :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit (hvec.trans (Matrix.mulVec_zero _).symm)
  have hz0 : z = 0 := by
    simpa using congrArg (toLp 2) hzero
  simp [hz0] at hnorm

/-- The corrected LINPACK certificates provide the Euclidean vanishing
curvature condition along any filter of successful shifted factorizations. -/
theorem linpackEuclideanCurvature_tendsto {n : ℕ} (hn : 0 < n)
    {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric)
    {ι : Type*} {f : Filter ι} {x : ι → ℝ} {L : ι → Matrix (Fin n) (Fin n) ℝ}
    {v w y : ι → Fin n → ℝ} (hx : Tendsto x f (𝓝 (-leftmost hM)))
    (hcert : ∀ᶠ k in f, L k * (L k)ᵀ = M + x k • 1 ∧
      (L k).IsLowerTriangular ∧ (∀ i, 0 < L k i i) ∧
      L k *ᵥ w k = v k ∧ (L k)ᵀ *ᵥ y k = w k ∧
      ∀ i, v k i = linpackSign (v k i - L k i i * w k i)) :
    Tendsto (fun k => ⟪linpackEuclideanDirection (y k),
      (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M + x k • 1) (linpackEuclideanDirection (y k))⟫) f (𝓝 0) := by
  have hcont : Continuous (fun t : ℝ => (M + t • (1 : Matrix (Fin n) (Fin n) ℝ)).det) := by
    fun_prop
  have hlim := hcont.continuousAt.tendsto.comp hx
  rw [det_shift_leftmost_eq_zero hn hM] at hlim
  have hdet : Tendsto (fun k => (L k * (L k)ᵀ).det) f (𝓝 0) :=
    hlim.congr' (hcert.mono fun _ hk => congrArg Matrix.det hk.1.symm)
  have ht := linpackCurvature_tendsto_zero_of_eventually hn
    (hcert.mono fun _ hk => hk.2) hdet
  apply ht.congr'
  filter_upwards [hcert] with k ⟨hfact, _, _, hw, hy, hv⟩
  rw [← Matrix.toEuclideanCLM_add_smul_one, ← hfact]
  exact (linpackEuclideanDirection_spec hn hw hy hv).2.symm

/-- The transported direction gives a certified lower bound on the pole. -/
theorem linpackEuclidean_lower_bound {n : ℕ} (hn : 0 < n)
    {M L : Matrix (Fin n) (Fin n) ℝ}
    (hM : (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric)
    {x : ℝ} {v w y : Fin n → ℝ} (hfact : L * Lᵀ = M + x • 1)
    (hw : L *ᵥ w = v) (hy : Lᵀ *ᵥ y = w)
    (hv : ∀ i, v i = linpackSign (v i - L i i * w i)) :
    x - linpackCurvature (L * Lᵀ) y ≤ -leftmost hM := by
  obtain ⟨hnorm, hcurv⟩ := linpackEuclideanDirection_spec hn hw hy hv
  have h := add_leftmost_mul_norm_sq_le (hH := hM) x (linpackEuclideanDirection y)
  rw [hnorm, one_pow, mul_one, real_inner_comm, ← Matrix.toEuclideanCLM_add_smul_one, ← hfact,
    hcurv] at h
  linarith

/-- Successful matrix factorizations and greedy back solves certify the
hard-case convergence conclusions of the actual safeguarded recurrence.
Either boundary root is allowed, including the model-minimizing root. -/
theorem moreSorensen_hard_matrix_run {n : ℕ} (hn : 0 < n)
    {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric)
    {g sM : EuclideanSpace ℝ (Fin n)} (hg : g ≠ 0)
    {Δ θ : ℝ} {lo hi x b α : ℕ → ℝ} {L : ℕ → Matrix (Fin n) (Fin n) ℝ}
    {v w y : ℕ → Fin n → ℝ} (hΔ : 0 < Δ) (hθ : θ ∈ Ioo 0 1)
    (hsM : ‖sM‖ ≤ Δ)
    (hmul : IsTrustRegionMultiplier g (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M) Δ sM
      (-leftmost hM))
    (hlo : 0 ≤ lo 0) (hlr : lo 0 ≤ -leftmost hM) (hhi : -leftmost hM < hi 0)
    (hx0 : x 0 ∈ Icc (lo 0) (hi 0))
    (hbFailure : ∀ k, x k ≤ -leftmost hM → b k ≤ -leftmost hM)
    (hbSuccess : ∀ k, -leftmost hM < x k →
      b k = x k - linpackCurvature (L k * (L k)ᵀ) (y k))
    (hrec : ∀ k, (lo (k + 1), hi (k + 1), x (k + 1)) =
      moreSorensenSafeguardedStep g (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M) (-leftmost hM) Δ θ
        (lo k) (hi k) (x k) (b k))
    (hcert : ∀ k, -leftmost hM < x k → L k * (L k)ᵀ = M + x k • 1 ∧
      (L k).IsLowerTriangular ∧ (∀ i, 0 < L k i i) ∧
      L k *ᵥ w k = v k ∧ (L k)ᵀ *ᵥ y k = w k ∧
      ∀ i, v k i = linpackSign (v k i - L k i i * w k i))
    (hboundary : ∀ k, -leftmost hM < x k →
      ‖shiftedStep g (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M) (x k) +
        α k • linpackEuclideanDirection (y k)‖ = Δ) :
    Tendsto x atTop (𝓝 (-leftmost hM)) ∧
      (∃ j : ℕ → ℕ, Tendsto j atTop atTop ∧ ∀ k, -leftmost hM < x (j k)) ∧
      ∀ (j : ℕ → ℕ), Tendsto j atTop atTop → (∀ k, -leftmost hM < x (j k)) →
        let s := fun k => shiftedStep g (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M) (x (j k)) +
          α (j k) • linpackEuclideanDirection (y (j k))
        Tendsto (fun k => quadModel g (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M) (s k)) atTop
          (𝓝 (quadModel g (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M) sM)) ∧
          (∀ (l : ℕ → ℕ) (z : EuclideanSpace ℝ (Fin n)), Tendsto l atTop atTop →
            Tendsto (s ∘ l) atTop (𝓝 z) →
            z ∈ Metric.closedBall 0 Δ ∧
              IsMinOn (quadModel g (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M)) (Metric.closedBall 0 Δ) z) ∧
          ((∀ z ∈ Metric.closedBall 0 Δ,
            IsMinOn (quadModel g (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M)) (Metric.closedBall 0 Δ) z → z = sM) →
            Tendsto s atTop (𝓝 sM)) := by
  have hb (k : ℕ) : b k ≤ -leftmost hM := by
    rcases le_or_gt (x k) (-leftmost hM) with hk | hk
    · exact hbFailure k hk
    · obtain ⟨hfact, _, _, hw, hy, hv⟩ := hcert k hk
      rw [hbSuccess k hk]
      exact linpackEuclidean_lower_bound hn hM hfact hw hy hv
  have hxlim : Tendsto x atTop (𝓝 (-leftmost hM)) :=
    (moreSorensen_hard_safeguarded_run (H := toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M)
      (hH := hM) hg hΔ hθ hsM hmul hlo hlr hhi.le hx0 hb hrec).2
  let f := (atTop : Filter ℕ) ⊓ 𝓟 {k | -leftmost hM < x k}
  have hsuc : ∀ᶠ k in f, -leftmost hM < x k :=
    mem_inf_of_right (mem_principal_self _)
  have hcurv := linpackEuclideanCurvature_tendsto hn hM (f := f) (hxlim.mono_left inf_le_left)
    (hsuc.mono hcert)
  have hunit (k : ℕ) (hk : -leftmost hM < x k) : ‖linpackEuclideanDirection (y k)‖ = 1 := by
    obtain ⟨_, _, _, hw, hy, hv⟩ := hcert k hk
    exact (linpackEuclideanDirection_spec hn hw hy hv).1
  have hresult := moreSorensen_hard_safeguarded_corrections
    (H := toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M) (hH := hM)
    (α := α) (u := fun k => linpackEuclideanDirection (y k))
    hg hΔ hθ hsM hmul hlo hlr hhi hx0 hb hrec hunit hboundary hcurv
  exact hresult

end ConnGouldToint.Chapter07
