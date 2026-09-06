import Numlib.LinearSolve.Multigrid.Basic

/-!
# Convergence of the two-grid cycle

The two-grid error propagation operator `S^ν₂ (1 - Q) S^ν₁` of
`Numlib/LinearSolve/Multigrid/Basic.lean` contracts the energy norm as soon as two constants are
available:

* a **smoothing property** `‖S e‖_A² ≤ ‖e‖_A² - α q(A e)²` (`Multigrid.IsSmootherWith`): the
  smoother is `A`-nonexpansive, and what it removes is measured by a seminorm `q` of the residual;
* an **approximation property** `∃ c ∈ Vc, p (e - c)² ≤ β ‖e‖_A²`
  (`Multigrid.IsApproximationWith`): the coarse space approximates in a second seminorm `p`.

Neither can be proved by linear algebra — they are estimates about a discretization, and a book
that supplies them for its own finite-element spaces inherits everything here.  What the two
seminorms have to share is only the duality `‖⟪u, w⟫‖ ≤ q u * p w`, which is
`Multigrid.IsDualSeminormPair`; the classical pair `p = ‖·‖_D`, `q = ‖·‖_{D⁻¹}` for a symmetric
positive definite `D` is `Multigrid.isDualSeminormPair_energy`, and the Cauchy–Schwarz pair
`p = q = ‖·‖` is `Multigrid.isDualSeminormPair_norm`.

The geometric half of the argument is `Multigrid.energyNorm_le_of_isApproximationWith`: an error
in the range of the coarse-grid correction is `A`-orthogonal to the coarse space, so
`‖e‖_A² = ⟪A e, e - c⟫` for every coarse `c`, and the duality together with the approximation
property turns that into `‖e‖_A ≤ √β q(A e)`.  Feeding it into the smoothing property gives the
rate `√(1 - α/β)` (`Multigrid.energyNorm_twoGrid_le`,
`Multigrid.energyNorm_twoGridOperator_le`), and comparing the two bounds on one nonzero error
shows `α ≤ β` (`Multigrid.IsSmootherWith.le_of_isApproximationWith`).

The only concrete smoothing property proved here is the Richardson/weighted-Jacobi one,
`Multigrid.isSmootherWith_richardson`: for `S = 1 - ω D⁻¹ A` the constant is `α = ω (2 - ω γ)`,
where `γ` bounds the quadratic form of `A` by that of `D`.  It is positive exactly on the classical
range `0 < ω < 2/γ`, but the identity itself holds for every `ω`.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.  The smoothing property is his (13.62), the approximation property his (13.63),
  the convergence theorem his Theorem 13.3, and the weighted Jacobi computation his Example 13.8.
-/

namespace Multigrid

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-! ### A dual pair of seminorms -/

/-- Two nonnegative functions on `E` that are dual to each other for the inner product:
`‖⟪u, w⟫‖ ≤ q u * p w`.  This is the only relation between the seminorms of the smoothing and
approximation properties that the two-grid theorem uses, so it is what the theorem assumes
(Saad, *Iterative Methods for Sparse Linear Systems*, (13.62)–(13.63), where `q = ‖·‖_{D⁻¹}` and
`p = ‖·‖_D`). -/
structure IsDualSeminormPair (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (p q : E → ℝ) : Prop where
  /-- The seminorm measuring the second argument is nonnegative. -/
  p_nonneg : ∀ w, 0 ≤ p w
  /-- The seminorm measuring the first argument is nonnegative. -/
  q_nonneg : ∀ u, 0 ≤ q u
  /-- The duality itself: `‖⟪u, w⟫‖ ≤ q u * p w`. -/
  norm_inner_le : ∀ u w, ‖inner 𝕜 u w‖ ≤ q u * p w

/-- The Cauchy–Schwarz pair: the norm is dual to itself. -/
theorem isDualSeminormPair_norm : IsDualSeminormPair 𝕜 (norm : E → ℝ) (norm : E → ℝ) :=
  ⟨fun _ => norm_nonneg _, fun _ => norm_nonneg _, fun _ _ => norm_inner_le_norm _ _⟩

/-- For a right inverse `Dinv` of a symmetric coercive `D`, the energy norm of `D` and the energy
norm of `Dinv` are dual: `‖⟪u, w⟫‖ ≤ ‖u‖_{D⁻¹} ‖w‖_D`.  With `D` the diagonal part of `A` this is
the pair Saad states the smoothing and approximation properties with. -/
theorem isDualSeminormPair_energy {D Dinv : E →ₗ[𝕜] E} (hD : D.IsSymmetricCoercive)
    (hinv : ∀ u, D (Dinv u) = u) :
    IsDualSeminormPair 𝕜 (energyNorm D) (energyNorm Dinv) := by
  have hnorm : ∀ u : E, energyNorm D (Dinv u) = energyNorm Dinv u := fun u => by
    have h : RCLike.re (inner 𝕜 (D (Dinv u)) (Dinv u)) = RCLike.re (inner 𝕜 (Dinv u) u) := by
      rw [hinv, ← inner_conj_symm (Dinv u) u, RCLike.conj_re]
    exact congrArg Real.sqrt h
  refine ⟨fun _ => energyNorm_nonneg _ _, fun _ => energyNorm_nonneg _ _, fun u w => ?_⟩
  have h : inner 𝕜 u w = energyInner D (Dinv u) w := by rw [energyInner, hinv]
  rw [h]
  exact (hD.abs_energyInner_le (Dinv u) w).trans_eq (by rw [hnorm])

/-! ### The two named hypotheses -/

/-- **The smoothing property** (Saad, *Iterative Methods for Sparse Linear Systems*, (13.62)):
the error propagation operator `S` of the smoother reduces the energy norm by an amount measured
by the seminorm `q` of the residual, `‖S e‖_A² ≤ ‖e‖_A² - α q(A e)²`.  It cannot be proved by
linear algebra alone; `Multigrid.isSmootherWith_richardson` is the one case the theory verifies. -/
def IsSmootherWith (A : E →ₗ[𝕜] E) (q : E → ℝ) (S : E →ₗ[𝕜] E) (α : ℝ) : Prop :=
  ∀ e, energyNorm A (S e) ^ 2 ≤ energyNorm A e ^ 2 - α * q (A e) ^ 2

/-- **The approximation property** of a coarse space (Saad, *Iterative Methods for Sparse Linear
Systems*, (13.63)): every error is approximated from `Vc` to within `β ‖e‖_A²` in the seminorm
`p`.  Stated with an existential rather than an infimum, which is what an interpolation estimate
provides and what the convergence proof consumes. -/
def IsApproximationWith (A : E →ₗ[𝕜] E) (p : E → ℝ) (Vc : Submodule 𝕜 E) (β : ℝ) : Prop :=
  ∀ e, ∃ c ∈ Vc, p (e - c) ^ 2 ≤ β * energyNorm A e ^ 2

namespace IsSmootherWith

variable {A : E →ₗ[𝕜] E} {q : E → ℝ} {S : E →ₗ[𝕜] E} {α : ℝ}

/-- A smoother with a nonnegative constant is `A`-nonexpansive: it never increases the energy
norm of the error. -/
theorem energyNorm_le (h : IsSmootherWith A q S α) (hα : 0 ≤ α) (e : E) :
    energyNorm A (S e) ≤ energyNorm A e := by
  refine energyNorm_le_of_sq_le ((h e).trans ?_)
  have : 0 ≤ α * q (A e) ^ 2 := mul_nonneg hα (sq_nonneg _)
  linarith

/-- Iterating a nonexpansive smoother stays nonexpansive. -/
theorem energyNorm_pow_le (h : IsSmootherWith A q S α) (hα : 0 ≤ α) (n : ℕ) (e : E) :
    energyNorm A ((S ^ n) e) ≤ energyNorm A e := by
  induction n generalizing e with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply]
      exact (ih (S e)).trans (h.energyNorm_le hα e)

end IsSmootherWith

/-! ### The geometry of the coarse-grid correction -/

section Geometry

variable (A : E →ₗ[𝕜] E) (hA : A.IsSymmetricCoercive) (Pr : F →ₗ[𝕜] E)

/-- The coarse-grid correction is the `A`-orthogonal projection onto the complement of the coarse
space, hence nonexpansive for the energy norm.  This is what lets the smoothing steps of a cycle
be counted separately from the correction. -/
theorem energyNorm_coarseCorrection_le (v : E) :
    energyNorm A (coarseCorrection A hA Pr v) ≤ energyNorm A v := by
  refine energyNorm_le_of_sq_le ?_
  set K := WithEnergy.submoduleMap A hA (LinearMap.range Pr) with hK
  have hval : WithEnergy.equiv A hA (coarseCorrection A hA Pr v)
      = Kᗮ.starProjection (WithEnergy.equiv A hA v) := by
    rw [coarseCorrection_apply, map_sub, equiv_coarseProjection,
      Submodule.starProjection_orthogonal_val]
  have h := K.norm_sq_eq_add_norm_sq_starProjection (WithEnergy.equiv A hA v)
  rw [← WithEnergy.norm_equiv A hA (coarseCorrection A hA Pr v), ← WithEnergy.norm_equiv A hA v,
    hval, h]
  have := sq_nonneg ‖K.starProjection (WithEnergy.equiv A hA v)‖
  linarith

end Geometry

section Convergence

variable {A : E →ₗ[𝕜] E} {hA : A.IsSymmetricCoercive} {Pr : F →ₗ[𝕜] E}
  {p q : E → ℝ} {α β : ℝ} [FiniteDimensional 𝕜 E]

/-- **The geometric half of Saad's Theorem 13.3** (Saad, *Iterative Methods for Sparse Linear
Systems*): an error left by the coarse-grid correction is `A`-orthogonal to the coarse space, so
the approximation property bounds its energy norm by the dual seminorm of its residual,
`‖e‖_A ≤ √β q(A e)`.  It is the statement the rate of the two-grid cycle and the inequality
`α ≤ β` both come from. -/
theorem energyNorm_le_of_isApproximationWith (hpq : IsDualSeminormPair 𝕜 p q)
    (happ : IsApproximationWith A p (LinearMap.range Pr) β) {e : E}
    (he : e ∈ LinearMap.range (coarseCorrection A hA Pr)) :
    energyNorm A e ≤ Real.sqrt β * q (A e) := by
  rw [range_coarseCorrection] at he
  have hPr : LinearMap.adjoint Pr (A e) = 0 := he
  obtain ⟨c, hc, hcb⟩ := happ e
  obtain ⟨y, rfl⟩ := hc
  have hq : 0 ≤ q (A e) := hpq.q_nonneg _
  have hzero : inner 𝕜 (A e) (Pr y) = (0 : 𝕜) := by
    rw [← LinearMap.adjoint_inner_left, hPr, inner_zero_left]
  have h1 : energyNorm A e ^ 2 = RCLike.re (inner 𝕜 (A e) (e - Pr y)) := by
    rw [hA.energyNorm_sq, inner_sub_right, hzero, sub_zero]
  have h2 : RCLike.re (inner 𝕜 (A e) (e - Pr y)) ≤ q (A e) * p (e - Pr y) :=
    (RCLike.re_le_norm _).trans (hpq.norm_inner_le _ _)
  have h3 : p (e - Pr y) ≤ Real.sqrt β * energyNorm A e := by
    calc p (e - Pr y) ≤ |p (e - Pr y)| := le_abs_self _
      _ = Real.sqrt (p (e - Pr y) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (β * energyNorm A e ^ 2) := Real.sqrt_le_sqrt hcb
      _ = Real.sqrt β * energyNorm A e := by
          rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (energyNorm_nonneg A e)]
  have hkey : energyNorm A e * energyNorm A e
      ≤ Real.sqrt β * q (A e) * energyNorm A e := by
    calc energyNorm A e * energyNorm A e = energyNorm A e ^ 2 := (sq _).symm
      _ ≤ q (A e) * p (e - Pr y) := h1.trans_le h2
      _ ≤ q (A e) * (Real.sqrt β * energyNorm A e) := by gcongr
      _ = Real.sqrt β * q (A e) * energyNorm A e := by ring
  rcases (energyNorm_nonneg A e).lt_or_eq with hpos | hzero'
  · exact le_of_mul_le_mul_right hkey hpos
  · rw [← hzero']
    exact mul_nonneg (Real.sqrt_nonneg β) hq

/-- **Saad's Theorem 13.3**, the constants: if a smoothing property and an approximation property
hold for the same dual pair, and some error left by the coarse-grid correction is nonzero, then
`α ≤ β`.  The nondegeneracy is needed: on the zero space every pair of constants qualifies. -/
theorem IsSmootherWith.le_of_isApproximationWith {S : E →ₗ[𝕜] E}
    (hsm : IsSmootherWith A q S α) (hpq : IsDualSeminormPair 𝕜 p q)
    (happ : IsApproximationWith A p (LinearMap.range Pr) β)
    {e : E} (he : e ∈ LinearMap.range (coarseCorrection A hA Pr)) (he0 : e ≠ 0) :
    α ≤ β := by
  have hgeo := energyNorm_le_of_isApproximationWith (hA := hA) hpq happ he
  have hpos : 0 < energyNorm A e := hA.energyNorm_pos he0
  have hb : 0 ≤ β := by
    by_contra hb
    push Not at hb
    rw [Real.sqrt_eq_zero_of_nonpos hb.le, zero_mul] at hgeo
    exact absurd hgeo (not_le.2 hpos)
  have hqpos : 0 < q (A e) := by
    by_contra h
    push Not at h
    exact absurd (hgeo.trans (mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg β) h))
      (not_le.2 hpos)
  have hbsq : energyNorm A e ^ 2 ≤ β * q (A e) ^ 2 := by
    calc energyNorm A e ^ 2 = energyNorm A e * energyNorm A e := sq _
      _ ≤ Real.sqrt β * q (A e) * (Real.sqrt β * q (A e)) :=
          mul_self_le_mul_self (energyNorm_nonneg A e) hgeo
      _ = Real.sqrt β ^ 2 * q (A e) ^ 2 := by ring
      _ = β * q (A e) ^ 2 := by rw [Real.sq_sqrt hb]
  have hsm' := hsm e
  have hnn : 0 ≤ energyNorm A (S e) ^ 2 := sq_nonneg _
  exact le_of_mul_le_mul_right (by linarith) (pow_pos hqpos 2)

/-- **Saad's Theorem 13.3** (Saad, *Iterative Methods for Sparse Linear Systems*): one coarse-grid
correction followed by one smoothing step contracts the energy norm of the error by the factor
`√(1 - α/β)`, which depends on nothing but the two constants. -/
theorem energyNorm_twoGrid_le {S : E →ₗ[𝕜] E} (hsm : IsSmootherWith A q S α)
    (hpq : IsDualSeminormPair 𝕜 p q)
    (happ : IsApproximationWith A p (LinearMap.range Pr) β) (hα : 0 ≤ α) (hβ : 0 < β) (v : E) :
    energyNorm A (S (coarseCorrection A hA Pr v))
      ≤ Real.sqrt (1 - α / β) * energyNorm A v := by
  have hmem : coarseCorrection A hA Pr v ∈ LinearMap.range (coarseCorrection A hA Pr) := ⟨v, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : E, coarseCorrection A hA Pr v = e := ⟨_, rfl⟩
  rw [he] at hmem ⊢
  have hgeo := energyNorm_le_of_isApproximationWith (hA := hA) hpq happ hmem
  have hnex : energyNorm A e ≤ energyNorm A v := by
    rw [← he]; exact energyNorm_coarseCorrection_le A hA Pr v
  have hqnn : 0 ≤ q (A e) := hpq.q_nonneg _
  have hsq : energyNorm A e ^ 2 ≤ β * q (A e) ^ 2 := by
    calc energyNorm A e ^ 2 = energyNorm A e * energyNorm A e := sq _
      _ ≤ Real.sqrt β * q (A e) * (Real.sqrt β * q (A e)) :=
          mul_self_le_mul_self (energyNorm_nonneg A e) hgeo
      _ = Real.sqrt β ^ 2 * q (A e) ^ 2 := by ring
      _ = β * q (A e) ^ 2 := by rw [Real.sq_sqrt hβ.le]
  have h1 := hsm e
  rcases (energyNorm_nonneg A e).lt_or_eq with hpos | hzero
  · -- the substantial case: the coarse-grid error is nonzero
    have hqpos : 0 < q (A e) ^ 2 := by
      rcases (sq_nonneg (q (A e))).lt_or_eq with h | h
      · exact h
      · rw [← h, mul_zero] at hsq
        exact absurd hsq (not_le.2 (pow_pos hpos 2))
    have hab : α ≤ β :=
      le_of_mul_le_mul_right (by linarith [sq_nonneg (energyNorm A (S e))]) hqpos
    have hcoef : 0 ≤ 1 - α / β := by rw [sub_nonneg, div_le_one hβ]; exact hab
    have h2 : α * (energyNorm A e ^ 2 / β) ≤ α * q (A e) ^ 2 := by
      refine mul_le_mul_of_nonneg_left ?_ hα
      rw [div_le_iff₀ hβ]
      calc energyNorm A e ^ 2 ≤ β * q (A e) ^ 2 := hsq
        _ = q (A e) ^ 2 * β := by ring
    have hid : (1 - α / β) * energyNorm A e ^ 2
        = energyNorm A e ^ 2 - α * (energyNorm A e ^ 2 / β) := by field_simp
    have h3 : energyNorm A (S e) ^ 2 ≤ (1 - α / β) * energyNorm A e ^ 2 := by
      rw [hid]; linarith
    have hmono : energyNorm A e ^ 2 ≤ energyNorm A v ^ 2 := by
      nlinarith [energyNorm_nonneg A e]
    have hbound : energyNorm A (S e) ^ 2 ≤ (1 - α / β) * energyNorm A v ^ 2 :=
      h3.trans (by gcongr)
    calc energyNorm A (S e) = Real.sqrt (energyNorm A (S e) ^ 2) :=
          (Real.sqrt_sq (energyNorm_nonneg A _)).symm
      _ ≤ Real.sqrt ((1 - α / β) * energyNorm A v ^ 2) := Real.sqrt_le_sqrt hbound
      _ = Real.sqrt (1 - α / β) * energyNorm A v := by
          rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (energyNorm_nonneg A v)]
  · -- a degenerate error: the smoothed error vanishes too
    have hnn : 0 ≤ α * q (A e) ^ 2 := mul_nonneg hα (sq_nonneg _)
    have h2 : energyNorm A (S e) ^ 2 ≤ 0 := by rw [← hzero] at h1; nlinarith
    have h3 : energyNorm A (S e) = 0 := by
      have := energyNorm_nonneg A (S e)
      nlinarith
    rw [h3]
    exact mul_nonneg (Real.sqrt_nonneg _) (energyNorm_nonneg A v)

/-- **Saad's Theorem 13.3** for the full cycle: with `ν₁` pre-smoothing and at least one
post-smoothing step, the two-grid error propagation operator contracts the energy norm by
`√(1 - α/β)`.  The extra smoothing steps can only help, being `A`-nonexpansive. -/
theorem energyNorm_twoGridOperator_le {S : E →ₗ[𝕜] E} (hsm : IsSmootherWith A q S α)
    (hpq : IsDualSeminormPair 𝕜 p q)
    (happ : IsApproximationWith A p (LinearMap.range Pr) β) (hα : 0 ≤ α) (hβ : 0 < β)
    {nu1 nu2 : ℕ} (hnu : 1 ≤ nu2) (v : E) :
    energyNorm A (twoGridOperator A hA Pr S nu1 nu2 v)
      ≤ Real.sqrt (1 - α / β) * energyNorm A v := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnu
  rw [twoGridOperator_apply, Nat.add_comm 1 k, pow_succ, Module.End.mul_apply]
  calc energyNorm A ((S ^ k) (S (coarseCorrection A hA Pr ((S ^ nu1) v))))
      ≤ energyNorm A (S (coarseCorrection A hA Pr ((S ^ nu1) v))) :=
        hsm.energyNorm_pow_le hα k _
    _ ≤ Real.sqrt (1 - α / β) * energyNorm A ((S ^ nu1) v) :=
        energyNorm_twoGrid_le hsm hpq happ hα hβ _
    _ ≤ Real.sqrt (1 - α / β) * energyNorm A v :=
        mul_le_mul_of_nonneg_left (hsm.energyNorm_pow_le hα nu1 v) (Real.sqrt_nonneg _)

end Convergence

/-! ### The one smoothing property that is a theorem -/

/-- **The smoothing property of a damped preconditioned Richardson iteration** (Saad, *Iterative
Methods for Sparse Linear Systems*, Example 13.8 and Exercise 13.15).  For `S = 1 - ω D⁻¹ A` with
`Dinv` a right inverse of a symmetric coercive `D` and `γ` a bound of the quadratic form of `A`
by that of `D`, the smoothing property holds with `q = ‖·‖_{D⁻¹}` and `α = ω (2 - ω γ)`, which is
positive exactly for `0 < ω < 2/γ`.  Richardson is `D = 1`, weighted Jacobi is `D` the diagonal
part of `A`. -/
theorem isSmootherWith_richardson {A D Dinv : E →ₗ[𝕜] E} (hA : A.IsSymmetricCoercive)
    (hD : D.IsSymmetricCoercive) (hinv : ∀ u, D (Dinv u) = u) {γ : ℝ}
    (hγ : ∀ x, RCLike.re (inner 𝕜 (A x) x) ≤ γ * RCLike.re (inner 𝕜 (D x) x)) (ω : ℝ) :
    IsSmootherWith A (energyNorm Dinv) (1 - (ω : 𝕜) • (Dinv ∘ₗ A)) (ω * (2 - ω * γ)) := by
  intro e
  obtain ⟨z, hz⟩ : ∃ z : E, Dinv (A e) = z := ⟨_, rfl⟩
  have hDz : D z = A e := by rw [← hz]; exact hinv (A e)
  have hSe : (1 - (ω : 𝕜) • (Dinv ∘ₗ A)) e = e - (ω : 𝕜) • z := by rw [← hz]; rfl
  -- the dual seminorm of the residual is the `D`-norm of the correction
  have hqnn : 0 ≤ RCLike.re (inner 𝕜 (Dinv (A e)) (A e)) := by
    rw [hz, ← hDz, ← inner_conj_symm z (D z), RCLike.conj_re]
    exact hD.isPositive.re_inner_nonneg_left z
  have hq : energyNorm Dinv (A e) ^ 2 = RCLike.re (inner 𝕜 (D z) z) := by
    have h : energyNorm Dinv (A e) ^ 2 = RCLike.re (inner 𝕜 (Dinv (A e)) (A e)) :=
      Real.sq_sqrt hqnn
    rw [h, hz, ← hDz, ← inner_conj_symm z (D z), RCLike.conj_re]
  -- expand the energy norm of the smoothed error
  have hexp : energyNorm A (e - (ω : 𝕜) • z) ^ 2
      = energyNorm A e ^ 2 - 2 * ω * RCLike.re (inner 𝕜 (A e) z)
        + ω ^ 2 * RCLike.re (inner 𝕜 (A z) z) := by
    have h1 : energyNorm A (e - (ω : 𝕜) • z)
        = ‖WithEnergy.equiv A hA e - (ω : 𝕜) • WithEnergy.equiv A hA z‖ := by
      rw [← WithEnergy.norm_equiv A hA (e - (ω : 𝕜) • z), map_sub, map_smul]
    have h2 : RCLike.re ((ω : 𝕜) * inner 𝕜 (WithEnergy.equiv A hA e) (WithEnergy.equiv A hA z))
        = ω * RCLike.re (inner 𝕜 (A e) z) := by
      rw [RCLike.re_ofReal_mul, WithEnergy.inner_equiv]
      rfl
    rw [h1, norm_sub_sq (𝕜 := 𝕜), inner_smul_right, h2, norm_smul, RCLike.norm_ofReal, mul_pow,
      sq_abs, WithEnergy.norm_equiv, WithEnergy.norm_equiv, hA.energyNorm_sq, hA.energyNorm_sq]
    ring
  have hAez : RCLike.re (inner 𝕜 (A e) z) = RCLike.re (inner 𝕜 (D z) z) := by rw [hDz]
  have hAzz : RCLike.re (inner 𝕜 (A z) z) ≤ γ * RCLike.re (inner 𝕜 (D z) z) := hγ z
  rw [hSe, hexp, hq, hAez]
  nlinarith [sq_nonneg ω]

end Multigrid
