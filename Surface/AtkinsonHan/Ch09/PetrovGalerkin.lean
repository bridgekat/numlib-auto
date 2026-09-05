import AtkinsonHan.Ch08.GeneralizedLaxMilgram

/-!
# The Petrov–Galerkin method (§9.2)

Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009.

The Petrov–Galerkin problem (9.2.5), the discrete inf–sup constant (9.2.6), Babuška's theorem
(Theorem 9.2.1 with the error bound (9.2.7) and the Galerkin orthogonality (9.2.8)), the
convergence corollary 9.2.3 (with (9.2.11)–(9.2.12)) and the uniform inf–sup condition
(9.2.13)–(9.2.14).

The book's supremum in (9.2.6) is taken without absolute values; `iSup_div_eq_opNorm`
(§8.7) identifies it with the norm of the functional `a(u_N, ·)` restricted to `V_N`, which is the
backbone's `IsPetrovGalerkinSolution.DiscreteInfSup`.

Remark 9.2.2 -- the Xu–Zikatanov sharpening `‖u − u_N‖ ≤ (M/α_N) inf_{w_N} ‖u − w_N‖` -- is
**deferred**: it needs the Petrov–Galerkin projector `P_N : u ↦ u_N` as a bounded idempotent
operator with `‖P_N‖ ≤ M/α_N`, which is a phase-2 item of `tracker/backbone.md` §5.2.3.  Kato's
lemma, the analytic ingredient, is already available and is recorded below as `kato`.
-/

open Filter Topology
open scoped InnerProductSpace

namespace AtkinsonHan

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]

/-- The Petrov–Galerkin problem (9.2.5): `u_N ∈ U_N` with `a(u_N, v_N) = ℓ(v_N)` for all
`v_N ∈ V_N`.  The trial space `U_N ⊂ U` and the test space `V_N ⊂ V` may differ. -/
def PetrovGalerkinProblem (a : BilinForm₂ U V) (ℓ : StrongDual ℝ V) (UN : Submodule ℝ U)
    (VN : Submodule ℝ V) (uN : U) : Prop :=
  uN ∈ UN ∧ ∀ v ∈ VN, a uN v = ℓ v

/-- The discrete inf–sup condition (9.2.6) with constant `α_N`:
`sup_{0 ≠ v_N ∈ V_N} a(u_N, v_N)/‖v_N‖ ≥ α_N ‖u_N‖` for all `u_N ∈ U_N`. -/
def DiscreteInfSup (a : BilinForm₂ U V) (UN : Submodule ℝ U) (VN : Submodule ℝ V) (αN : ℝ) :
    Prop :=
  ∀ uN ∈ UN, αN * ‖uN‖ ≤ ⨆ vN : {v : VN // v ≠ 0}, a uN ((vN : VN) : V) / ‖((vN : VN) : V)‖

/-- The uniform inf–sup (Babuška–Brezzi) condition (9.2.13): the discrete inf–sup condition holds
for every `N` with one and the same constant `α₀`. -/
def InfSupCondition (a : BilinForm₂ U V) (UN : ℕ → Submodule ℝ U) (VN : ℕ → Submodule ℝ V)
    (α₀ : ℝ) : Prop :=
  ∀ N, DiscreteInfSup a (UN N) (VN N) α₀

/-- The quantity `inf_{0 ≠ u_N} sup_{0 ≠ v_N} a(u_N, v_N)/(‖u_N‖ ‖v_N‖)` of (9.2.14). -/
noncomputable def infSupValue (a : BilinForm₂ U V) (UN : Submodule ℝ U) (VN : Submodule ℝ V) :
    ℝ :=
  ⨅ uN : {u : UN // u ≠ 0}, ⨆ vN : {v : VN // v ≠ 0},
    a ((uN : UN) : U) ((vN : VN) : V) / (‖((uN : UN) : U)‖ * ‖((vN : VN) : V)‖)

/-- The discrete inf–sup condition weakens as the constant decreases. -/
theorem DiscreteInfSup.mono {a : BilinForm₂ U V} {UN : Submodule ℝ U} {VN : Submodule ℝ V}
    {αN α₀ : ℝ} (h : DiscreteInfSup a UN VN αN) (hα : α₀ ≤ αN) : DiscreteInfSup a UN VN α₀ :=
  fun w hw => le_trans (mul_le_mul_of_nonneg_right hα (norm_nonneg _)) (h w hw)

/-- (9.2.13): trial/test pairs whose discrete inf–sup constants `α_N` are all at least `α₀`
satisfy the uniform inf–sup condition with that one constant.  This is how the book's varying
`α_N ≥ α₀` reduces to `InfSupCondition`. -/
theorem infSupCondition_of_forall_le {a : BilinForm₂ U V} {UN : ℕ → Submodule ℝ U}
    {VN : ℕ → Submodule ℝ V} {αN : ℕ → ℝ} {α₀ : ℝ}
    (h : ∀ i, DiscreteInfSup a (UN i) (VN i) (αN i)) (hα : ∀ i, α₀ ≤ αN i) :
    InfSupCondition a UN VN α₀ := fun i => (h i).mono (hα i)

namespace Ch09

variable {a : BilinForm₂ U V} {ℓ : StrongDual ℝ V} {M αN α₀ : ℝ} {UN : Submodule ℝ U}
  {VN : Submodule ℝ V} {u uN : U}

/-- The Petrov–Galerkin problem is the backbone's `IsPetrovGalerkinSolution`. -/
theorem petrovGalerkinProblem_iff (hM : a.IsBoundedWith M) :
    PetrovGalerkinProblem a ℓ UN VN uN ↔
      IsPetrovGalerkinSolution (a.toCLM hM) ℓ UN VN uN := Iff.rfl

/-- The book's supremum in (9.2.6) is the norm of the functional `a(u_N, ·)` restricted to
`V_N`. -/
theorem iSup_div_eq_norm_comp (hM : a.IsBoundedWith M) (w : U) (VN : Submodule ℝ V) :
    (⨆ vN : {v : VN // v ≠ 0}, a w ((vN : VN) : V) / ‖((vN : VN) : V)‖)
      = ‖(a.toCLM hM w).comp VN.subtypeL‖ :=
  iSup_div_eq_opNorm ((a.toCLM hM w).comp VN.subtypeL)

/-- (9.2.6) is the backbone's discrete inf–sup condition. -/
theorem discreteInfSup_iff (hM : a.IsBoundedWith M) :
    DiscreteInfSup a UN VN αN ↔
      IsPetrovGalerkinSolution.DiscreteInfSup (a.toCLM hM) UN VN αN := by
  refine forall_congr' fun w => forall_congr' fun _ => ?_
  rw [iSup_div_eq_norm_comp hM w VN]

/-- (9.2.8), Galerkin orthogonality for the Petrov–Galerkin method. -/
theorem petrovGalerkin_orthogonality (hu : ∀ v, a u v = ℓ v)
    (huN : PetrovGalerkinProblem a ℓ UN VN uN) {v : V} (hv : v ∈ VN) : a (u - uN) v = 0 := by
  rw [map_sub, LinearMap.sub_apply, hu v, huN.2 v hv, sub_self]

/-- Theorem 9.2.1 (Babuška), part 1: with `dim U_N = dim V_N` and the discrete inf–sup condition
(9.2.6), the Petrov–Galerkin problem (9.2.5) has a unique solution.  Completeness of `U` and `V`
and the continuous conditions (9.2.3)–(9.2.4) are not used here. -/
theorem thm_9_2_1_existsUnique [FiniteDimensional ℝ UN] [FiniteDimensional ℝ VN]
    (hM : a.IsBoundedWith M) (hdim : Module.finrank ℝ UN = Module.finrank ℝ VN) (hαN : 0 < αN)
    (hinfsup : DiscreteInfSup a UN VN αN) (ℓ : StrongDual ℝ V) :
    ∃! uN, PetrovGalerkinProblem a ℓ UN VN uN :=
  IsPetrovGalerkinSolution.existsUnique (a := a.toCLM hM) (ℓ := ℓ) hdim hαN
    ((discreteInfSup_iff hM).mp hinfsup)

/-- Theorem 9.2.1 (Babuška), estimate (9.2.7), pointwise form:
`‖u − u_N‖ ≤ (1 + M/α_N) ‖u − w_N‖` for every `w_N ∈ U_N`. -/
theorem thm_9_2_1_le [FiniteDimensional ℝ UN] [FiniteDimensional ℝ VN] (hM0 : 0 ≤ M)
    (hM : a.IsBoundedWith M) (hdim : Module.finrank ℝ UN = Module.finrank ℝ VN) (hαN : 0 < αN)
    (hinfsup : DiscreteInfSup a UN VN αN) (huN : PetrovGalerkinProblem a ℓ UN VN uN)
    (hu : ∀ v, a u v = ℓ v) {w : U} (hw : w ∈ UN) :
    ‖u - uN‖ ≤ (1 + M / αN) * ‖u - w‖ :=
  IsPetrovGalerkinSolution.norm_sub_le hdim hαN hM0 (a.isBoundedWith_toCLM hM)
    ((discreteInfSup_iff hM).mp hinfsup) huN hu hw

/-- Theorem 9.2.1 (Babuška): unique solvability of (9.2.5) together with the quasi-optimal error
bound (9.2.7) `‖u − u_N‖_U ≤ (1 + M/α_N) inf_{w_N ∈ U_N} ‖u − w_N‖_U`. -/
theorem thm_9_2_1 [FiniteDimensional ℝ UN] [FiniteDimensional ℝ VN] (hM0 : 0 ≤ M)
    (hM : a.IsBoundedWith M) (hdim : Module.finrank ℝ UN = Module.finrank ℝ VN) (hαN : 0 < αN)
    (hinfsup : DiscreteInfSup a UN VN αN) (ℓ : StrongDual ℝ V) (hu : ∀ v, a u v = ℓ v) :
    (∃! uN, PetrovGalerkinProblem a ℓ UN VN uN) ∧
      ∀ uN, PetrovGalerkinProblem a ℓ UN VN uN →
        ‖u - uN‖ ≤ (1 + M / αN) * ⨅ wN : UN, ‖u - (wN : U)‖ := by
  have hC : 0 < 1 + M / αN := by
    have : 0 ≤ M / αN := div_nonneg hM0 hαN.le
    linarith
  refine ⟨thm_9_2_1_existsUnique hM hdim hαN hinfsup ℓ, fun uN huN => ?_⟩
  have hkey : ∀ w : UN, ‖u - uN‖ / (1 + M / αN) ≤ ‖u - (w : U)‖ := fun w => by
    rw [div_le_iff₀ hC, mul_comm]
    exact thm_9_2_1_le hM0 hM hdim hαN hinfsup huN hu w.2
  have hle := le_ciInf hkey
  rw [div_le_iff₀ hC] at hle
  linarith [hle]

/-- The remark after Corollary 9.2.3: the constant in (9.2.7) is bounded by
`(1 + M) max{1, α_N⁻¹}`, so convergence follows as soon as
`max{1, α_N⁻¹} inf_{w_N} ‖u − w_N‖ → 0`. -/
theorem one_add_div_le (hM0 : 0 ≤ M) :
    1 + M / αN ≤ (1 + M) * max 1 αN⁻¹ := by
  have h1 : (1 : ℝ) ≤ max 1 αN⁻¹ := le_max_left _ _
  have h2 : αN⁻¹ ≤ max 1 αN⁻¹ := le_max_right _ _
  have h3 : M / αN = M * αN⁻¹ := div_eq_mul_inv M αN
  nlinarith

/-- Corollary 9.2.3, (9.2.11)–(9.2.12): under a uniform discrete inf–sup condition and with trial
spaces that increase and have dense union, the Petrov–Galerkin solutions converge. -/
theorem cor_9_2_3 (a : BilinForm₂ U V) (ℓ : StrongDual ℝ V) {M α₀ : ℝ} (hM0 : 0 ≤ M)
    (hM : a.IsBoundedWith M) (hα₀ : 0 < α₀) (UN : ℕ → Submodule ℝ U) (VN : ℕ → Submodule ℝ V)
    [∀ i, FiniteDimensional ℝ (UN i)] [∀ i, FiniteDimensional ℝ (VN i)]
    (hdim : ∀ i, Module.finrank ℝ (UN i) = Module.finrank ℝ (VN i)) (αN : ℕ → ℝ)
    (hαN : ∀ i, α₀ ≤ αN i) (hinfsup : ∀ i, DiscreteInfSup a (UN i) (VN i) (αN i))
    (hmono : Monotone UN) (hdense : Dense (⋃ i, (UN i : Set U))) {u : U}
    (hu : ∀ v, a u v = ℓ v) (uN : ℕ → U)
    (huN : ∀ i, PetrovGalerkinProblem a ℓ (UN i) (VN i) (uN i)) :
    Tendsto (fun i => ‖u - uN i‖) atTop (𝓝 0) := by
  have huniform : InfSupCondition a UN VN α₀ := infSupCondition_of_forall_le hinfsup hαN
  have hunif : ∀ i, IsPetrovGalerkinSolution.DiscreteInfSup (a.toCLM hM) (UN i) (VN i) α₀ :=
    fun i => (discreteInfSup_iff hM).mp (huniform i)
  have h := IsPetrovGalerkinSolution.tendsto (a := a.toCLM hM) (ℓ := ℓ) hdim hα₀ hM0
    (a.isBoundedWith_toCLM hM) hunif hmono hdense huN hu
  rw [tendsto_iff_norm_sub_tendsto_zero] at h
  simpa only [norm_sub_rev] using h

/-! ### (9.2.13) ⇔ (9.2.14) -/

private theorem iSup_div_mul_eq (a : BilinForm₂ U V) (VN : Submodule ℝ V) {w : U}
    (hw : w ≠ 0) :
    (⨆ vN : {v : VN // v ≠ 0}, a w ((vN : VN) : V) / (‖w‖ * ‖((vN : VN) : V)‖))
      = (⨆ vN : {v : VN // v ≠ 0}, a w ((vN : VN) : V) / ‖((vN : VN) : V)‖) / ‖w‖ := by
  have hpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  rw [div_eq_mul_inv, Real.iSup_mul_of_nonneg (by positivity)]
  refine iSup_congr fun v => ?_
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_comm ‖w‖⁻¹, ← mul_assoc]

/-- (9.2.13) ⇔ (9.2.14): the uniform inf–sup condition with constant `α₀` says exactly that the
inf–sup values (9.2.14) of the pairs `(U_N, V_N)` are all at least `α₀`. -/
theorem discreteInfSup_iff_le_infSupValue (hM : a.IsBoundedWith M) (hUN : UN ≠ ⊥) :
    DiscreteInfSup a UN VN α₀ ↔ α₀ ≤ infSupValue a UN VN := by
  have hnn : ∀ w : U, 0 ≤ ⨆ vN : {v : VN // v ≠ 0}, a w ((vN : VN) : V) / ‖((vN : VN) : V)‖ :=
    fun w => by
      rw [iSup_div_eq_norm_comp hM w VN]
      exact norm_nonneg ((a.toCLM hM w).comp VN.subtypeL)
  have hne : Nonempty {x : UN // x ≠ 0} := by
    obtain ⟨w, hw, hw0⟩ := UN.ne_bot_iff.mp hUN
    exact ⟨⟨⟨w, hw⟩, fun h => hw0 (congrArg Subtype.val h)⟩⟩
  have hbdd : BddBelow (Set.range fun uN : {x : UN // x ≠ 0} =>
      ⨆ vN : {v : VN // v ≠ 0}, a ((uN : UN) : U) ((vN : VN) : V) /
        (‖((uN : UN) : U)‖ * ‖((vN : VN) : V)‖)) := by
    refine ⟨0, Set.forall_mem_range.2 fun x => ?_⟩
    have hx : ((x : UN) : U) ≠ 0 := fun h => x.2 (Subtype.ext h)
    rw [iSup_div_mul_eq a VN hx]
    exact div_nonneg (hnn _) (norm_nonneg _)
  rw [infSupValue, le_ciInf_iff hbdd]
  constructor
  · intro h x
    have hx : ((x : UN) : U) ≠ 0 := fun hz => x.2 (Subtype.ext hz)
    rw [iSup_div_mul_eq a VN hx, le_div_iff₀ (norm_pos_iff.mpr hx)]
    exact h _ (x : UN).2
  · intro h w hw
    rcases eq_or_ne w 0 with rfl | hw0
    · simp
    · have hx := h ⟨⟨w, hw⟩, fun hz => hw0 (congrArg Subtype.val hz)⟩
      rw [iSup_div_mul_eq a VN hw0, le_div_iff₀ (norm_pos_iff.mpr hw0)] at hx
      exact hx

/-! ### Kato's lemma -/

/-- The analytic ingredient of Remark 9.2.2: a bounded idempotent `P ≠ 0, 1` on a Hilbert space
satisfies `‖P‖ = ‖I − P‖`. -/
theorem kato {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {P : H →L[ℝ] H} (hP : IsIdempotentElem P) (h0 : P ≠ 0) (h1 : P ≠ 1) : ‖P‖ = ‖1 - P‖ :=
  (ContinuousLinearMap.IsIdempotentElem.norm_one_sub_eq hP h0 h1).symm

end Ch09

end AtkinsonHan
