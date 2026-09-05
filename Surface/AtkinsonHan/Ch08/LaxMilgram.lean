import AtkinsonHan.Ch08.BilinearForms

/-!
# The Lax–Milgram lemma (§8.3)

Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009.

Theorem 8.3.2 (minimization of `E(v) = ½‖v‖² − ℓ(v)` over a nonempty closed convex set),
Theorem 8.3.3 (the same for the energy `E(v) = ½ a(v,v) − ℓ(v)` of a symmetric `V`-elliptic form,
with the variational inequality (8.3.3) and the variational equation (8.3.4)), and Theorem 8.3.4
(Lax–Milgram) with the stability estimate `‖u‖ ≤ ‖ℓ‖/α`.  Both proofs the book gives for
Theorem 8.3.4 are available: the damped fixed-point iteration `P_θ` of the first proof
(`contractingWith_damped_sub_smul`) and the closed-range argument of the second
(`isClosed_range_toOperator`, `bijective_toOperator`).  Exercise 8.3.1 rederives it from the
strongly monotone Lipschitz theory of §5.1.
-/

open Filter Topology
open scoped InnerProductSpace

namespace AtkinsonHan.Ch08

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `u ∈ K` minimizes `f` on `K` iff `f u` is the infimum of `f` over `K`: the passage between
the book's `E(u) = inf_K E` and Mathlib's `IsMinOn`. -/
theorem isMinOn_iff_eq_ciInf {X : Type*} {K : Set X} {f : X → ℝ} {u : X} (hu : u ∈ K)
    (hbdd : BddBelow (Set.range fun v : K => f v)) :
    IsMinOn f K u ↔ f u = ⨅ v : K, f v := by
  have : Nonempty K := ⟨⟨u, hu⟩⟩
  rw [isMinOn_iff]
  constructor
  · intro h
    exact le_antisymm (le_ciInf fun v => h (v : X) v.2) (ciInf_le hbdd ⟨u, hu⟩)
  · intro h v hv
    rw [h]
    exact ciInf_le hbdd ⟨v, hv⟩

/-! ### Theorem 8.3.2: the energy `E(v) = ½‖v‖² − ℓ(v)` -/

theorem energy_innerSL (ℓ : StrongDual ℝ V) (v : V) :
    SesqForm.energy (innerSL ℝ : SesqForm ℝ V) ℓ v = (1 / 2 : ℝ) * ‖v‖ ^ 2 - ℓ v := by
  simp [SesqForm.energy]

private theorem energy_innerSL_eq (ℓ : StrongDual ℝ V) :
    (fun v => (1 / 2 : ℝ) * ‖v‖ ^ 2 - ℓ v) = SesqForm.energy (innerSL ℝ : SesqForm ℝ V) ℓ := by
  funext v
  rw [energy_innerSL]

private theorem innerSL_hermitian : SesqForm.IsHermitian (innerSL ℝ : SesqForm ℝ V) :=
  SesqForm.innerSL_isHermitian

private theorem innerSL_coercive : SesqForm.IsCoerciveWith (innerSL ℝ : SesqForm ℝ V) 1 :=
  SesqForm.innerSL_isCoerciveWith

/-- Theorem 8.3.2: on a nonempty closed convex subset `K` of a Hilbert space the functional
`E(v) = ½‖v‖² − ℓ(v)` has a unique minimizer, and `u ∈ K` is that minimizer exactly when it
satisfies the variational inequality `(u, v − u) ≥ ℓ(v − u)` for all `v ∈ K`. -/
theorem thm_8_3_2 [CompleteSpace V] {K : Set V} (hne : K.Nonempty) (hcl : IsClosed K)
    (hconv : Convex ℝ K) (ℓ : StrongDual ℝ V) :
    (∃! u, u ∈ K ∧ IsMinOn (fun v => (1 / 2 : ℝ) * ‖v‖ ^ 2 - ℓ v) K u) ∧
      ∀ u ∈ K, (IsMinOn (fun v => (1 / 2 : ℝ) * ‖v‖ ^ 2 - ℓ v) K u ↔
        ∀ v ∈ K, ℓ (v - u) ≤ ⟪u, v - u⟫_ℝ) := by
  rw [energy_innerSL_eq]
  refine ⟨SesqForm.existsUnique_isMinOn_energy (innerSL_hermitian (V := V)) ℓ
      one_pos innerSL_coercive hconv hcl hne, fun u hu => ?_⟩
  exact SesqForm.isMinOn_energy_iff_forall_le (innerSL_hermitian (V := V)) ℓ
    one_pos innerSL_coercive hconv hu

/-- Theorem 8.3.2, subspace case: `u ∈ K` minimizes `E(v) = ½‖v‖² − ℓ(v)` over the subspace `K`
iff `(u, v) = ℓ(v)` for all `v ∈ K`. -/
theorem thm_8_3_2_subspace [CompleteSpace V] (K : Submodule ℝ V) (ℓ : StrongDual ℝ V) {u : V}
    (hu : u ∈ K) :
    IsMinOn (fun v => (1 / 2 : ℝ) * ‖v‖ ^ 2 - ℓ v) (K : Set V) u ↔ ∀ v ∈ K, ⟪u, v⟫_ℝ = ℓ v := by
  rw [energy_innerSL_eq]
  exact SesqForm.isMinOn_energy_iff ℓ innerSL_hermitian one_pos innerSL_coercive K hu

/-! ### Theorem 8.3.3: the energy of a symmetric `V`-elliptic form -/

variable {a : BilinForm V} {M α : ℝ}

/-- Theorem 8.3.3, existence and uniqueness: the energy `E(v) = ½ a(v,v) − ℓ(v)` of a bounded,
symmetric, `V`-elliptic form has a unique minimizer on any nonempty closed convex set. -/
theorem thm_8_3_3 [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V)
    {K : Set V} (hne : K.Nonempty) (hcl : IsClosed K) (hconv : Convex ℝ K) :
    ∃! u, u ∈ K ∧ IsMinOn (a.energy ℓ) K u := by
  have hh := (BilinForm.isSymm_iff_isHermitian hM).mp hs
  exact SesqForm.existsUnique_isMinOn_energy (a := a.toCLM hM) hh ℓ hα ha hconv hcl hne

/-- Theorem 8.3.3, characterization (8.3.3): on a convex set the minimizer of the energy is the
solution of the variational inequality `a(u, v − u) ≥ ℓ(v − u)` for all `v ∈ K`. -/
theorem thm_8_3_3_iff [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V)
    {K : Set V} (hconv : Convex ℝ K) {u : V} (hu : u ∈ K) :
    IsMinOn (a.energy ℓ) K u ↔ ∀ v ∈ K, ℓ (v - u) ≤ a u (v - u) := by
  have hh := (BilinForm.isSymm_iff_isHermitian hM).mp hs
  exact SesqForm.isMinOn_energy_iff_forall_le (a := a.toCLM hM) hh ℓ hα ha hconv hu

/-- Theorem 8.3.3, characterization (8.3.4): on a subspace the minimizer of the energy is the
solution of the variational equation `a(u,v) = ℓ(v)` for all `v ∈ K`.  Neither closedness of `K`
nor finite dimension is needed. -/
theorem thm_8_3_3_subspace [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V)
    (K : Submodule ℝ V) {u : V} (hu : u ∈ K) :
    IsMinOn (a.energy ℓ) (K : Set V) u ↔ ∀ v ∈ K, a u v = ℓ v := by
  have hh := (BilinForm.isSymm_iff_isHermitian hM).mp hs
  exact SesqForm.isMinOn_energy_iff ℓ hh hα ha K hu

/-- The energy identity at the solution: `E(v) − E(u) = ½ ‖v − u‖_a²` (the computation inside the
proof of Theorem 8.3.3, and (9.1.9)). -/
theorem energy_sub_energy_eq [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V) {u : V}
    (hu : ∀ v, a u v = ℓ v) (v : V) :
    a.energy ℓ v - a.energy ℓ u = (1 / 2 : ℝ) * a.energyNorm (v - u) ^ 2 := by
  have hh := (BilinForm.isSymm_iff_isHermitian hM).mp hs
  have hpos : SesqForm.IsCoerciveWith (a.toCLM hM) 0 :=
    SesqForm.IsCoerciveWith.mono (a.toCLM hM) ha hα.le
  exact SesqForm.energy_sub_energy_eq ℓ hh hpos hu v

/-! ### Theorem 8.3.4: the Lax–Milgram lemma -/

/-- Theorem 8.3.4 (Lax–Milgram): a bounded `V`-elliptic bilinear form on a Hilbert space makes
the variational problem (8.3.5) `a(u,v) = ℓ(v) ∀ v ∈ V` uniquely solvable. -/
theorem thm_8_3_4 [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) : ∃! u, ∀ v, a u v = ℓ v :=
  SesqForm.laxMilgram (a.toCLM hM) ℓ hα ha

/-- The stability estimate `‖u‖ ≤ ‖ℓ‖ / α` accompanying Theorem 8.3.4; it is the one-space case
of (8.7.5). -/
theorem thm_8_3_4_norm_le [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) {u : V} (hu : ∀ v, a u v = ℓ v) :
    ‖u‖ ≤ ‖ℓ‖ / α :=
  SesqForm.norm_le_of_forall_apply_eq (a.toCLM hM) ℓ hα ha hu

/-- The solution depends Lipschitz-continuously on the data, with constant `1/α`. -/
theorem thm_8_3_4_norm_sub_le [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) {ℓ₁ ℓ₂ : StrongDual ℝ V} {u₁ u₂ : V} (h₁ : ∀ v, a u₁ v = ℓ₁ v)
    (h₂ : ∀ v, a u₂ v = ℓ₂ v) : ‖u₁ - u₂‖ ≤ ‖ℓ₁ - ℓ₂‖ / α :=
  SesqForm.norm_sub_le_of_forall_apply_eq (a.toCLM hM) hα ha h₁ h₂

/-! ### First proof of Theorem 8.3.4: the damped iteration `P_θ` -/

/-- The estimate `‖(I − θ𝒥A)w‖² ≤ (1 − 2θα + θ²M²)‖w‖²` behind the first proof of
Theorem 8.3.4. -/
theorem norm_sub_smul_toOperator_sq_le [CompleteSpace V] (hM0 : 0 ≤ M) (hM : a.IsBoundedWith M)
    (ha : a.IsEllipticWith α) {θ : ℝ} (hθ : 0 ≤ θ) (w : V) :
    ‖w - θ • BilinForm.toOperator a hM w‖ ^ 2 ≤ (1 - 2 * θ * α + θ ^ 2 * M ^ 2) * ‖w‖ ^ 2 := by
  have hcoer := BilinForm.isCoerciveWith_toOperator hM ha
  have hbase := ContinuousLinearMap.norm_sub_smul_apply_sq_le (𝕜 := ℝ) hcoer hθ w
  refine hbase.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
  have hA : ‖BilinForm.toOperator a hM‖ ≤ M := BilinForm.norm_toOperator_le hM0 hM
  have hA0 : 0 ≤ ‖BilinForm.toOperator a hM‖ := norm_nonneg _
  have hsq : ‖BilinForm.toOperator a hM‖ ^ 2 ≤ M ^ 2 := by nlinarith
  nlinarith [sq_nonneg θ, hsq]

/-- The operator `A = 𝒥 a` of a `V`-elliptic form is strongly monotone (5.1.8) with the same
constant, which is what the §5.1 theory (`zarantonello`, `contractingWith_damped`) asks for. -/
theorem stronglyMonotone_toOperator [CompleteSpace V] (hM : a.IsBoundedWith M)
    (ha : a.IsEllipticWith α) (x y : V) :
    α * ‖x - y‖ ^ 2 ≤ RCLike.re (inner ℝ
      (BilinForm.toOperator a hM x - BilinForm.toOperator a hM y) (x - y)) := by
  rw [← map_sub]
  exact BilinForm.isCoerciveWith_toOperator hM ha (x - y)

/-- The operator of a bounded form is Lipschitz with the constant of (9.4.3). -/
theorem lipschitzWith_toOperator [CompleteSpace V] (hM0 : 0 ≤ M) (hM : a.IsBoundedWith M) :
    LipschitzWith (Real.toNNReal M) (BilinForm.toOperator a hM) := by
  refine (BilinForm.toOperator a hM).lipschitzWith.weaken ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal M hM0]
  exact BilinForm.norm_toOperator_le hM0 hM

/-- The map `P_θ u = u − θ (A u − f)` of the first proof of Theorem 8.3.4 is a contraction for
`0 < θ < 2α/M²`, so Banach's fixed point theorem produces the solution of (8.3.5). -/
theorem contractingWith_damped_sub_smul [CompleteSpace V] (hM0 : 0 < M) (hM : a.IsBoundedWith M)
    (hα : 0 < α) (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ < 2 * α / M ^ 2) :
    ContractingWith (Real.toNNReal (Real.sqrt (1 - 2 * θ * α + θ ^ 2 * M ^ 2)))
      (fun u => u - θ • (BilinForm.toOperator a hM u - SesqForm.rieszRep ℓ)) :=
  contractingWith_damped (𝕜 := ℝ) hα hM0 (stronglyMonotone_toOperator hM ha)
    (lipschitzWith_toOperator hM0.le hM) (SesqForm.rieszRep ℓ) hθ hθ'

/-! ### Second proof of Theorem 8.3.4: closed range plus dense range -/

/-- `α ‖u‖ ≤ ‖A u‖` for the operator `A = 𝒥 a` of a `V`-elliptic form: the stability estimate
(8.2.2) that drives the second proof of Theorem 8.3.4. -/
theorem norm_le_norm_toOperator [CompleteSpace V] (hM : a.IsBoundedWith M)
    (ha : a.IsEllipticWith α) (u : V) : α * ‖u‖ ≤ ‖BilinForm.toOperator a hM u‖ := by
  rw [SesqForm.toOperator_apply_eq_rieszRep, SesqForm.norm_rieszRep]
  exact SesqForm.IsCoerciveWith.norm_le_norm_apply (a.toCLM hM) ha u

theorem isClosed_range_toOperator [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) :
    IsClosed (LinearMap.range (BilinForm.toOperator a hM : V →ₗ[ℝ] V) : Set V) :=
  ContinuousLinearMap.isClosed_range_of_le_norm _ hα (norm_le_norm_toOperator hM ha)

theorem orthogonal_range_toOperator [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) :
    (LinearMap.range (BilinForm.toOperator a hM : V →ₗ[ℝ] V))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hz : ⟪BilinForm.toOperator a hM v, v⟫_ℝ = 0 := hv _ ⟨v, rfl⟩
  rw [BilinForm.inner_toOperator] at hz
  have h1 : α * ‖v‖ ^ 2 ≤ 0 := (ha v).trans_eq hz
  have h2 : ‖v‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖v‖]
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h2 (sq_nonneg _)))

/-- The second proof of Theorem 8.3.4: the operator `A = 𝒥 a` is bounded below, hence has closed
range, and its range is dense, hence `A` is a bijection of `V` (Theorem 8.2.1). -/
theorem bijective_toOperator [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) : Function.Bijective (BilinForm.toOperator a hM) :=
  ContinuousLinearMap.bijective_of_le_norm_of_orthogonal_range_eq_bot _ hα
    (norm_le_norm_toOperator hM ha) (orthogonal_range_toOperator hM hα ha)

/-! ### Exercise 8.3.1 -/

/-- Exercise 8.3.1: Lax–Milgram follows from the theory of strongly monotone Lipschitz operators
of §5.1 (the backbone's `zarantonello`), applied to `T = A` with `c₁ = α`, `c₂ = M` and `b = f`
the Riesz representative of `ℓ`. -/
theorem ex_8_3_1 [CompleteSpace V] (hM0 : 0 ≤ M) (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) : ∃! u, ∀ v, a u v = ℓ v := by
  obtain ⟨u, hu, huniq⟩ := zarantonello (𝕜 := ℝ) hα (stronglyMonotone_toOperator hM ha)
    (lipschitzWith_toOperator hM0 hM) (SesqForm.rieszRep ℓ)
  refine ⟨u, (BilinForm.toOperator_eq_rieszRep_iff hM ℓ u).mp hu, fun y hy => ?_⟩
  exact huniq y ((BilinForm.toOperator_eq_rieszRep_iff hM ℓ y).mpr hy)

end AtkinsonHan.Ch08
