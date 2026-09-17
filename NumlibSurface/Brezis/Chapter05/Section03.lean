import Numlib.Variational.Inequality.Basic
import Numlib.Variational.LaxMilgram

/-!
# Brezis §5.3: the theorems of Stampacchia and Lax–Milgram

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §5.3, over a real Hilbert space `H`. The book's bilinear
forms `a : H × H → ℝ` are `LinearMap.BilinForm ℝ H` (the `abbrev` `BilinForm H`, so that the
predicates below are found by dot notation, the pattern of `AtkinsonHan.BilinForm`), with
continuity and coercivity as the book's Definition has them; the bridge `BilinForm.toSesqForm`
bundles a continuous form as the backbone's `SesqForm ℝ H` (`Numlib/Variational/Forms`), through
which every theorem delegates: Stampacchia to
`existsUnique_isVariationalInequalitySolution_of_isCoercive` and
`SesqForm.isMinOn_energy_iff_forall_le`, Lax–Milgram to `SesqForm.laxMilgram` and
`SesqForm.isMinOn_energy_iff`, and the Banach fixed-point theorem to Mathlib's `ContractingWith`.

## Main results

* `BilinForm`, `BilinForm.IsContinuousWith`, `BilinForm.IsCoerciveWith` — the Definition, with
  the bridges `BilinForm.toSesqForm`, `toSesqForm_apply`, `isCoerciveWith_toSesqForm`,
  `isHermitian_toSesqForm_of_isSymm`.
* `theorem_5_6`, `theorem_5_6_symm` — Stampacchia's theorem: the variational inequality
  `a(u, v - u) ≥ ⟨φ, v - u⟩ ∀ v ∈ K` has a unique solution, which for symmetric `a` is the
  minimizer of `½ a(v, v) - ⟨φ, v⟩` on `K`.
* `theorem_5_7` — the Banach fixed-point theorem.
* `corollary_5_8`, `corollary_5_8_symm` — the Lax–Milgram theorem and its symmetric clause.
* `remark_5_6`, `remark_5_7`, `remark_5_8` — convexity of `v ↦ a(v, v)` for a nonnegative form
  (no symmetry), the energy's derivative (`(17)` is the Euler equation `F'(u) = 0`), and the
  direct proof of Lax–Milgram through the operator `A`: injective, closed range, dense range.

Theorem 5.16 (Minty–Browder, Comments) is not planned.
-/

open scoped InnerProductSpace

noncomputable section

namespace Brezis.Chapter05

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-! ### The Definition: continuous and coercive bilinear forms -/

/-- The book's bilinear forms `a : H × H → ℝ`: `LinearMap.BilinForm ℝ H`, as an abbreviation so
that the predicates below are found by dot notation. -/
abbrev BilinForm (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :=
  LinearMap.BilinForm ℝ H

namespace BilinForm

omit [CompleteSpace H] in
/-- **Definition (i)**: `a` is continuous with constant `C`, `|a(u, v)| ≤ C |u| |v|` for all
`u, v ∈ H`. -/
def IsContinuousWith (a : BilinForm H) (C : ℝ) : Prop :=
  ∀ u v, |a u v| ≤ C * ‖u‖ * ‖v‖

omit [CompleteSpace H] in
/-- **Definition (ii)**: `a` is coercive with constant `α`, `a(v, v) ≥ α |v|²` for all `v ∈ H`;
the theorems add `0 < α`. -/
def IsCoerciveWith (a : BilinForm H) (α : ℝ) : Prop :=
  ∀ v, α * ‖v‖ ^ 2 ≤ a v v

omit [CompleteSpace H] in
/-- A continuous bilinear form bundled as the backbone's `SesqForm ℝ H`: over `ℝ` a bounded
bilinear map `H →L[ℝ] H →L[ℝ] ℝ` *is* a sesquilinear form. -/
def toSesqForm (a : BilinForm H) {C : ℝ} (hC : a.IsContinuousWith C) : SesqForm ℝ H :=
  LinearMap.mkContinuous₂ a C fun u v => by simpa [Real.norm_eq_abs] using hC u v

omit [CompleteSpace H] in
/-- Bundling does not change the values: `toSesqForm a hC u v = a u v`. -/
@[simp]
theorem toSesqForm_apply (a : BilinForm H) {C : ℝ} (hC : a.IsContinuousWith C) (u v : H) :
    a.toSesqForm hC u v = a u v := rfl

omit [CompleteSpace H] in
/-- The book's coercivity is the backbone's `SesqForm.IsCoerciveWith` of the bundled form. -/
theorem isCoerciveWith_toSesqForm (a : BilinForm H) {C α : ℝ} (hC : a.IsContinuousWith C)
    (hα : a.IsCoerciveWith α) : SesqForm.IsCoerciveWith (a.toSesqForm hC) α := by
  rw [SesqForm.isCoerciveWith_real_iff]
  exact hα

omit [CompleteSpace H] in
/-- The book's "symmetric" (`a(u, v) = a(v, u)`, Mathlib's `LinearMap.BilinForm.IsSymm`) is the
backbone's `SesqForm.IsHermitian` of the bundled form. -/
theorem isHermitian_toSesqForm_of_isSymm (a : BilinForm H) {C : ℝ} (hC : a.IsContinuousWith C)
    (hs : LinearMap.BilinForm.IsSymm a) : (a.toSesqForm hC).IsHermitian := by
  rw [SesqForm.isHermitian_real_iff]
  intro u v
  rw [toSesqForm_apply, toSesqForm_apply]
  exact LinearMap.BilinForm.isSymm_def.1 hs u v

end BilinForm

open BilinForm

/-! ### Stampacchia's theorem -/

/-- **Theorem 5.6 (Stampacchia), existence and uniqueness.** For a continuous coercive bilinear
form `a` on `H`, a nonempty closed convex `K ⊆ H` and `φ ∈ H*`, there is a unique `u ∈ K` with
`a(u, v - u) ≥ ⟨φ, v - u⟩` for all `v ∈ K` (display (10)). The backbone's proof is the book's:
a fixed point of `v ↦ P_K (ρ f - ρ A v + v)` for small `ρ > 0`, `P_K` being nonexpansive. -/
theorem theorem_5_6 {a : BilinForm H} {C α : ℝ} (hC : a.IsContinuousWith C) (hα : 0 < α)
    (ha : a.IsCoerciveWith α) {K : Set H} (hne : K.Nonempty) (hcl : IsClosed K)
    (hK : Convex ℝ K) (φ : StrongDual ℝ H) :
    ∃! u, u ∈ K ∧ ∀ v ∈ K, φ (v - u) ≤ a u (v - u) := by
  have h := existsUnique_isVariationalInequalitySolution_of_isCoercive hα
    (isCoerciveWith_toSesqForm a hC ha) hne hcl hK (convexOn_const 0 hK)
    lowerSemicontinuousOn_const φ
  simpa [IsVariationalInequalitySolution, SesqForm.inner_rieszRep, SesqForm.inner_toOperator,
    toSesqForm_apply] using h

/-- **Theorem 5.6, the symmetric clause.** If moreover `a` is symmetric, then `u` is characterized
by `u ∈ K` and `½ a(u, u) - ⟨φ, u⟩ = min_{v ∈ K} {½ a(v, v) - ⟨φ, v⟩}` (display (11)): the
solutions of (10) in `K` are exactly the minimizers of the energy on `K`, and the minimizer exists
and is unique. The book's proof — `u` is the projection of `g` onto `K` in the scalar product
`a` — is the backbone's `IsVariationalInequalitySolution.isBestApprox_energy`. -/
theorem theorem_5_6_symm {a : BilinForm H} {C α : ℝ} (hC : a.IsContinuousWith C) (hα : 0 < α)
    (ha : a.IsCoerciveWith α) (hs : LinearMap.BilinForm.IsSymm a) {K : Set H}
    (hne : K.Nonempty) (hcl : IsClosed K) (hK : Convex ℝ K) (φ : StrongDual ℝ H) :
    (∀ u, (u ∈ K ∧ ∀ v ∈ K, φ (v - u) ≤ a u (v - u)) ↔
        (u ∈ K ∧ IsMinOn (fun v => 1 / 2 * a v v - φ v) K u)) ∧
      ∃! u, u ∈ K ∧ IsMinOn (fun v => 1 / 2 * a v v - φ v) K u := by
  have hh := isHermitian_toSesqForm_of_isSymm a hC hs
  have hE : (a.toSesqForm hC).energy φ = fun v => 1 / 2 * a v v - φ v := by
    funext v
    simp [SesqForm.energy, toSesqForm_apply]
  refine ⟨fun u => ?_, ?_⟩
  · constructor
    · rintro ⟨hu, h⟩
      refine ⟨hu, ?_⟩
      rw [← hE]
      exact (SesqForm.isMinOn_energy_iff_forall_le hh φ hα (isCoerciveWith_toSesqForm a hC ha) hK
        hu).2 h
    · rintro ⟨hu, h⟩
      refine ⟨hu, ?_⟩
      rw [← hE] at h
      exact (SesqForm.isMinOn_energy_iff_forall_le hh φ hα (isCoerciveWith_toSesqForm a hC ha) hK
        hu).1 h
  · rw [← hE]
    exact SesqForm.existsUnique_isMinOn_energy hh φ hα (isCoerciveWith_toSesqForm a hC ha) hK hcl
      hne

/-- **Theorem 5.7 (Banach fixed-point theorem, the contraction mapping principle).** A strict
contraction `S` of a nonempty complete metric space `X` — `d(S v₁, S v₂) ≤ k d(v₁, v₂)` with
`k < 1` — has a unique fixed point `u = S u`. Mathlib's `ContractingWith`, with the book's real
`k` replaced by `max k 0` (if `k < 0` the hypothesis forces `S` to be constant). -/
theorem theorem_5_7 {X : Type*} [MetricSpace X] [Nonempty X] [CompleteSpace X] (S : X → X)
    {k : ℝ} (hk : k < 1) (hS : ∀ v₁ v₂, dist (S v₁) (S v₂) ≤ k * dist v₁ v₂) :
    ∃! u, S u = u := by
  refine ContractingWith.existsUnique_eq_self (K := Real.toNNReal k) ⟨?_, ?_⟩
  · exact_mod_cast Real.toNNReal_lt_one.2 hk
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    calc dist (S x) (S y) ≤ k * dist x y := hS x y
      _ ≤ Real.toNNReal k * dist x y :=
          mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal k) dist_nonneg

/-! ### The Lax–Milgram theorem -/

/-- **Corollary 5.8 (Lax–Milgram).** For a continuous coercive bilinear form `a` on `H` and
`φ ∈ H*` there is a unique `u ∈ H` with `a(u, v) = ⟨φ, v⟩` for all `v ∈ H` (display (17)). -/
theorem corollary_5_8 {a : BilinForm H} {C α : ℝ} (hC : a.IsContinuousWith C) (hα : 0 < α)
    (ha : a.IsCoerciveWith α) (φ : StrongDual ℝ H) : ∃! u, ∀ v, a u v = φ v :=
  SesqForm.laxMilgram (a.toSesqForm hC) φ hα (isCoerciveWith_toSesqForm a hC ha)

omit [CompleteSpace H] in
/-- **Corollary 5.8, the symmetric clause.** If moreover `a` is symmetric, `u` is characterized by
`½ a(u, u) - ⟨φ, u⟩ = min_{v ∈ H} {½ a(v, v) - ⟨φ, v⟩}` (display (18)). -/
theorem corollary_5_8_symm {a : BilinForm H} {C α : ℝ} (hC : a.IsContinuousWith C) (hα : 0 < α)
    (ha : a.IsCoerciveWith α) (hs : LinearMap.BilinForm.IsSymm a) (φ : StrongDual ℝ H) (u : H) :
    (∀ v, a u v = φ v) ↔ IsMinOn (fun v => 1 / 2 * a v v - φ v) Set.univ u := by
  have hE : (a.toSesqForm hC).energy φ = fun v => 1 / 2 * a v v - φ v := by
    funext v
    simp [SesqForm.energy, toSesqForm_apply]
  have h := SesqForm.isMinOn_energy_iff φ (isHermitian_toSesqForm_of_isSymm a hC hs) hα
    (isCoerciveWith_toSesqForm a hC ha) ⊤ (Submodule.mem_top (x := u))
  rw [hE, Submodule.top_coe] at h
  rw [h]
  simp only [Submodule.mem_top, true_implies, toSesqForm_apply]

/-! ### Remarks 6–8 -/

omit [CompleteSpace H] in
/-- **Remark 6.** If `a(v, v) ≥ 0` for all `v` then `v ↦ a(v, v)` is convex — no symmetry and no
continuity is needed: for `s + t = 1`,
`a(s u + t v, s u + t v) = s a(u, u) + t a(v, v) - s t a(u - v, u - v)`. -/
theorem remark_5_6 (a : BilinForm H) (hpos : ∀ v, 0 ≤ a v v) :
    ConvexOn ℝ Set.univ fun v => a v v := by
  refine ⟨convex_univ, fun x _ y _ s t hs ht hst => ?_⟩
  have hsub : a (x - y) (x - y) = a x x - (a x y + a y x) + a y y := by
    simp only [map_sub, LinearMap.sub_apply]
    ring
  have h := hpos (x - y)
  rw [hsub] at h
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  obtain rfl : t = 1 - s := by linarith
  nlinarith [mul_nonneg (mul_nonneg hs ht) h]

omit [CompleteSpace H] in
/-- **Remark 7.** The precise content of "(17) says `F'(u) = 0` where
`F(v) = ½ a(v, v) - ⟨φ, v⟩`": for a symmetric continuous `a`, `F` is Fréchet differentiable at
every `u` with derivative the functional `v ↦ a(u, v) - ⟨φ, v⟩`, and (17) holds at `u` exactly
when `F'(u) = 0` — (17) is the Euler equation of the minimization problem (18). -/
theorem remark_5_7 {a : BilinForm H} {C : ℝ} (hC : a.IsContinuousWith C)
    (hs : LinearMap.BilinForm.IsSymm a) (φ : StrongDual ℝ H) (u : H) :
    HasFDerivAt (fun v => 1 / 2 * a v v - φ v) (a.toSesqForm hC u - φ) u ∧
      ((∀ v, a u v = φ v) ↔ fderiv ℝ (fun v => 1 / 2 * a v v - φ v) u = 0) := by
  have hE : (a.toSesqForm hC).energy φ = fun v => 1 / 2 * a v v - φ v := by
    funext v
    simp [SesqForm.energy, toSesqForm_apply]
  have hd := SesqForm.hasFDerivAt_energy (isHermitian_toSesqForm_of_isSymm a hC hs) φ u
  rw [hE] at hd
  refine ⟨hd, ?_⟩
  rw [hd.fderiv, sub_eq_zero]
  constructor
  · intro h
    ext v
    exact h v
  · intro h v
    exact congrArg (fun ψ : StrongDual ℝ H => ψ v) h

/-- **Remark 8, the direct proof of Lax–Milgram.** With `A : H → H` the operator of (13),
`(A u, v) = a(u, v)` (the backbone's `SesqForm.toOperator`), (a) `A` is injective, since `a` is
coercive; (b) `R(A)` is closed, since `α |v| ≤ |A v|`; (c) `R(A)` is dense, since `(A u, v) = 0`
for all `u` forces `v = 0`; hence `A` is a bijection of `H` onto `H`, which is (17). -/
theorem remark_5_8 {a : BilinForm H} {C α : ℝ} (hC : a.IsContinuousWith C) (hα : 0 < α)
    (ha : a.IsCoerciveWith α) :
    Function.Injective (a.toSesqForm hC).toOperator ∧
      IsClosed (Set.range (a.toSesqForm hC).toOperator) ∧
      Dense (Set.range (a.toSesqForm hC).toOperator) ∧
      Function.Bijective (a.toSesqForm hC).toOperator := by
  have hcoer : ((a.toSesqForm hC).toOperator : H →ₗ[ℝ] H).IsCoerciveWith α :=
    (SesqForm.isCoerciveWith_iff_toOperator _ α).1 (isCoerciveWith_toSesqForm a hC ha)
  have hle : ∀ v, α * ‖v‖ ≤ ‖(a.toSesqForm hC).toOperator v‖ := hcoer.norm_le_norm_apply
  have hrange : Set.range (a.toSesqForm hC).toOperator =
      (LinearMap.range ((a.toSesqForm hC).toOperator : H →ₗ[ℝ] H) : Set H) := by
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
  have horth : (LinearMap.range ((a.toSesqForm hC).toOperator : H →ₗ[ℝ] H))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hz : ⟪(a.toSesqForm hC).toOperator v, v⟫_ℝ = 0 := hv _ ⟨v, rfl⟩
    rw [SesqForm.inner_toOperator, toSesqForm_apply] at hz
    have h1 : α * ‖v‖ ^ 2 ≤ 0 := (ha v).trans_eq hz
    have h2 : ‖v‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖v‖]
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h2 (sq_nonneg _)))
  refine ⟨LinearMap.IsCoercive.injective ⟨α, hα, hcoer⟩, ?_, ?_, ?_⟩
  · rw [hrange]
    exact ContinuousLinearMap.isClosed_range_of_le_norm _ hα hle
  · rw [hrange, Submodule.dense_iff_topologicalClosure_eq_top,
      Submodule.topologicalClosure_eq_top_iff]
    exact horth
  · exact ContinuousLinearMap.bijective_of_le_norm_of_orthogonal_range_eq_bot _ hα hle horth

end Brezis.Chapter05

end
