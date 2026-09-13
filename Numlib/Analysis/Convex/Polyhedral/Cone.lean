import Numlib.Analysis.Convex.Duality.Polar

/-!
# Polyhedral convex cones and the Minkowski–Weyl theorem

A convex cone can be described in two ways: *from outside*, as the solution set of finitely many
homogeneous linear inequalities (`PolyhedralCone`, an H-cone), or *from inside*, as the set of
nonnegative combinations of finitely many vectors (`FinitelyGeneratedCone`, a V-cone). In finite
dimensions the two descriptions are equivalent — the Minkowski–Weyl theorem, the foundation of the
rest of the polyhedral theory. Mathlib has the two predicates for pointed cones
(`PointedCone.DualFG` and `PointedCone.FG`) but not the equivalence.

## Main results

* `FinitelyGeneratedCone.polyhedralCone` — Weyl's half, V ⇒ H, by Fourier–Motzkin elimination.
  Purely algebraic: no topology, only `FiniteDimensional`.
* `PolyhedralCone.isClosed`, `FinitelyGeneratedCone.isClosed` — a corollary of Weyl's half, and
  the reason Weyl is proved first.
* `PolyhedralCone.finitelyGeneratedCone` — Minkowski's half, H ⇒ V, by separation in the dual.
* `polyhedralCone_iff_finitelyGeneratedCone` — the **Minkowski–Weyl theorem** for cones
  (Theorem 19.1 in [^1]).

## Implementation notes

Fourier–Motzkin is run once, for Weyl's half, in the form "adding a ray to a polyhedral cone
leaves it polyhedral" (`PolyhedralCone.add_ray`); closedness of a finitely generated cone is then
free, and Carathéodory is not needed. Minkowski's half pairs `E` with `Module.Dual ℝ E` directly
and uses only `geometric_hahn_banach_closed_point`, which keeps the statement free of a pairing
parameter. `add_ray` is stated with a difference, `{x | ∃ t ≥ 0, x - t • v ∈ K}`, rather than the
equal `K + {t • v | t ≥ 0}`, because that is the form the elimination proof manipulates.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §19.
-/

open Set

namespace ConvexAnalysis

/-! ### Homogeneous half-spaces cut out by linear functionals -/

section HalfSpace

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- The homogeneous half-space `{m | θ m ≤ 0}` of a *linear* functional, bundled as a pointed cone.

`Separation.lean`'s `halfSpaceCone` is the same construction for a *continuous* functional; the
algebraic version is what Weyl's half of Minkowski–Weyl needs, since that half uses no topology. -/
def halfSpaceConeₗ (θ : M →ₗ[ℝ] ℝ) : PointedCone ℝ M where
  carrier := {m | θ m ≤ 0}
  add_mem' {m m'} hm hm' := by
    have hm₁ : θ m ≤ 0 := hm
    have hm₂ : θ m' ≤ 0 := hm'
    change θ (m + m') ≤ 0
    rw [map_add]
    linarith
  zero_mem' := by
    change θ 0 ≤ 0
    simp
  smul_mem' a {m} hm := by
    have hm' : θ m ≤ 0 := hm
    have ha : (0 : ℝ) ≤ (a : ℝ) := a.2
    change θ ((a : ℝ) • m) ≤ 0
    rw [map_smul, smul_eq_mul]
    nlinarith

@[simp]
theorem mem_halfSpaceConeₗ {θ : M →ₗ[ℝ] ℝ} {m : M} : m ∈ halfSpaceConeₗ θ ↔ θ m ≤ 0 := Iff.rfl

/-- A linear functional nonpositive on a set is nonpositive on the convex cone it generates.

This is the workhorse of the file: both halves of Minkowski–Weyl use it, once in `E` and once in
the dual of `E`, which is why it is stated for an arbitrary module. -/
theorem forall_nonpos_of_mem_hull {θ : M →ₗ[ℝ] ℝ} {S : Set M} (h : ∀ m ∈ S, θ m ≤ 0) {m : M}
    (hm : m ∈ PointedCone.hull ℝ S) : θ m ≤ 0 := by
  have hsub : S ⊆ (halfSpaceConeₗ θ : Set M) := fun m' hm' => h m' hm'
  have hle : PointedCone.hull ℝ S ≤ halfSpaceConeₗ θ := Submodule.span_le.2 hsub
  exact hle hm

end HalfSpace

/-! ### The two descriptions of a cone -/

section Defs

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A **polyhedral convex cone**: the solution set of finitely many homogeneous linear
inequalities. Rockafellar's "polyhedral convex cone", and the H-cone of the linear-programming
literature. -/
def PolyhedralCone (K : Set E) : Prop :=
  ∃ s : Finset (E →ₗ[ℝ] ℝ), K = {x | ∀ φ ∈ s, φ x ≤ 0}

/-- A **finitely generated convex cone**: the set of nonnegative combinations of finitely many
vectors. The V-cone of the linear-programming literature. -/
def FinitelyGeneratedCone (K : Set E) : Prop :=
  ∃ s : Finset E, K = (PointedCone.hull ℝ (s : Set E) : Set E)

theorem PolyhedralCone.convex {K : Set E} (hK : PolyhedralCone K) : Convex ℝ K := by
  obtain ⟨s, rfl⟩ := hK
  intro x hx y hy a b ha hb _ φ hφ
  have h₁ : φ x ≤ 0 := hx φ hφ
  have h₂ : φ y ≤ 0 := hy φ hφ
  have : φ (a • x + b • y) = a * φ x + b * φ y := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [this]
  nlinarith

theorem PolyhedralCone.zero_mem {K : Set E} (hK : PolyhedralCone K) : (0 : E) ∈ K := by
  obtain ⟨s, rfl⟩ := hK
  intro φ _
  simp

theorem PolyhedralCone.smul_mem {K : Set E} (hK : PolyhedralCone K) {a : ℝ} (ha : 0 ≤ a) {x : E}
    (hx : x ∈ K) : a • x ∈ K := by
  obtain ⟨s, rfl⟩ := hK
  intro φ hφ
  have h : φ x ≤ 0 := hx φ hφ
  rw [map_smul, smul_eq_mul]
  nlinarith

theorem FinitelyGeneratedCone.convex {K : Set E} (hK : FinitelyGeneratedCone K) : Convex ℝ K := by
  obtain ⟨s, rfl⟩ := hK
  exact ((PointedCone.hull ℝ (s : Set E) : ConvexCone ℝ E)).convex

theorem FinitelyGeneratedCone.zero_mem {K : Set E} (hK : FinitelyGeneratedCone K) :
    (0 : E) ∈ K := by
  obtain ⟨s, rfl⟩ := hK
  exact (PointedCone.hull ℝ (s : Set E)).zero_mem

theorem FinitelyGeneratedCone.smul_mem {K : Set E} (hK : FinitelyGeneratedCone K) {a : ℝ}
    (ha : 0 ≤ a) {x : E} (hx : x ∈ K) : a • x ∈ K := by
  obtain ⟨s, rfl⟩ := hK
  have h := Submodule.smul_mem (PointedCone.hull ℝ (s : Set E)) (⟨a, ha⟩ : {c : ℝ // 0 ≤ c}) hx
  exact h

end Defs

/-! ### Weyl's half: a finitely generated cone is polyhedral -/

section Weyl

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Adjoining a generator to a cone hull adds a ray to it. -/
theorem coe_hull_insert (v : E) (S : Set E) :
    (PointedCone.hull ℝ (insert v S) : Set E)
      = {x | ∃ t : ℝ, 0 ≤ t ∧ x - t • v ∈ (PointedCone.hull ℝ S : Set E)} := by
  rw [PointedCone.hull, Submodule.span_insert, Submodule.coe_sup]
  ext x
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
    exact ⟨(a : ℝ), a.2, by simpa using hz⟩
  · rintro ⟨t, ht, hmem⟩
    refine ⟨t • v, Submodule.mem_span_singleton.2 ⟨⟨t, ht⟩, rfl⟩, x - t • v, hmem, by simp⟩

/-- **Fourier–Motzkin elimination.** Adding a ray to a polyhedral cone leaves it polyhedral.

The inequalities of the new cone are those old inequalities `φ` with `φ v ≤ 0`, kept unchanged,
together with one combination `(ψ v) • χ - (χ v) • ψ` for each pair with `ψ v > 0` and `χ v < 0`:
those are exactly the consequences of the old system that do not mention the eliminated
variable. -/
theorem PolyhedralCone.add_ray {K : Set E} (hK : PolyhedralCone K) (v : E) :
    PolyhedralCone {x | ∃ t : ℝ, 0 ≤ t ∧ x - t • v ∈ K} := by
  classical
  obtain ⟨s, rfl⟩ := hK
  refine ⟨s.filter (fun φ => φ v ≤ 0) ∪
    Finset.image₂ (fun ψ χ => ψ v • χ - χ v • ψ) (s.filter (fun φ => 0 < φ v))
      (s.filter (fun φ => φ v < 0)), ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Finset.mem_union, Finset.mem_filter, Finset.mem_image₂]
  constructor
  · rintro ⟨t, ht0, hmem⟩ χ hχ
    rcases hχ with ⟨hχs, hχv⟩ | ⟨ψ, ⟨hψs, hψv⟩, χ', ⟨hχ's, hχ'v⟩, rfl⟩
    · have h := hmem χ hχs
      rw [map_sub, map_smul, smul_eq_mul] at h
      nlinarith
    · have h₁ := hmem ψ hψs
      have h₂ := hmem χ' hχ's
      rw [map_sub, map_smul, smul_eq_mul] at h₁ h₂
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      nlinarith
  · intro h
    have hZ : ∀ φ ∈ s, φ v ≤ 0 → φ x ≤ 0 := fun φ hφ hφv => h φ (Or.inl ⟨hφ, hφv⟩)
    have hPN : ∀ ψ ∈ s, 0 < ψ v → ∀ χ ∈ s, χ v < 0 → ψ v * χ x - χ v * ψ x ≤ 0 := by
      intro ψ hψ hψv χ hχ hχv
      have hcomb := h _ (Or.inr ⟨ψ, ⟨hψ, hψv⟩, χ, ⟨hχ, hχv⟩, rfl⟩)
      simpa only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] using hcomb
    set T : Finset ℝ :=
      insert 0 ((s.filter (fun φ => 0 < φ v)).image (fun φ => φ x / φ v)) with hT
    have hTne : T.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
    -- the witness is the largest of `0` and the lower bounds forced by the `φ v > 0` rows; being
    -- a `max'` it is one of them, which is what the `φ v < 0` rows are checked against
    have hmaxcase : T.max' hTne = 0 ∨
        ∃ ψ ∈ s, 0 < ψ v ∧ ψ x / ψ v = T.max' hTne := by
      rcases Finset.mem_insert.1 (T.max'_mem hTne) with hzero | hmem
      · exact Or.inl hzero
      · obtain ⟨ψ, hψ, hψeq⟩ := Finset.mem_image.1 hmem
        obtain ⟨hψs, hψv⟩ := Finset.mem_filter.1 hψ
        exact Or.inr ⟨ψ, hψs, hψv, hψeq⟩
    refine ⟨T.max' hTne, Finset.le_max' _ _ (Finset.mem_insert_self _ _), ?_⟩
    intro φ hφ
    rw [map_sub, map_smul, smul_eq_mul]
    rcases lt_trichotomy (φ v) 0 with hφv | hφv | hφv
    · have hφx : φ x ≤ 0 := hZ φ hφ hφv.le
      rcases hmaxcase with hzero | ⟨ψ, hψs, hψv, hψeq⟩
      · rw [hzero]
        linarith
      · have key := hPN ψ hψs hψv φ hφ hφv
        rw [← hψeq, div_mul_eq_mul_div, sub_nonpos, le_div_iff₀ hψv]
        linarith
    · rw [hφv]
      have := hZ φ hφ hφv.le
      linarith
    · have hmem : φ x / φ v ∈ T :=
        Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨φ, Finset.mem_filter.2 ⟨hφ, hφv⟩, rfl⟩)
      have hle := Finset.le_max' T _ hmem
      rw [div_le_iff₀ hφv] at hle
      linarith

/-- In a finite-dimensional space the origin is a polyhedral cone: it is cut out by the `2 n`
inequalities `± bᵢ* x ≤ 0` for a basis `b`. This is the base of the induction in Weyl's half, and
the only place finite-dimensionality enters it. -/
theorem polyhedralCone_zero [FiniteDimensional ℝ E] : PolyhedralCone ({0} : Set E) := by
  classical
  set b := Module.finBasis ℝ E with hb
  refine ⟨Finset.univ.image b.coord ∪ Finset.univ.image (fun i => -b.coord i), ?_⟩
  ext x
  simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro rfl φ _
    simp
  · intro h
    refine b.forall_coord_eq_zero_iff.1 fun i => le_antisymm (h _ (Or.inl ⟨i, rfl⟩)) ?_
    have := h _ (Or.inr ⟨i, rfl⟩)
    simpa using this

/-- **Weyl's half of Minkowski–Weyl**: a finitely generated convex cone is polyhedral.

The proof is an induction on the generators: the origin is polyhedral, and `add_ray` adds one
generator at a time. No topology is involved. -/
theorem FinitelyGeneratedCone.polyhedralCone [FiniteDimensional ℝ E] {K : Set E}
    (hK : FinitelyGeneratedCone K) : PolyhedralCone K := by
  classical
  obtain ⟨s, rfl⟩ := hK
  induction s using Finset.induction_on with
  | empty =>
    have : (PointedCone.hull ℝ ((∅ : Finset E) : Set E) : Set E) = {0} := by
      rw [Finset.coe_empty, PointedCone.hull, Submodule.span_empty]
      rfl
    rw [this]
    exact polyhedralCone_zero
  | insert v s _ ih =>
    rw [Finset.coe_insert, coe_hull_insert]
    exact ih.add_ray v

end Weyl

/-! ### Closedness -/

section Closed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A polyhedral cone is closed: it is a finite intersection of closed half-spaces, and in finite
dimensions every linear functional is continuous. -/
theorem PolyhedralCone.isClosed {K : Set E} (hK : PolyhedralCone K) : IsClosed K := by
  obtain ⟨s, rfl⟩ := hK
  have hEq : {x : E | ∀ φ ∈ s, φ x ≤ 0} = ⋂ φ ∈ s, {x : E | φ x ≤ 0} := by
    ext x; simp
  rw [hEq]
  exact isClosed_iInter fun φ => isClosed_iInter fun _ =>
    isClosed_le (LinearMap.continuous_of_finiteDimensional φ) continuous_const

/-- **A finitely generated convex cone is closed.** The classical route is Carathéodory's theorem,
before Minkowski–Weyl; here it is a corollary of Weyl's half. -/
theorem FinitelyGeneratedCone.isClosed {K : Set E} (hK : FinitelyGeneratedCone K) : IsClosed K :=
  hK.polyhedralCone.isClosed

end Closed

/-! ### Minkowski's half, and the equivalence of the two descriptions -/

section Minkowski

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Minkowski's half of Minkowski–Weyl**: a polyhedral convex cone is finitely generated.

The generators are produced in the dual: the cone `C` generated by the constraint functionals is
finitely generated, hence polyhedral by Weyl's half, and the functionals cutting `C` out are
evaluations at points `v₁, …, v_m` of `E` because a finite-dimensional space is reflexive. Those
points generate `K`. One inclusion is immediate; the other separates a point of `K` from the cone
they generate — which is closed, again by Weyl's half — and observes that the separating
functional lies in `C`. -/
theorem PolyhedralCone.finitelyGeneratedCone {K : Set E} (hK : PolyhedralCone K) :
    FinitelyGeneratedCone K := by
  classical
  obtain ⟨s, rfl⟩ := hK
  obtain ⟨t, ht⟩ :
      PolyhedralCone (PointedCone.hull ℝ (s : Set (E →ₗ[ℝ] ℝ)) : Set (E →ₗ[ℝ] ℝ)) :=
    FinitelyGeneratedCone.polyhedralCone ⟨s, rfl⟩
  set D : Finset E := t.image fun Φ => (Module.evalEquiv ℝ E).symm Φ with hD
  have hEval : ∀ (Φ : (E →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ) (ψ : E →ₗ[ℝ] ℝ),
      Φ ψ = ψ ((Module.evalEquiv ℝ E).symm Φ) := by
    intro Φ ψ
    conv_lhs => rw [← (Module.evalEquiv ℝ E).apply_symm_apply Φ]
    rfl
  have hmemD : ∀ w ∈ D, ∃ Φ ∈ t, (Module.evalEquiv ℝ E).symm Φ = w := by
    intro w hw
    obtain ⟨Φ, hΦ, rfl⟩ := Finset.mem_image.1 hw
    exact ⟨Φ, hΦ, rfl⟩
  refine ⟨D, subset_antisymm ?_ ?_⟩
  · -- the hard inclusion, by separation
    intro x hx
    by_contra hcon
    have hGclosed : IsClosed (PointedCone.hull ℝ (D : Set E) : Set E) :=
      FinitelyGeneratedCone.isClosed ⟨D, rfl⟩
    obtain ⟨f, u, hfG, hfx⟩ :=
      geometric_hahn_banach_closed_point
        ((PointedCone.hull ℝ (D : Set E) : ConvexCone ℝ E)).convex hGclosed hcon
    have hcone : ∀ ⦃a : ℝ⦄, 0 < a → ∀ ⦃y⦄, y ∈ (PointedCone.hull ℝ (D : Set E) : Set E) →
        a • y ∈ (PointedCone.hull ℝ (D : Set E) : Set E) :=
      fun a ha y hy =>
        Submodule.smul_mem (PointedCone.hull ℝ (D : Set E)) (⟨a, ha.le⟩ : {c : ℝ // 0 ≤ c}) hy
    have hle : ∀ y ∈ (PointedCone.hull ℝ (D : Set E) : Set E), f y ≤ 0 := fun y hy =>
      le_zero_of_isCone_of_forall_le hcone (fun z hz => (hfG z hz).le) hy
    have hu : 0 < u := by
      have h0 := hfG 0 (PointedCone.hull ℝ (D : Set E)).zero_mem
      simpa using h0
    -- the separating functional satisfies the constraints defining `t`, so it lies in the cone
    -- generated by `s`
    have hfC : (f : E →ₗ[ℝ] ℝ) ∈
        (PointedCone.hull ℝ (s : Set (E →ₗ[ℝ] ℝ)) : Set (E →ₗ[ℝ] ℝ)) := by
      rw [ht]
      intro Φ hΦ
      rw [hEval]
      exact hle _ (PointedCone.subset_hull (Finset.mem_coe.2
        (Finset.mem_image.2 ⟨Φ, hΦ, rfl⟩)))
    -- but then it is nonpositive at `x`
    have hfx0 : f x ≤ 0 :=
      forall_nonpos_of_mem_hull (θ := Module.Dual.eval ℝ E x)
        (fun ψ hψ => hx ψ (Finset.mem_coe.1 hψ)) hfC
    linarith
  · -- the easy inclusion
    intro x hx φ hφ
    refine forall_nonpos_of_mem_hull (θ := φ) (fun w hw => ?_) hx
    obtain ⟨Φ, hΦ, rfl⟩ := hmemD w (Finset.mem_coe.1 hw)
    rw [← hEval]
    have : φ ∈ (PointedCone.hull ℝ (s : Set (E →ₗ[ℝ] ℝ)) : Set (E →ₗ[ℝ] ℝ)) :=
      PointedCone.subset_hull (Finset.mem_coe.2 hφ)
    rw [ht] at this
    exact this Φ hΦ

/-- **The Minkowski–Weyl theorem, for cones.** In a finite-dimensional space, a convex cone is cut
out by finitely many homogeneous linear inequalities if and only if it is generated by finitely
many vectors. -/
theorem polyhedralCone_iff_finitelyGeneratedCone {K : Set E} :
    PolyhedralCone K ↔ FinitelyGeneratedCone K :=
  ⟨PolyhedralCone.finitelyGeneratedCone, FinitelyGeneratedCone.polyhedralCone⟩

end Minkowski

end ConvexAnalysis
