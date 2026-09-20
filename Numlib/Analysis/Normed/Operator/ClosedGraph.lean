/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Operator.Banach`, beside
`LinearMap.continuous_of_seq_closed_graph`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# A bounded lift along an injective bounded map

For Banach spaces `X`, `Y` and an injective bounded linear `J : Y → Z`, a bounded linear
`S : X → Z` whose values all lie in the range of `J` factors as `S = J ∘ T` with `T : X → Y`
bounded linear (`exists_continuousLinearMap_comp_eq_of_injective`): the lift is linear by the
injectivity of `J`, and continuous by the closed graph theorem since `J` and `S` are continuous.
This is how a solution operator with values in a smaller space (`D(A) → H¹₀(Ω)`,
`D(A^ℓ) → H^{2ℓ}(Ω)`) is made bounded for the norm of the smaller space.
-/

open Filter Topology

/-- **A bounded lift along an injective bounded map, by the closed graph theorem**: for Banach
spaces `X`, `Y` and an injective bounded linear `J : Y → Z`, a bounded linear `S : X → Z` whose
values all lie in the range of `J` factors as `S = J ∘ T` with `T : X → Y` bounded linear. The
lift is linear by the injectivity of `J` and has closed graph since `J` and `S` are continuous. -/
theorem exists_continuousLinearMap_comp_eq_of_injective {X Y Z : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {J : Y →L[ℝ] Z} (hJ : Function.Injective J)
    {S : X →L[ℝ] Z} (hS : ∀ x, ∃ y, J y = S x) : ∃ T : X →L[ℝ] Y, ∀ x, J (T x) = S x := by
  choose T hT using hS
  obtain ⟨Tₗ, hTₗ⟩ : ∃ Tₗ : X →ₗ[ℝ] Y, ∀ x, Tₗ x = T x := by
    refine ⟨{ toFun := T, map_add' := fun x y ↦ ?_, map_smul' := fun c x ↦ ?_ }, fun _ ↦ rfl⟩
    · refine hJ ?_
      rw [map_add, hT, hT, hT, map_add]
    · refine hJ ?_
      rw [RingHom.id_apply, map_smul, hT, hT, map_smul]
  have hcont : Continuous Tₗ := by
    refine Tₗ.continuous_of_seq_closed_graph fun u x y hux hTy ↦ ?_
    have h1 : Tendsto (fun n ↦ J (Tₗ (u n))) atTop (𝓝 (J y)) := (J.continuous.tendsto y).comp hTy
    have h2 : Tendsto (fun n ↦ S (u n)) atTop (𝓝 (S x)) := (S.continuous.tendsto x).comp hux
    have h12 : (fun n ↦ J (Tₗ (u n))) = fun n ↦ S (u n) := by
      funext n
      rw [hTₗ, hT]
    rw [h12] at h1
    refine hJ ?_
    rw [hTₗ, hT, tendsto_nhds_unique h1 h2]
  exact ⟨⟨Tₗ, hcont⟩, fun x ↦ by rw [← hT x, ← hTₗ x]; rfl⟩
