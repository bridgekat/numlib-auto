import Numlib.Krylov.Monotonicity
import Numlib.Analysis.InnerProductSpace.Projection.Compression

/-!
# Galerkin iterates inside a finite Krylov compression

Compression to a later Krylov space preserves all earlier powers and Galerkin
conditions. Positive definiteness only on that compression therefore suffices
for monotonicity of the earlier Galerkin iterate norms.
-/

namespace Krylov
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Powers of a compressed operator agree with ambient powers while the orbit stays in
its compression space. -/
theorem coe_pow_compression (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (b : K) (i : ℕ)
    (hmem : ∀ j ≤ i, (A ^ j) (b : E) ∈ K) :
    (((compression A K) ^ i) b : E) = (A ^ i) (b : E) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi := ih fun j hj => hmem j (hj.trans (Nat.le_succ i))
    rw [pow_succ', Module.End.mul_apply]
    change (K.orthogonalProjectionOnto
      (A ((((compression A K) ^ i) b : K) : E)) : E) = _
    rw [hi]
    have he : A ((A ^ i) (b : E)) = (A ^ (i + 1)) (b : E) := by
      rw [pow_succ']; rfl
    rw [he]
    exact congrArg Subtype.val (K.orthogonalProjectionOnto_mem_subspace_eq_self
      ⟨_, hmem (i + 1) le_rfl⟩)

/-- Compressing to a later Krylov space preserves every earlier Krylov space. -/
theorem map_subspace_compression (A : E →ₗ[𝕜] E) (b : E) {l : ℕ} (hl : 0 < l)
    {k : ℕ} (hk : k ≤ l) :
    (subspace (compression A (subspace A b l))
      ⟨b, self_mem_subspace A b hl⟩ k).map (subspace A b l).subtype = subspace A b k := by
  change (Submodule.span 𝕜 (Set.range fun i : Fin k =>
    ((compression A (subspace A b l)) ^ (i : ℕ))
      ⟨b, self_mem_subspace A b hl⟩)).map _ =
        Submodule.span 𝕜 (Set.range fun i : Fin k => (A ^ (i : ℕ)) b)
  rw [Submodule.map_span, ← Set.range_comp]
  congr 1
  congr 1
  funext i
  exact coe_pow_compression A (subspace A b l) _ i fun j hj =>
    pow_apply_mem_subspace A b (lt_of_le_of_lt hj (lt_of_lt_of_le i.isLt hk))

/-- An actual Galerkin iterate transfers to the compression to a later Krylov space. -/
theorem isGalerkinIterate_compression (A : E →ₗ[𝕜] E) (b : E) {l : ℕ} (hl : 0 < l)
    {k : ℕ} (hk : k ≤ l) {x : E} (hx : IsGalerkinIterate A b 0 k x) :
    IsGalerkinIterate (compression A (subspace A b l))
      ⟨b, self_mem_subspace A b hl⟩ 0 k
      ⟨x, subspace_mono A b hk (by simpa using hx.mem)⟩ := by
  let K := subspace A b l
  let bK : K := ⟨b, self_mem_subspace A b hl⟩
  let xK : K := ⟨x, subspace_mono A b hk (by simpa using hx.mem)⟩
  have hmap := map_subspace_compression A b hl hk
  refine ⟨?_, ?_⟩
  · simp only [map_zero, sub_zero]
    have hxmem : x ∈ (subspace (compression A K) bK k).map K.subtype := by
      rw [hmap]
      simpa using hx.mem
    obtain ⟨z, hz, hzx⟩ := hxmem
    have he : z = xK := Subtype.ext hzx
    change xK ∈ subspace (compression A K) bK k
    rw [← he]
    exact hz
  · apply (Submodule.mem_orthogonal _ _).mpr
    intro z hz
    simp only [map_zero, sub_zero] at hz
    have hz' : (z : E) ∈ subspace A b k := by
      rw [← hmap]
      exact Submodule.mem_map_of_mem hz
    have hh := IsPetrovGalerkin.inner_residual_eq_zero hx (by simpa using hz')
    change inner 𝕜 z (bK - compression A K xK) = 0
    rw [inner_sub_right, compression.inner_apply']
    change inner 𝕜 (z : E) b - inner 𝕜 (z : E) (A x) = 0
    simpa only [inner_sub_right] using hh

/-- Krylov Galerkin norms are ordered whenever the operator is positive definite on the
later Krylov space. Ambient positive definiteness is unnecessary. -/
theorem norm_le_norm_of_compression_isSymmetricCoercive
    (A : E →ₗ[𝕜] E) (b : E) {k l : ℕ} (hl : 0 < l) (hkl : k ≤ l)
    (hA : (compression A (subspace A b l)).IsSymmetricCoercive)
    {x y : E} (hx : IsGalerkinIterate A b 0 k x)
    (hy : IsGalerkinIterate A b 0 l y) : ‖x‖ ≤ ‖y‖ := by
  have hx' := isGalerkinIterate_compression A b hl hkl hx
  have hy' := isGalerkinIterate_compression A b hl le_rfl hy
  have hh := CG.norm_iterate_monotone
    (⟨b, self_mem_subspace A b hl⟩ : subspace A b l) hA hkl
  dsimp only at hh
  rw [← IsGalerkinIterate.eq_CG_iterate hA hx',
    ← IsGalerkinIterate.eq_CG_iterate hA hy'] at hh
  exact hh
end Krylov
