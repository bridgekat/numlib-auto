import Numlib.Analysis.InnerProductSpace.Coercive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Projection methods: specifications and well-posedness

The canonical Prop-valued specifications of a projection step (Saad[^saad-iterative] Ch. 5,
Fong–Saunders[^fong-saunders] §2, Choi[^choi] Table 2.5, Atkinson–Han[^atkinson-han] Ch. 9):

* `IsPetrovGalerkin A b x₀ K L x`: `x ∈ x₀ + K` and `b - A x ⟂ L`;
* `IsGalerkin A b x₀ K x`: the case `L = K` (FOM, CG, Lanczos method);
* `IsMinRes A b x₀ K x`: `x ∈ x₀ + K` minimizes `‖b - A x‖` (GMRES, MINRES, CR);
* `IsMinError xstar x₀ K x`: `x ∈ x₀ + K` minimizes `‖xstar - x‖` (SYMMLQ, CGNE).

Well-posedness (Saad Prop 5.1), the residual formula (Saad Prop 5.4), exactness on invariant
subspaces (Saad Prop 5.6) and the matrix representation (Saad (5.7)) are stated here; optimality
characterizations are in `Optimality.lean`.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
[^fong-saunders]: David Chin-Lung Fong and Michael Saunders, *CG versus MINRES: an empirical
  comparison*, SQU Journal for Science 17 (2012), 44–62.
[^choi]: Sou-Cheng Choi, *Iterative Methods for Singular Linear Equations and Least-Squares
  Problems*, PhD thesis, Stanford University, 2006.
[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Submodule

variable {K : Submodule 𝕜 E}

/-- Membership in the orthogonal complement of a span is tested on the spanning set. -/
theorem mem_orthogonal_span {s : Set E} {v : E} :
    v ∈ (Submodule.span 𝕜 s)ᗮ ↔ ∀ u ∈ s, inner 𝕜 u v = 0 := by
  refine ⟨fun h u hu => h u (Submodule.subset_span hu), fun h u hu => ?_⟩
  induction hu using Submodule.span_induction with
  | mem z hz => exact h z hz
  | zero => simp
  | add z w _ _ hz hw => rw [inner_add_left, hz, hw, add_zero]
  | smul c z _ hz => rw [inner_smul_left, hz, mul_zero]

/-- The orthogonal projection is invisible to inner products against `K`. -/
theorem inner_starProjection_right [K.HasOrthogonalProjection] {w : E} (hw : w ∈ K) (u : E) :
    inner 𝕜 w (K.starProjection u) = inner 𝕜 w u := by
  have h : inner 𝕜 w (u - K.starProjection u) = (0 : 𝕜) :=
    inner_eq_zero_symm.1 (K.starProjection_inner_eq_zero u w hw)
  rw [inner_sub_right, sub_eq_zero] at h
  exact h.symm

/-- Best approximation from a subspace: the error of a minimizer is orthogonal to the subspace
(the pointwise form of `Submodule.norm_eq_iInf_iff_inner_eq_zero`). -/
theorem inner_eq_zero_of_forall_norm_sub_le {u v : E} (hv : v ∈ K)
    (h : ∀ w ∈ K, ‖u - v‖ ≤ ‖u - w‖) {w : E} (hw : w ∈ K) : inner 𝕜 (u - v) w = 0 := by
  have hbdd : BddBelow (Set.range fun z : K => ‖u - (z : E)‖) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact norm_nonneg _
  refine (K.norm_eq_iInf_iff_inner_eq_zero hv).1 ?_ w hw
  exact le_antisymm (le_ciInf fun z => h z z.2) (ciInf_le hbdd ⟨v, hv⟩)

/-- Conversely, a point of `K` whose error is orthogonal to `K` is a best approximation. -/
theorem norm_sub_le_of_forall_inner_eq_zero {u v : E} (hv : v ∈ K)
    (h : ∀ w ∈ K, inner 𝕜 (u - v) w = 0) {w : E} (hw : w ∈ K) : ‖u - v‖ ≤ ‖u - w‖ := by
  have hvw : u - w = (u - v) + (v - w) := by abel
  have h0 : inner 𝕜 (u - v) (v - w) = (0 : 𝕜) := h _ (K.sub_mem hv hw)
  have h1 : ‖u - v‖ * ‖u - v‖ ≤ ‖u - w‖ * ‖u - w‖ := by
    rw [hvw, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0]
    nlinarith [norm_nonneg (v - w)]
  have h2 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_mul_self (norm_nonneg _), Real.sqrt_mul_self (norm_nonneg _)] at h2

end Submodule

/-- Petrov–Galerkin specification: `x ∈ x₀ + K` and `b - A x ⟂ L`
(Saad, *Iterative Methods*, (5.1)–(5.2)). -/
structure IsPetrovGalerkin (A : E →ₗ[𝕜] E) (b x₀ : E) (K L : Submodule 𝕜 E) (x : E) : Prop where
  mem : x - x₀ ∈ K
  orth : b - A x ∈ Lᗮ

/-- Galerkin (orthogonal projection) specification `L = K`. -/
abbrev IsGalerkin (A : E →ₗ[𝕜] E) (b x₀ : E) (K : Submodule 𝕜 E) (x : E) : Prop :=
  IsPetrovGalerkin A b x₀ K K x

/-- Minimal-residual specification: `x ∈ x₀ + K` minimizes `‖b - A x‖`. -/
structure IsMinRes (A : E →ₗ[𝕜] E) (b x₀ : E) (K : Submodule 𝕜 E) (x : E) : Prop where
  mem : x - x₀ ∈ K
  min : ∀ y, y - x₀ ∈ K → ‖b - A x‖ ≤ ‖b - A y‖

/-- Minimal-error specification: `x ∈ x₀ + K` minimizes the distance to the target `xstar` (the
solution of `A x = b`, made explicit so that the specification is meaningful for singular `A`):
SYMMLQ with `K = A 𝒦_m`, CGNE / Craig's method with `K = A† L`. No operator appears — this is
best approximation of `xstar` from the affine subspace `x₀ + K`. -/
structure IsMinError (xstar x₀ : E) (K : Submodule 𝕜 E) (x : E) : Prop where
  mem : x - x₀ ∈ K
  min : ∀ y, y - x₀ ∈ K → ‖xstar - x‖ ≤ ‖xstar - y‖

namespace IsPetrovGalerkin

variable {A : E →ₗ[𝕜] E} {b x₀ : E} {K L : Submodule 𝕜 E} {x : E}

/-- The Petrov–Galerkin condition as a scalar equation: the residual `b - A x` is orthogonal to
every test vector `w ∈ L`.  This is the form in which the orthogonality is used downstream. -/
theorem inner_residual_eq_zero (hx : IsPetrovGalerkin A b x₀ K L x) {w : E} (hw : w ∈ L) :
    inner 𝕜 w (b - A x) = 0 :=
  (Submodule.mem_orthogonal _ _).1 hx.orth w hw

/-- Two Petrov–Galerkin solutions differ by an element of `K ⊓ A⁻¹(Lᗮ)`; uniqueness when
`A` maps `K` injectively "modulo `Lᗮ`", the nondegeneracy condition of Saad,
*Iterative Methods*, Prop 5.1. -/
theorem eq_of_forall (hx : IsPetrovGalerkin A b x₀ K L x) {x' : E}
    (hx' : IsPetrovGalerkin A b x₀ K L x')
    (hKL : ∀ z ∈ K, A z ∈ Lᗮ → z = 0) : x = x' := by
  have hmem : x - x' ∈ K := by
    have h : x - x' = (x - x₀) - (x' - x₀) := by abel
    rw [h]; exact K.sub_mem hx.mem hx'.mem
  have hAz : A (x - x') ∈ Lᗮ := by
    have h : A (x - x') = (b - A x') - (b - A x) := by rw [map_sub]; abel
    rw [h]; exact Submodule.sub_mem _ hx'.orth hx.orth
  exact sub_eq_zero.1 (hKL _ hmem hAz)

/-- Saad, *Iterative Methods*, Prop 5.6: exactness on invariant subspaces.  If `K` is invariant
under `A`, the initial residual lies in `K` and `K ⊓ Lᗮ = 0`, then the Petrov–Galerkin iterate
solves `A x = b` exactly. -/
theorem eq_of_invt (hx : IsPetrovGalerkin A b x₀ K L x) (hK : K ∈ Module.End.invtSubmodule A)
    (hr : b - A x₀ ∈ K) (hKL : ∀ z ∈ K, z ∈ Lᗮ → z = 0) : A x = b := by
  have h1 : b - A x ∈ K := by
    have h : b - A x = (b - A x₀) - A (x - x₀) := by rw [map_sub]; abel
    rw [h]
    exact K.sub_mem hr ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).1 hK _ hx.mem)
  exact (sub_eq_zero.1 (hKL _ h1 hx.orth)).symm

/-- Restarting: a Petrov–Galerkin step from `x₀` is a Petrov–Galerkin step from any
`x₁ ∈ x₀ + K`. -/
theorem of_mem (hx : IsPetrovGalerkin A b x₀ K L x) {x₁ : E} (hx₁ : x₁ - x₀ ∈ K) :
    IsPetrovGalerkin A b x₁ K L x := by
  refine ⟨?_, hx.orth⟩
  have h : x - x₁ = (x - x₀) - (x₁ - x₀) := by abel
  rw [h]; exact K.sub_mem hx.mem hx₁

/-- The Petrov–Galerkin residual is orthogonal to `L`; a restatement of the defining condition,
and the input to the quasi-optimality bound of Saad, *Iterative Methods*, Thm 5.7, which with
`r₀ = b - A x₀` and `d₀ = x* - x₀` controls the error by the distance of `d₀` from `K`.  See
`Optimality.lean` for the Galerkin / minimal-residual cases. -/
theorem residual_mem_orthogonal (hx : IsPetrovGalerkin A b x₀ K L x) : b - A x ∈ Lᗮ := hx.orth

end IsPetrovGalerkin

/-- The residual at `y` in terms of the initial residual. -/
theorem residual_eq_sub_apply_sub (A : E →ₗ[𝕜] E) (b x₀ y : E) :
    b - A y = (b - A x₀) - A (y - x₀) := by rw [map_sub]; abel

namespace IsMinRes

variable {A : E →ₗ[𝕜] E} {b x₀ : E} {K : Submodule 𝕜 E} {x : E}

/-- Saad, *Iterative Methods*, Prop 5.3: minimal residual over `x₀ + K` iff Petrov–Galerkin with
`L = A K`. -/
theorem iff_isPetrovGalerkin [FiniteDimensional 𝕜 K] :
    IsMinRes A b x₀ K x ↔ IsPetrovGalerkin A b x₀ K (K.map A) x := by
  constructor
  · rintro ⟨hmem, hmin⟩
    refine ⟨hmem, (Submodule.mem_orthogonal' _ _).2 fun u hu => ?_⟩
    rw [residual_eq_sub_apply_sub A b x₀ x]
    refine Submodule.inner_eq_zero_of_forall_norm_sub_le (Submodule.mem_map_of_mem hmem) ?_ hu
    rintro _ hw
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hw
    have h := hmin (x₀ + z) (by simpa using hz)
    rwa [residual_eq_sub_apply_sub A b x₀ x, residual_eq_sub_apply_sub A b x₀ (x₀ + z),
      add_sub_cancel_left] at h
  · rintro ⟨hmem, horth⟩
    refine ⟨hmem, fun y hy => ?_⟩
    rw [residual_eq_sub_apply_sub A b x₀ x, residual_eq_sub_apply_sub A b x₀ y]
    refine Submodule.norm_sub_le_of_forall_inner_eq_zero (Submodule.mem_map_of_mem hmem) ?_
      (Submodule.mem_map_of_mem hy)
    intro w hw
    rw [← residual_eq_sub_apply_sub A b x₀ x]
    exact (Submodule.mem_orthogonal' _ _).1 horth w hw

theorem isPetrovGalerkin [FiniteDimensional 𝕜 K] (hx : IsMinRes A b x₀ K x) :
    IsPetrovGalerkin A b x₀ K (K.map A) x :=
  (iff_isPetrovGalerkin).1 hx

/-- Saad, *Iterative Methods*, Prop 5.4: the residual of every minimal-residual iterate is
`(1 - P_{A K}) r₀`, with `r₀ = b - A x₀` and `P_{A K}` the orthogonal projection onto `A K`. -/
theorem residual_eq [FiniteDimensional 𝕜 K] (hx : IsMinRes A b x₀ K x) :
    b - A x = (b - A x₀) - (K.map A).starProjection (b - A x₀) := by
  have hproj : (K.map A).starProjection (b - A x₀) = A (x - x₀) :=
    Submodule.eq_starProjection_of_mem_orthogonal' (Submodule.mem_map_of_mem hx.mem)
      hx.isPetrovGalerkin.orth
      (by rw [residual_eq_sub_apply_sub A b x₀ x]; abel)
  rw [hproj, ← residual_eq_sub_apply_sub A b x₀ x]

/-- The residual is unique even when the iterate is not. -/
theorem residual_unique [FiniteDimensional 𝕜 K] (hx : IsMinRes A b x₀ K x) {x' : E}
    (hx' : IsMinRes A b x₀ K x') : b - A x = b - A x' := by
  rw [hx.residual_eq, hx'.residual_eq]

/-- A minimal-residual step never increases the residual norm, since the starting point `x₀` is
itself a competitor in the minimization over `x₀ + K`. -/
theorem norm_residual_le_norm_residual_zero (hx : IsMinRes A b x₀ K x) :
    ‖b - A x‖ ≤ ‖b - A x₀‖ :=
  hx.min x₀ (by simp)

/-- Residual norms on nested subspaces are nonincreasing. -/
theorem norm_residual_le {K' : Submodule 𝕜 E} {x' : E} (hx : IsMinRes A b x₀ K x)
    (hx' : IsMinRes A b x₀ K' x') (hKK' : K ≤ K') : ‖b - A x'‖ ≤ ‖b - A x‖ :=
  hx'.min x (hKK' hx.mem)

/-- Exactness: if some `y ∈ x₀ + K` solves the system, so does every minimal-residual iterate. -/
theorem apply_eq_of_exists (hx : IsMinRes A b x₀ K x) {y : E} (hy : y - x₀ ∈ K) (hAy : A y = b) :
    A x = b := by
  have h := hx.min y hy
  rw [hAy, sub_self, norm_zero] at h
  exact (sub_eq_zero.1 (norm_le_zero_iff.1 h)).symm

end IsMinRes

section WellPosed

variable {A : E →ₗ[𝕜] E} (b x₀ : E) (K : Submodule 𝕜 E)

/-- Coercivity gives the nondegeneracy condition of Saad, *Iterative Methods*, Prop 5.1 (i):
no nonzero `z ∈ K` has `A z ⟂ K`. -/
theorem eq_zero_of_isCoercive_of_apply_mem_orthogonal (hA : A.IsCoercive) {z : E} (hz : z ∈ K)
    (hAz : A z ∈ Kᗮ) : z = 0 := by
  obtain ⟨c, hc, hAc⟩ := hA
  have h0 : inner 𝕜 z (A z) = (0 : 𝕜) := (Submodule.mem_orthogonal _ _).1 hAz z hz
  have hre : RCLike.re (inner 𝕜 (A z) z) = 0 := by
    rw [← inner_conj_symm, h0, map_zero, map_zero]
  have hle := hAc z
  rw [hre] at hle
  have hz2 : ‖z‖ ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hz2)

/-- Saad, *Iterative Methods*, Prop 5.1 (i): Galerkin with coercive `A` is uniquely solvable. -/
theorem existsUnique_isGalerkin_of_isCoercive (hA : A.IsCoercive) [FiniteDimensional 𝕜 K] :
    ∃! x, IsGalerkin A b x₀ K x := by
  have hKL : ∀ z ∈ K, A z ∈ Kᗮ → z = 0 := fun z hz hAz =>
    eq_zero_of_isCoercive_of_apply_mem_orthogonal K hA hz hAz
  -- the compression of `A` to `K` is injective, hence surjective
  have hinj : Function.Injective
      ((K.orthogonalProjectionOnto : E →ₗ[𝕜] K).comp (A.comp K.subtype)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hz' : K.starProjection (A (z : E)) = 0 := by
      rw [Submodule.starProjection_apply]
      exact congrArg Subtype.val hz
    refine Subtype.ext (hKL _ z.2 ((Submodule.mem_orthogonal _ _).2 fun w hw => ?_))
    rw [← Submodule.inner_starProjection_right hw (A (z : E)), hz', inner_zero_right]
  obtain ⟨z, hz⟩ :=
    (LinearMap.injective_iff_surjective.1 hinj) (K.orthogonalProjectionOnto (b - A x₀))
  have hz' : K.starProjection (A (z : E)) = K.starProjection (b - A x₀) := by
    rw [Submodule.starProjection_apply, Submodule.starProjection_apply]
    exact congrArg Subtype.val hz
  have hgal : IsGalerkin A b x₀ K (x₀ + (z : E)) := by
    refine ⟨by simp, (Submodule.mem_orthogonal _ _).2 fun w hw => ?_⟩
    have h1 : inner 𝕜 w (A (z : E)) = inner 𝕜 w (b - A x₀) := by
      rw [← Submodule.inner_starProjection_right hw (A (z : E)), hz',
        Submodule.inner_starProjection_right hw]
    rw [map_add, ← sub_sub, inner_sub_right, h1, sub_self]
  exact ⟨x₀ + (z : E), hgal, fun y hy => hy.eq_of_forall hgal hKL⟩

/-- A minimal-residual iterate always exists on a finite-dimensional `K`. -/
theorem exists_isMinRes [FiniteDimensional 𝕜 K] : ∃ x, IsMinRes A b x₀ K x := by
  obtain ⟨z, hz, hzeq⟩ := Submodule.mem_map.1
    (Submodule.starProjection_apply_mem (K.map A) (b - A x₀))
  refine ⟨x₀ + z, IsMinRes.iff_isPetrovGalerkin.2 ⟨by simpa using hz, ?_⟩⟩
  have h : b - A (x₀ + z) = (b - A x₀) - (K.map A).starProjection (b - A x₀) := by
    rw [map_add, hzeq]; abel
  rw [h]
  exact Submodule.sub_starProjection_mem_orthogonal _

/-- Saad, *Iterative Methods*, Prop 5.1 (ii): minimal residual with `A` injective on `K` is
uniquely solvable. -/
theorem existsUnique_isMinRes_of_injOn [FiniteDimensional 𝕜 K] (hinj : Set.InjOn A K) :
    ∃! x, IsMinRes A b x₀ K x := by
  obtain ⟨x, hx⟩ := exists_isMinRes (A := A) b x₀ K
  refine ⟨x, hx, fun y hy => ?_⟩
  refine hy.isPetrovGalerkin.eq_of_forall hx.isPetrovGalerkin fun z hz hAz => ?_
  have h0 : A z = 0 :=
    inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 hAz (A z)
      (Submodule.mem_map_of_mem hz))
  exact hinj hz K.zero_mem (by rw [h0, map_zero])

/-- A minimal-error iterate always exists on a finite-dimensional `K` (projection of `x*`). -/
theorem exists_isMinError [FiniteDimensional 𝕜 K] (xstar : E) : ∃ x, IsMinError xstar x₀ K x := by
  refine ⟨x₀ + K.starProjection (xstar - x₀), ?_, fun y hy => ?_⟩
  · rw [add_sub_cancel_left]
    exact Submodule.starProjection_apply_mem K _
  have h1 : xstar - (x₀ + K.starProjection (xstar - x₀))
      = (xstar - x₀) - K.starProjection (xstar - x₀) := by abel
  have h2 : xstar - y = (xstar - x₀) - (y - x₀) := by abel
  rw [h1, h2]
  exact Submodule.norm_sub_le_of_forall_inner_eq_zero (Submodule.starProjection_apply_mem K _)
    (fun w hw => K.starProjection_inner_eq_zero _ w hw) hy

end WellPosed

section MatrixForm

variable {ι : Type*} [Fintype ι]
variable {A : E →ₗ[𝕜] E} {b x₀ : E} {K L : Submodule 𝕜 E}

/-- Saad, *Iterative Methods*, (5.7): with bases `V` of `K` and `W` of `L`, `x = x₀ + V y` is
Petrov–Galerkin iff `(Wᴴ A V) y = Wᴴ r₀`, where `r₀ = b - A x₀`. -/
theorem isPetrovGalerkin_iff_mulVec (V : Module.Basis ι 𝕜 K) (W : Module.Basis ι 𝕜 L)
    (y : ι → 𝕜) :
    IsPetrovGalerkin A b x₀ K L (x₀ + ∑ j, y j • (V j : E)) ↔
      (Matrix.of fun i j => inner 𝕜 (W i : E) (A (V j))).mulVec y =
        fun i => inner 𝕜 (W i : E) (b - A x₀) := by
  have hmem : (x₀ + ∑ j, y j • (V j : E)) - x₀ ∈ K := by
    simpa using Submodule.sum_mem _ fun j (_ : j ∈ Finset.univ) => K.smul_mem (y j) (V j).2
  have hinner : ∀ i : ι, inner 𝕜 (W i : E) (b - A (x₀ + ∑ j, y j • (V j : E)))
      = inner 𝕜 (W i : E) (b - A x₀)
        - (Matrix.of fun i j => inner 𝕜 (W i : E) (A (V j))).mulVec y i := by
    intro i
    have hres : b - A (x₀ + ∑ j, y j • (V j : E))
        = (b - A x₀) - ∑ j, y j • A (V j) := by
      simp only [map_add, map_sum, map_smul]; abel
    rw [hres, inner_sub_right, inner_sum]
    congr 1
    simp only [Matrix.mulVec, Matrix.of_apply, dotProduct, inner_smul_right]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hL : Submodule.span 𝕜 (Set.range fun i => (W i : E)) = L := by
    have himg : (L.subtype '' Set.range W) = Set.range fun i => (W i : E) := by
      rw [← Set.range_comp]; rfl
    rw [← himg, ← Submodule.map_span, W.span_eq, Submodule.map_top, Submodule.range_subtype]
  constructor
  · intro h
    funext i
    have h0 := (Submodule.mem_orthogonal _ _).1 h.orth (W i : E) (W i).2
    rw [hinner i] at h0
    exact (sub_eq_zero.1 h0).symm
  · intro h
    refine ⟨hmem, ?_⟩
    rw [← hL, Submodule.mem_orthogonal_span]
    rintro _ ⟨i, rfl⟩
    rw [hinner i, congrFun h i, sub_self]

end MatrixForm
