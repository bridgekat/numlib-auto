import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ENat.Lattice
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder
import Numlib.Optimization.Complexity.Basic
import Numlib.Optimization.Complexity.OracleMethod

/-!
# Zero chains and zero-respecting methods

Oracle complexity of classes of `p`-th order methods on classes of functions of variable dimension,
and zero-respecting methods on zero-chain functions ([cartis2022evaluation], Section 4.2, after
Carmon, Duchi, Hinder and Sidford, *Lower bounds for finding stationary points I*). Spaces are
`EuclideanSpace ℝ (Fin n)`, since zero chains and zero-respecting methods are coordinate notions;
the coordinate vectors are `EuclideanSpace.single j 1`.

## Methods and complexity

* `Optimization.Jet E p`: the answers `(f(x), ∇f(x), …, ∇^p f(x))` of the `p`-th order
  oracle.
* `Optimization.JetMethod p`: one deterministic `p`-th order oracle method in every dimension (the
  book's maps `M^{(k)}`), with iterates `M.iter n f k` on `f : ℝ^n → ℝ`; `methodClass p` is the
  class `𝓜(p)` of such methods starting at `x₀ = 0`.
* `Optimization.firstStationaryIndex x f ε : ℕ∞`: the first `k` with `‖∇f(x_k)‖ ≤ ε` (`⊤` if there
  is none), the book's `k_ε(M, f)`.
* `Optimization.classComplexity 𝓜 𝓕 ε : ℕ∞`: the book's `#_ε(𝓜, 𝓕) = inf_M sup_f k_ε(M, f)`,
  (4.2.2).
* `Optimization.smoothClass Δ L p`: the class `𝓕(Δ, p)`, with the orthogonal invariance
  `comp_adjoint_mem_smoothClass` (footnote 30).

## Zero chains

* `Optimization.IsNullDirection A v`: the multilinear map `A` vanishes whenever one of its arguments
  is `v` (the book's `∇^q f(x) e_j = 0`; for symmetric `A` this is `A.curryLeft v = 0`, see
  `isNullDirection_iff_curryLeft_eq_zero`).
* `Optimization.IsZeroRespectingFor M f` ((4.2.1)) and the class `zeroRespectingClass p`
  (`𝓜_ZR(p)`).
* `Optimization.IsZeroChain f p` ((4.2.4)), its scale invariance `IsZeroChain.comp_smul`
  (Lemma 4.2.1), Lemma 4.2.2 (`IsZeroRespectingFor.iterate_apply_eq_zero`) and Lemma 4.2.3
  (`le_firstStationaryIndex_of_isZeroChain`, `le_classComplexity_of_isZeroChain`).

Coordinates are `0`-based: the book's `[x]_j`, `j ∈ [1 : n]`, is `x ⟨j - 1, _⟩`.
-/

open Set Filter Topology ContDiff
open scoped InnerProductSpace

namespace Optimization

/-! ### Jets, jet methods and the class `𝓜(p)` -/

/-- The answers of the `p`-th order oracle on `E`: one continuous `j`-linear form for each
`j = 0, …, p` (the values `∇^j f(x)` of `jetOracle f p x`). -/
abbrev Jet (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ℕ) :=
  (j : Fin (p + 1)) → ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ

/-- A deterministic `p`-th order method in every dimension: for each `n`, an oracle method on
`ℝ^n` whose iterates are functions of the jets `(f(x_i), ∇f(x_i), …, ∇^p f(x_i))`, `i ≤ k`, at the
previous iterates ([cartis2022evaluation], Section 4.2.1.2, the maps `M^{(k)}`). -/
abbrev JetMethod (p : ℕ) :=
  (n : ℕ) → OracleMethod (EuclideanSpace ℝ (Fin n)) (Jet (EuclideanSpace ℝ (Fin n)) p)

namespace JetMethod

variable {p : ℕ}

/-- The `k`-th iterate of the method `M` applied to `f : ℝ^n → ℝ`. -/
noncomputable def iter (M : JetMethod p) (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  (M n).iterate (jetOracle f p) k

theorem iter_eq (M : JetMethod p) (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    M.iter n f = (M n).iterate (jetOracle f p) := rfl

end JetMethod

/-- The class `𝓜(p)` of `p`-th order methods ([cartis2022evaluation], Section 4.2.1.2): all jet
methods whose initial point is `x₀ = 0` in every dimension. -/
def methodClass (p : ℕ) : Set (JetMethod p) := {M | ∀ n, (M n).x₀ = 0}

theorem mem_methodClass {p : ℕ} {M : JetMethod p} : M ∈ methodClass p ↔ ∀ n, (M n).x₀ = 0 :=
  Iff.rfl

/-! ### The first `ε`-stationary iterate -/

section FirstStationary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The index of the first `ε`-stationary point of the sequence `x` for `f`, the first `k` with
`‖∇f(x_k)‖ ≤ ε` ([cartis2022evaluation], Section 4.2.1.3, the book's `k_ε(M, f)` when `x` is the
sequence of iterates of `M` on `f`); it is `⊤` when no point of the sequence is `ε`-stationary.
Where `f` is not differentiable, `fderiv ℝ f` is `0`, so such points count as stationary; all
functions of interest (`smoothClass`) are differentiable. -/
noncomputable def firstStationaryIndex (x : ℕ → E) (f : E → ℝ) (ε : ℝ) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : ‖fderiv ℝ f (x k)‖ ≤ ε), (k : ℕ∞)

variable {x : ℕ → E} {f : E → ℝ} {ε : ℝ}

/-- `c ≤ k_ε` iff no point before `c` is `ε`-stationary. -/
theorem le_firstStationaryIndex_iff {c : ℕ∞} :
    c ≤ firstStationaryIndex x f ε ↔ ∀ k : ℕ, (k : ℕ∞) < c → ε < ‖fderiv ℝ f (x k)‖ := by
  simp only [firstStationaryIndex, le_iInf_iff]
  constructor
  · intro h k hk
    by_contra hle
    exact absurd (h k (not_lt.1 hle)) (not_le.2 hk)
  · intro h k hk
    by_contra hlt
    exact absurd hk (not_le.2 (h k (not_le.1 hlt)))

theorem coe_le_firstStationaryIndex_iff {c : ℕ} :
    (c : ℕ∞) ≤ firstStationaryIndex x f ε ↔ ∀ k < c, ε < ‖fderiv ℝ f (x k)‖ := by
  rw [le_firstStationaryIndex_iff]
  exact forall_congr' fun k => by rw [Nat.cast_lt]

theorem firstStationaryIndex_le {k : ℕ} (hk : ‖fderiv ℝ f (x k)‖ ≤ ε) :
    firstStationaryIndex x f ε ≤ k :=
  iInf₂_le k hk

theorem firstStationaryIndex_eq_top_iff :
    firstStationaryIndex x f ε = ⊤ ↔ ∀ k, ε < ‖fderiv ℝ f (x k)‖ := by
  rw [← top_le_iff, le_firstStationaryIndex_iff]
  exact forall_congr' fun k => by simp

/-- `k_ε = k` iff `x_k` is the first `ε`-stationary point. -/
theorem firstStationaryIndex_eq_coe_iff {k : ℕ} :
    firstStationaryIndex x f ε = k ↔ IsFirstHit (fun j => ‖fderiv ℝ f (x j)‖ ≤ ε) k := by
  constructor
  · intro h
    have hle := (coe_le_firstStationaryIndex_iff (x := x) (f := f) (ε := ε) (c := k)).1 h.ge
    refine ⟨?_, fun j hj => not_le.2 (hle j hj)⟩
    by_contra hk
    have : ((k + 1 : ℕ) : ℕ∞) ≤ firstStationaryIndex x f ε := by
      rw [coe_le_firstStationaryIndex_iff]
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact hle j hj
      · exact not_le.1 hk
    rw [h] at this
    exact absurd (Nat.cast_le.1 this) (by omega)
  · intro h
    refine le_antisymm (firstStationaryIndex_le h.test) ?_
    rw [coe_le_firstStationaryIndex_iff]
    exact fun j hj => not_le.1 (h.not_test_of_lt hj)

/-- If, before `T`, the sequence `y` for `g` is `ε`-stationary whenever `x` for `f` is, then
`min T k_ε(y, g) ≤ k_ε(x, f)`. The two sequences may live in different spaces. -/
theorem min_firstStationaryIndex_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {y : ℕ → F} {g : F → ℝ} {T : ℕ}
    (h : ∀ k < T, ‖fderiv ℝ f (x k)‖ ≤ ε → ‖fderiv ℝ g (y k)‖ ≤ ε) :
    min (T : ℕ∞) (firstStationaryIndex y g ε) ≤ firstStationaryIndex x f ε := by
  rw [le_firstStationaryIndex_iff]
  intro k hk
  rw [lt_min_iff] at hk
  by_contra hle
  have := h k (Nat.cast_lt.1 hk.1) (not_lt.1 hle)
  exact absurd (firstStationaryIndex_le (x := y) this) (not_le.2 hk.2)

end FirstStationary

/-! ### The complexity of a class of methods on a class of functions -/

section Complexity

variable {p : ℕ}

/-- The complexity `#_ε(𝓜, 𝓕) = inf_{M ∈ 𝓜} sup_{f ∈ 𝓕} k_ε(M, f)` of the class of methods `𝓜` on
the class of functions `𝓕` of variable dimension ([cartis2022evaluation], (4.2.2)), in `ℕ∞`. -/
noncomputable def classComplexity (𝓜 : Set (JetMethod p))
    (𝓕 : Set (Σ n, EuclideanSpace ℝ (Fin n) → ℝ)) (ε : ℝ) : ℕ∞ :=
  ⨅ M ∈ 𝓜, ⨆ F ∈ 𝓕, firstStationaryIndex (M.iter F.1 F.2) F.2 ε

variable {𝓜 𝓜' : Set (JetMethod p)} {𝓕 𝓕' : Set (Σ n, EuclideanSpace ℝ (Fin n) → ℝ)} {ε : ℝ}

theorem le_classComplexity_iff {c : ℕ∞} :
    c ≤ classComplexity 𝓜 𝓕 ε ↔
      ∀ M ∈ 𝓜, c ≤ ⨆ F ∈ 𝓕, firstStationaryIndex (M.iter F.1 F.2) F.2 ε := by
  simp only [classComplexity, le_iInf_iff]

/-- `c ≤ #_ε(𝓜, 𝓕)` iff for every method `M ∈ 𝓜` and every `k < c` some `f ∈ 𝓕` has
`k < k_ε(M, f)` (no attainment of the supremum is needed). -/
theorem le_classComplexity_iff_forall_lt {c : ℕ∞} :
    c ≤ classComplexity 𝓜 𝓕 ε ↔
      ∀ M ∈ 𝓜, ∀ k < c, ∃ F ∈ 𝓕, k < firstStationaryIndex (M.iter F.1 F.2) F.2 ε := by
  rw [le_classComplexity_iff]
  refine forall₂_congr fun M _ => ?_
  constructor
  · intro h k hk
    have := hk.trans_le h
    simpa only [lt_iSup_iff, exists_prop] using this
  · intro h
    refine le_of_forall_lt fun k hk => ?_
    obtain ⟨F, hF, hk⟩ := h k hk
    exact hk.trans_le (le_iSup₂ (f := fun F (_ : F ∈ 𝓕) =>
      firstStationaryIndex (M.iter F.1 F.2) F.2 ε) F hF)

theorem le_classComplexity_of_forall_exists {c : ℕ∞}
    (h : ∀ M ∈ 𝓜, ∃ F ∈ 𝓕, c ≤ firstStationaryIndex (M.iter F.1 F.2) F.2 ε) :
    c ≤ classComplexity 𝓜 𝓕 ε := by
  rw [le_classComplexity_iff]
  intro M hM
  obtain ⟨F, hF, hc⟩ := h M hM
  exact hc.trans (le_iSup₂ (f := fun F (_ : F ∈ 𝓕) =>
    firstStationaryIndex (M.iter F.1 F.2) F.2 ε) F hF)

theorem le_classComplexity_singleton_iff {c : ℕ∞} {F : Σ n, EuclideanSpace ℝ (Fin n) → ℝ} :
    c ≤ classComplexity 𝓜 {F} ε ↔ ∀ M ∈ 𝓜, c ≤ firstStationaryIndex (M.iter F.1 F.2) F.2 ε := by
  simp only [le_classComplexity_iff, mem_singleton_iff, iSup_iSup_eq_left]

/-- `#_ε` decreases when the class of methods grows. -/
theorem classComplexity_anti_left (h : 𝓜 ⊆ 𝓜') :
    classComplexity 𝓜' 𝓕 ε ≤ classComplexity 𝓜 𝓕 ε :=
  biInf_mono h

/-- `#_ε` increases when the class of functions grows. -/
theorem classComplexity_mono_right (h : 𝓕 ⊆ 𝓕') :
    classComplexity 𝓜 𝓕 ε ≤ classComplexity 𝓜 𝓕' ε :=
  iInf₂_mono fun _ _ => biSup_mono h

end Complexity

/-! ### Orthogonal embeddings and the class `𝓕(Δ, p)` -/

section Embedding

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The adjoint `Uᵀ : F → E` of a linear isometry `U : E → F` (the book's `Uᵀ` for
`U ∈ O(n̄, n)`). -/
noncomputable def isometryAdjoint (U : E →ₗᵢ[ℝ] F) : F →L[ℝ] E :=
  ContinuousLinearMap.adjoint U.toContinuousLinearMap

variable (U : E →ₗᵢ[ℝ] F)

theorem inner_isometryAdjoint_apply (z : F) (x : E) :
    ⟪isometryAdjoint U z, x⟫_ℝ = ⟪z, U x⟫_ℝ := by
  rw [isometryAdjoint, ContinuousLinearMap.adjoint_inner_left]
  rfl

/-- `Uᵀ U = I`. -/
@[simp]
theorem isometryAdjoint_apply_self (x : E) : isometryAdjoint U (U x) = x := by
  refine ext_inner_right ℝ fun y => ?_
  rw [inner_isometryAdjoint_apply, U.inner_map_map]

theorem isometryAdjoint_surjective : Function.Surjective (isometryAdjoint U) :=
  fun x => ⟨U x, isometryAdjoint_apply_self U x⟩

theorem norm_isometryAdjoint_le : ‖isometryAdjoint U‖ ≤ 1 := by
  rw [isometryAdjoint, ContinuousLinearMap.adjoint.norm_map]
  exact U.norm_toContinuousLinearMap_le

theorem norm_isometryAdjoint_apply_le (z : F) : ‖isometryAdjoint U z‖ ≤ ‖z‖ :=
  by simpa using (isometryAdjoint U).le_of_opNorm_le (norm_isometryAdjoint_le U) z

/-- Composing a continuous multilinear map with `Uᵀ` in every argument preserves its norm. -/
theorem norm_compContinuousLinearMap_isometryAdjoint {q : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) ℝ) :
    ‖A.compContinuousLinearMap fun _ => isometryAdjoint U‖ = ‖A‖ := by
  refine le_antisymm ?_ ?_
  · refine (A.norm_compContinuousLinearMap_le _).trans ?_
    calc ‖A‖ * ∏ _ : Fin q, ‖isometryAdjoint U‖ ≤ ‖A‖ * ∏ _ : Fin q, (1 : ℝ) := by
          gcongr with i; exact norm_isometryAdjoint_le U
      _ = ‖A‖ := by simp
  · refine A.opNorm_le_bound (norm_nonneg _) fun v => ?_
    have h := (A.compContinuousLinearMap fun _ => isometryAdjoint U).le_opNorm (fun i => U (v i))
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      isometryAdjoint_apply_self, LinearIsometry.norm_map] at h
    exact h

/-- The derivatives of `f ∘ Uᵀ` are those of `f` composed with `Uᵀ`. -/
theorem iteratedFDeriv_comp_isometryAdjoint {f : E → ℝ} {N : WithTop ℕ∞} (hf : ContDiff ℝ N f)
    {q : ℕ} (hq : (q : WithTop ℕ∞) ≤ N) (z : F) :
    iteratedFDeriv ℝ q (f ∘ isometryAdjoint U) z =
      (iteratedFDeriv ℝ q f (isometryAdjoint U z)).compContinuousLinearMap
        fun _ => isometryAdjoint U :=
  (isometryAdjoint U).iteratedFDeriv_comp_right hf z hq

theorem norm_iteratedFDeriv_comp_isometryAdjoint {f : E → ℝ} {N : WithTop ℕ∞}
    (hf : ContDiff ℝ N f) {q : ℕ} (hq : (q : WithTop ℕ∞) ≤ N) (z : F) :
    ‖iteratedFDeriv ℝ q (f ∘ isometryAdjoint U) z‖ =
      ‖iteratedFDeriv ℝ q f (isometryAdjoint U z)‖ := by
  rw [iteratedFDeriv_comp_isometryAdjoint U hf hq, norm_compContinuousLinearMap_isometryAdjoint]

/-- `‖∇(f ∘ Uᵀ)(z)‖ = ‖∇f(Uᵀ z)‖`. -/
theorem norm_fderiv_comp_isometryAdjoint {f : E → ℝ} (z : F)
    (hf : DifferentiableAt ℝ f (isometryAdjoint U z)) :
    ‖fderiv ℝ (f ∘ isometryAdjoint U) z‖ = ‖fderiv ℝ f (isometryAdjoint U z)‖ := by
  rw [fderiv_comp z hf (isometryAdjoint U).differentiableAt, ContinuousLinearMap.fderiv]
  refine le_antisymm ?_ ?_
  · calc ‖(fderiv ℝ f (isometryAdjoint U z)).comp (isometryAdjoint U)‖
        ≤ ‖fderiv ℝ f (isometryAdjoint U z)‖ * ‖isometryAdjoint U‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ f (isometryAdjoint U z)‖ * 1 := by
          gcongr; exact norm_isometryAdjoint_le U
      _ = _ := mul_one _
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    have h := ((fderiv ℝ f (isometryAdjoint U z)).comp (isometryAdjoint U)).le_opNorm (U x)
    simpa only [ContinuousLinearMap.comp_apply, isometryAdjoint_apply_self,
      LinearIsometry.norm_map] using h

/-- The range of `f ∘ Uᵀ` is the range of `f`. -/
theorem range_comp_isometryAdjoint (f : E → ℝ) : range (f ∘ isometryAdjoint U) = range f :=
  (isometryAdjoint_surjective U).range_comp f

end Embedding

private theorem sub_compContinuousLinearMap {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {q : ℕ}
    (A B : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) ℝ) (g : G →L[ℝ] E) :
    (A - B).compContinuousLinearMap (fun _ => g) =
      A.compContinuousLinearMap (fun _ => g) - B.compContinuousLinearMap (fun _ => g) := by
  ext v; simp

/-- The class `𝓕(Δ, p)` of [cartis2022evaluation], Section 4.2.1.1, with the Lipschitz constant `L`
of the `p`-th derivative made explicit: functions `f : ℝ^n → ℝ` of any dimension `n` that are
infinitely differentiable (the book's footnote 29), whose `p`-th derivative is `L`-Lipschitz
(f.DpL), which are bounded below (f.Bb) and satisfy `f(0) - inf f ≤ Δ`. -/
def smoothClass (Δ L : ℝ) (p : ℕ) : Set (Σ n, EuclideanSpace ℝ (Fin n) → ℝ) :=
  {F | ContDiff ℝ ∞ F.2 ∧ IteratedFDerivLipschitzOn F.2 p L univ ∧ BddBelow (range F.2) ∧
    F.2 0 - ⨅ x, F.2 x ≤ Δ}

theorem mem_smoothClass {Δ L : ℝ} {p : ℕ} {F : Σ n, EuclideanSpace ℝ (Fin n) → ℝ} :
    F ∈ smoothClass Δ L p ↔ ContDiff ℝ ∞ F.2 ∧ IteratedFDerivLipschitzOn F.2 p L univ ∧
      BddBelow (range F.2) ∧ F.2 0 - ⨅ x, F.2 x ≤ Δ :=
  Iff.rfl

/-- **Orthogonal invariance of `𝓕(Δ, p)`** ([cartis2022evaluation], Section 4.2.1.1, footnote 30).
If `f : ℝ^n → ℝ` is in `𝓕(Δ, p)` and `U : ℝ^n → ℝ^m` is a linear isometry (an `m × n` matrix with
orthonormal columns), then `f_U = f ∘ Uᵀ : ℝ^m → ℝ` is in `𝓕(Δ, p)`. The Lipschitz constant is
assumed nonnegative (for `L < 0` the class only contains functions on `ℝ^0`). -/
theorem comp_adjoint_mem_smoothClass {Δ L : ℝ} {p n m : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hL0 : 0 ≤ L)
    (hf : (⟨n, f⟩ : Σ n, EuclideanSpace ℝ (Fin n) → ℝ) ∈ smoothClass Δ L p)
    (U : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) :
    (⟨m, f ∘ isometryAdjoint U⟩ : Σ n, EuclideanSpace ℝ (Fin n) → ℝ) ∈ smoothClass Δ L p := by
  obtain ⟨hc, hL, hb, hΔ⟩ := hf
  refine ⟨hc.comp (isometryAdjoint U).contDiff, ?_, ?_, ?_⟩
  · intro z _ w _
    dsimp only
    rw [iteratedFDeriv_comp_isometryAdjoint U hc (by exact_mod_cast le_top),
      iteratedFDeriv_comp_isometryAdjoint U hc (by exact_mod_cast le_top),
      ← sub_compContinuousLinearMap,
      norm_compContinuousLinearMap_isometryAdjoint]
    refine (hL _ trivial _ trivial).trans ?_
    rw [Real.rpow_one, Real.rpow_one, ← map_sub]
    exact mul_le_mul_of_nonneg_left (norm_isometryAdjoint_apply_le U _) hL0
  · dsimp only
    rwa [range_comp_isometryAdjoint]
  · dsimp only
    have h1 : (⨅ x, (f ∘ isometryAdjoint U) x) = ⨅ x, f x := by
      rw [← sInf_range, ← sInf_range, range_comp_isometryAdjoint]
    rw [h1, Function.comp_apply, map_zero]
    exact hΔ

/-! ### Null directions of multilinear maps -/

section NullDirection

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {q : ℕ}

/-- `v` is a *null direction* of the multilinear map `A`: `A` vanishes whenever one of its
arguments is `v`. For a derivative tensor `A = ∇^q f(x)` (symmetric) this is the book's
`∇^q f(x) e_j = 0` with `v = e_j` ([cartis2022evaluation], (4.2.1), (4.2.4)); see
`isNullDirection_iff_curryLeft_eq_zero`. -/
def IsNullDirection (A : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) G) (v : E) : Prop :=
  ∀ (i : Fin q) (w : Fin q → E), A (Function.update w i v) = 0

variable {A : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) G} {v v' : E}

theorem isNullDirection_zero : IsNullDirection A 0 :=
  fun i w => A.map_update_zero w i

theorem IsNullDirection.add (hv : IsNullDirection A v) (hv' : IsNullDirection A v') :
    IsNullDirection A (v + v') := fun i w => by
  rw [A.map_update_add, hv i w, hv' i w, add_zero]

theorem IsNullDirection.smul (hv : IsNullDirection A v) (c : ℝ) : IsNullDirection A (c • v) :=
  fun i w => by rw [A.map_update_smul, hv i w, smul_zero]

/-- The null directions of `A` form a submodule. -/
def nullSubmodule (A : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) G) : Submodule ℝ E where
  carrier := {v | IsNullDirection A v}
  add_mem' := IsNullDirection.add
  zero_mem' := isNullDirection_zero
  smul_mem' c _ hv := hv.smul c

@[simp]
theorem mem_nullSubmodule : v ∈ nullSubmodule A ↔ IsNullDirection A v := Iff.rfl

/-- A combination of null directions is a null direction. -/
theorem isNullDirection_of_mem_span {S : Set E} (hS : ∀ u ∈ S, IsNullDirection A u)
    (hv : v ∈ Submodule.span ℝ S) : IsNullDirection A v := by
  have : Submodule.span ℝ S ≤ nullSubmodule A := Submodule.span_le.2 hS
  exact this hv

/-- If all arguments of `A` differ by null directions, the values agree. -/
theorem apply_eq_of_forall_sub_isNullDirection {u w : Fin q → E}
    (h : ∀ i, IsNullDirection A (w i - u i)) : A w = A u := by
  classical
  suffices ∀ s : Finset (Fin q), A (s.piecewise w u) = A u by
    simpa using this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.piecewise_insert]
    have hsi : s.piecewise w u i = u i := Finset.piecewise_eq_of_notMem _ _ _ hi
    have hw : w i = s.piecewise w u i + (w i - u i) := by rw [hsi]; abel
    rw [hw, A.map_update_add, Function.update_eq_self, h i, add_zero, ih]

/-- A null direction of `A` is killed by `A.curryLeft`. -/
theorem IsNullDirection.curryLeft_eq_zero
    {A : ContinuousMultilinearMap ℝ (fun _ : Fin (q + 1) => E) G} (hv : IsNullDirection A v) :
    A.curryLeft v = 0 := by
  ext w
  have := hv 0 (Fin.cons v w)
  rwa [Fin.update_cons_zero, ← ContinuousMultilinearMap.curryLeft_apply] at this

/-- For a symmetric multilinear map (such as a derivative tensor `∇^{q+1} f(x)`), `v` is a null
direction iff `A[v, ·] = 0`, the book's `∇^{q+1} f(x) v = 0`. -/
theorem isNullDirection_iff_curryLeft_eq_zero
    {A : ContinuousMultilinearMap ℝ (fun _ : Fin (q + 1) => E) G}
    (hA : ∀ (σ : Equiv.Perm (Fin (q + 1))) (w : Fin (q + 1) → E), A (w ∘ σ) = A w) :
    IsNullDirection A v ↔ A.curryLeft v = 0 := by
  refine ⟨IsNullDirection.curryLeft_eq_zero, fun h i w => ?_⟩
  have h1 : (Function.update w i v) ∘ Equiv.swap 0 i =
      Fin.cons v (Fin.tail ((Function.update w i v) ∘ Equiv.swap 0 i)) := by
    rw [← Fin.cons_self_tail ((Function.update w i v) ∘ Equiv.swap 0 i)]
    congr 1
    simp
  rw [← hA (Equiv.swap 0 i), h1, ← ContinuousMultilinearMap.curryLeft_apply, h]
  rfl

/-- Composition: if `g v` is a null direction of `A`, then `v` is a null direction of
`A ∘ (g, …, g)`. -/
theorem IsNullDirection.compContinuousLinearMap {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : F →L[ℝ] E} {v : F} (hv : IsNullDirection A (g v)) :
    IsNullDirection (A.compContinuousLinearMap fun _ => g) v := fun i w => by
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have : (fun j => g (Function.update w i v j)) = Function.update (fun j => g (w j)) i (g v) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [this]
  exact hv i _

/-- If `f` agrees near `x` with `f ∘ π` for a linear map `π` with `π v = 0` (`f` does not depend
on the `v`-component near `x`), then `v` is a null direction of every derivative `∇^q f(x)`. -/
theorem isNullDirection_iteratedFDeriv_of_eventuallyEq_comp {f : E → G} {N : WithTop ℕ∞}
    (hf : ContDiff ℝ N f) {x : E} {π : E →L[ℝ] E} (hfx : f =ᶠ[𝓝 x] f ∘ π) (hv : π v = 0)
    (hq : (q : WithTop ℕ∞) ≤ N) : IsNullDirection (iteratedFDeriv ℝ q f x) v := by
  rw [(hfx.iteratedFDeriv ℝ q).eq_of_nhds, π.iteratedFDeriv_comp_right hf x hq]
  refine IsNullDirection.compContinuousLinearMap ?_
  rw [hv]
  exact isNullDirection_zero

end NullDirection

/-! ### Zero-respecting methods -/

section ZeroRespecting

variable {n p : ℕ}

/-- The method `M` on `ℝ^n` is *zero-respecting* for `f` ([cartis2022evaluation], (4.2.1)): it
starts at `x₀ = 0`, and if for every order `q ∈ [1 : p]` and every past iterate `x_i`, `i ≤ k`,
the coordinate vector `e_j` is a null direction of `∇^q f(x_i)`, then `[x_{k+1}]_j = 0`.

For `C^p` functions the derivative tensors are symmetric and the condition is the book's
`∇^q f(x_i) e_j = 0` (`isNullDirection_iff_curryLeft_eq_zero`). In general, "`e_j` is a null
direction of `∇^q f(x_i)`" (the multilinear map vanishes whenever one argument is `e_j`) implies
`∇^q f(x_i) e_j = 0`, so the premise here is stronger and the requirement on the method weaker:
every method that is zero-respecting in the book's sense is zero-respecting here. Hence
`zeroRespectingClass p` contains the book's `𝓜_ZR(p)`, and a lower bound on
`#_ε(zeroRespectingClass p, ·)` implies the same lower bound for `𝓜_ZR(p)`. -/
structure IsZeroRespectingFor
    (M : OracleMethod (EuclideanSpace ℝ (Fin n)) (Jet (EuclideanSpace ℝ (Fin n)) p))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop where
  /-- The initial point is the origin. -/
  x₀_eq_zero : M.x₀ = 0
  /-- Coordinates on which no derivative of order `1, …, p` has been seen stay zero. -/
  iterate_succ_apply_eq_zero : ∀ (k : ℕ) (j : Fin n),
    (∀ q, 1 ≤ q → q ≤ p → ∀ i ≤ k, IsNullDirection
      (iteratedFDeriv ℝ q f (M.iterate (jetOracle f p) i)) (EuclideanSpace.single j 1)) →
    M.iterate (jetOracle f p) (k + 1) j = 0

/-- The class `𝓜_ZR(p)` of zero-respecting `p`-th order methods ([cartis2022evaluation],
Section 4.2.1.2): methods that are zero-respecting for every function in every dimension. -/
def zeroRespectingClass (p : ℕ) : Set (JetMethod p) :=
  {M | ∀ n f, IsZeroRespectingFor (M n) f}

theorem mem_zeroRespectingClass {M : JetMethod p} :
    M ∈ zeroRespectingClass p ↔ ∀ n f, IsZeroRespectingFor (M n) f := Iff.rfl

theorem zeroRespectingClass_subset_methodClass : zeroRespectingClass p ⊆ methodClass p :=
  fun _ hM n => (hM n 0).x₀_eq_zero

/-- The class `𝓜_ZR(p)` is nonempty: the method that stays at `0` is zero-respecting. (So the
infimum in `#_ε(𝓜_ZR(p), 𝓕)` is not over an empty set.) -/
theorem zeroRespectingClass_nonempty : (zeroRespectingClass p).Nonempty :=
  ⟨fun _ => ⟨0, fun _ _ => 0⟩, fun _ _ =>
    ⟨rfl, fun k j _ => by rw [OracleMethod.iterate_succ]; rfl⟩⟩

/-- The class `𝓜(p)` is nonempty. -/
theorem methodClass_nonempty : (methodClass p).Nonempty :=
  zeroRespectingClass_nonempty.mono zeroRespectingClass_subset_methodClass

end ZeroRespecting

/-! ### Zero chains -/

section ZeroChain

variable {n p : ℕ}

/-- `f : ℝ^n → ℝ` is a `p`-th order *zero chain* ([cartis2022evaluation], (4.2.4)): if the
coordinates `j, j+1, …` of `x` vanish (`0`-based), then for every order `q ∈ [1 : p]` the
coordinate vectors `e_i`, `i > j`, are null directions of `∇^q f(x)`. -/
def IsZeroChain (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) : Prop :=
  ∀ (x : EuclideanSpace ℝ (Fin n)) (j : ℕ), (∀ i : Fin n, j ≤ i → x i = 0) →
    ∀ q, 1 ≤ q → q ≤ p → ∀ i : Fin n, j < i →
      IsNullDirection (iteratedFDeriv ℝ q f x) (EuclideanSpace.single i 1)

/-- **Lemma 4.2.1 of [cartis2022evaluation]** (scale invariance of zero chains). If `f` is a
`p`-th order zero chain, `μ₁ : ℝ` and `μ₂ ≠ 0`, then `x ↦ μ₁ f(x / μ₂)` is a `p`-th order zero
chain. -/
theorem IsZeroChain.comp_smul {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsZeroChain f p)
    (μ₁ : ℝ) {μ₂ : ℝ} (hμ₂ : μ₂ ≠ 0) : IsZeroChain (fun x => μ₁ * f (μ₂⁻¹ • x)) p := by
  intro x j hx q hq1 hqp i hji
  -- the dilation as a continuous linear equivalence
  let g : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 μ₂⁻¹ (inv_ne_zero hμ₂))
  have hg : ∀ y, g y = μ₂⁻¹ • y := fun y => rfl
  have hfun : (fun x => μ₁ * f (μ₂⁻¹ • x)) = fun x => μ₁ • (f ∘ g) x := by
    funext y; simp [hg, smul_eq_mul]
  have hcomp : iteratedFDeriv ℝ q (f ∘ g) x =
      (iteratedFDeriv ℝ q f (g x)).compContinuousLinearMap fun _ => (g : _ →L[ℝ] _) := by
    simpa [iteratedFDerivWithin_univ] using
      g.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (mem_univ (g x)) q
  have hnull : IsNullDirection (iteratedFDeriv ℝ q (f ∘ g) x) (EuclideanSpace.single i 1) := by
    rw [hcomp]
    refine IsNullDirection.compContinuousLinearMap ?_
    have h1 : (g : _ →L[ℝ] _) (EuclideanSpace.single i (1 : ℝ)) =
        μ₂⁻¹ • EuclideanSpace.single i (1 : ℝ) := hg _
    rw [h1]
    refine (hf (g x) j (fun i' hi' => ?_) q hq1 hqp i hji).smul _
    rw [hg, PiLp.smul_apply, hx i' hi', smul_zero]
  rw [hfun]
  by_cases hμ₁ : μ₁ = 0
  · subst hμ₁
    simp only [zero_smul]
    rw [iteratedFDeriv_fun_zero]
    intro i w
    rfl
  · let c : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 μ₁ hμ₁)
    have hc : (fun x => μ₁ • (f ∘ g) x) = c ∘ (f ∘ g) := rfl
    rw [hc, c.iteratedFDeriv_comp_left]
    intro i' w
    simp [hnull i' w]

/-- **Lemma 4.2.2 of [cartis2022evaluation]** (Carmon–Duchi–Hinder–Sidford, Observation 1).
A zero-respecting method applied to a
`p`-th order zero chain generates iterates with `[x_k]_j = 0` for all coordinates
`j ≥ k` (`0`-based; the book's `j ∈ [k + 1 : n]`). -/
theorem IsZeroRespectingFor.iterate_apply_eq_zero
    {M : OracleMethod (EuclideanSpace ℝ (Fin n)) (Jet (EuclideanSpace ℝ (Fin n)) p)}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hM : IsZeroRespectingFor M f) (hf : IsZeroChain f p)
    (k : ℕ) (j : Fin n) (hkj : k ≤ j) : M.iterate (jetOracle f p) k j = 0 := by
  induction k using Nat.strong_induction_on generalizing j with
  | _ k ih =>
    rcases k with _ | k
    · simp [hM.x₀_eq_zero]
    · refine hM.iterate_succ_apply_eq_zero k j fun q hq1 hqp i hik => ?_
      exact hf _ i (fun i' hi' => ih i (by omega) i' hi') q hq1 hqp j (by omega)

/-- **Lemma 4.2.3 of [cartis2022evaluation]** (Carmon–Duchi–Hinder–Sidford, Observation 2), for
one method. Let `f : ℝ^n → ℝ` be
a `p`-th order zero chain with `‖∇f(x)‖ > ε` whenever the last coordinate of `x`
vanishes ((4.2.5)). Then a method that is zero-respecting for `f` needs at least `n` iterations to
find an `ε`-stationary point. -/
theorem le_firstStationaryIndex_of_isZeroChain
    {M : OracleMethod (EuclideanSpace ℝ (Fin n)) (Jet (EuclideanSpace ℝ (Fin n)) p)}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {ε : ℝ} (hM : IsZeroRespectingFor M f)
    (hf : IsZeroChain f p)
    (hgrad : ∀ (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n)), x ⟨n - 1, by omega⟩ = 0 →
      ε < ‖fderiv ℝ f x‖) :
    (n : ℕ∞) ≤ firstStationaryIndex (M.iterate (jetOracle f p)) f ε := by
  rw [coe_le_firstStationaryIndex_iff]
  intro k hk
  exact hgrad (by omega) _ (hM.iterate_apply_eq_zero hf k _ (by simp; omega))

/-- **Lemma 4.2.3 of [cartis2022evaluation]**: under the hypotheses of
`le_firstStationaryIndex_of_isZeroChain`, `#_ε(𝓜_ZR(p), {f}) ≥ n`, and so `#_ε(𝓜_ZR(p), 𝓕) ≥ n`
for every class `𝓕` containing `f` (`#_ε` as in (4.2.2)). -/
theorem le_classComplexity_of_isZeroChain {f : EuclideanSpace ℝ (Fin n) → ℝ} {ε : ℝ}
    (hf : IsZeroChain f p)
    (hgrad : ∀ (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n)), x ⟨n - 1, by omega⟩ = 0 →
      ε < ‖fderiv ℝ f x‖)
    {𝓕 : Set (Σ n, EuclideanSpace ℝ (Fin n) → ℝ)} (h𝓕 : ⟨n, f⟩ ∈ 𝓕) :
    (n : ℕ∞) ≤ classComplexity (zeroRespectingClass p) {⟨n, f⟩} ε ∧
      (n : ℕ∞) ≤ classComplexity (zeroRespectingClass p) 𝓕 ε := by
  have h1 : (n : ℕ∞) ≤ classComplexity (zeroRespectingClass p) {⟨n, f⟩} ε :=
    le_classComplexity_singleton_iff.2 fun M hM =>
      le_firstStationaryIndex_of_isZeroChain (hM n f) hf hgrad
  exact ⟨h1, h1.trans (classComplexity_mono_right (singleton_subset_iff.2 h𝓕))⟩

end ZeroChain

end Optimization
