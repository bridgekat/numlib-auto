/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Domain.lean` and `Numlib/Analysis/Sobolev/MultiIndex.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Sobolev.DenyLions

/-!
# The tensor Sobolev seminorm against the multi-index one

`Numlib/Analysis/Sobolev/Domain.lean` measures the derivatives of order `n` of a function of
`W^{k,p}(Ω)` by the `L^p(Ω)` norm of the operator norm of the weak derivative *tensor*
`∂^n f : Ω → E [×n]→L[ℝ] F` (`sobolevSeminorm f n p Ω μ`), while
`Numlib/Analysis/Sobolev/MultiIndex.lean` and `Numlib/Analysis/Sobolev/DenyLions.lean` index the
derivatives by multi-indices `α` of a basis `b` and take the `ℓ^p` sum
`|u|_{k,p,Ω} = (∑_{|α| = k} ‖∂^α u‖_p^p)^{1/p}` (`SobolevMultiIndex.topSeminorm`). On a
finite-dimensional space the two are equivalent, and this file proves the two inequalities with
explicit constants depending on the basis alone:

* `SobolevMultiIndex.sobolevSeminorm_fn_le`: `‖∂^n (fn u)‖_{L^p(Ω)} ≤ C_n ‖u‖_{k,p,Ω}` for
  `u ∈ W^{k,p}(Ω)` and `n ≤ k`, with `C_n = ∑_{m : Fin n → ι} ‖basisCoordProd b m‖`: the tensor
  is determined by its values on tuples of basis vectors, which are the `∂^α`
  (`ContinuousMultilinearMap.norm_le_sum_norm_basisCoordProd_mul`);
* `SobolevMultiIndex.ofReal_topSeminorm_le_sobolevSeminorm`:
  `|u|_{k,p,Ω} ≤ C'_k ‖∂^k (fn u)‖_{L^p(Ω)}`, with `C'_k = ∑_{|α| = k} ∏_j ‖(e_α)_j‖`: each
  `∂^α u` is the tensor evaluated at the tuple `e_α` naming `α`.

For the standard basis of `ℝ^N` both constants are counts of multi-indices, `N^n` and
`#{|α| = k}`. The file also carries the algebra of `sobolevSeminorm` on `W^{k,p}(Ω)` that the
finite element interpolation estimates of `[han2009theoretical]` §10.3 use: invariance under
almost-everywhere equality, finiteness, the triangle inequality, homogeneity, and the bound for
a finite linear combination.

## Main results

* `sobolevSeminorm_congr_ae`, `MemSobolev.sobolevSeminorm_ne_top`, `sobolevSeminorm_add_le`,
  `sobolevSeminorm_sub_le`, `sobolevSeminorm_const_smul`, `sobolevSeminorm_sum_smul_le`,
  `MemSobolev.finsetSum`: the algebra of the tensor seminorm on `W^{k,p}(Ω)`;
  `MemSobolev.sobolevNorm_le_sum_sobolevSeminorm`: the norm is at most the sum of the seminorms
  of all orders.
* `SobolevMultiIndex.weakDeriv_ae_eq_weakIteratedFDeriv_apply`: `∂^α u` is the tensor
  derivative of order `|α|` of `fn u` evaluated at the tuple naming `α`, almost everywhere; and
  `SobolevMultiIndex.weakDeriv_multiIndexCount_ae_eq` for an arbitrary tuple of basis vectors,
  through the symmetry of the weak derivative in its directions.
* `SobolevMultiIndex.sobolevSeminorm_fn_le`,
  `SobolevMultiIndex.ofReal_topSeminorm_le_sobolevSeminorm` (and its real form
  `SobolevMultiIndex.topSeminorm_le_mul_toReal_sobolevSeminorm`): the two comparisons.

## References

`[han2009theoretical]` Definition 7.2.2 and §7.3.5 (the seminorm `|·|_{k,p,Ω}`); the equivalence
is the remark that on `ℝ^d` the operator norm of a symmetric tensor is comparable to any norm
on its finitely many entries.
-/

open Filter MeasureTheory Module Set TopologicalSpace

open scoped ENNReal NNReal

noncomputable section

/-! ### The algebra of the tensor seminorm on `W^{k,p}(Ω)` -/

section Algebra

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {Ω : Opens E} {μ : Measure E} {k : ℕ} {p : ℝ≥0∞} {f g : E → F}

/-- The Sobolev seminorm only sees the function up to a null set of `Ω`: the chosen weak
derivatives of two almost everywhere equal functions are almost everywhere equal, or both
absent. -/
theorem sobolevSeminorm_congr_ae (hfg : f =ᵐ[μ.restrict (Ω : Set E)] g) :
    sobolevSeminorm f k p Ω μ = sobolevSeminorm g k p Ω μ := by
  by_cases h : ∃ w, HasWeakIteratedFDerivOn k f w Ω μ
  · obtain ⟨w, hw⟩ := h
    unfold sobolevSeminorm
    rw [eLpNorm_congr_ae
        ((ae_restrict_iff' Ω.isOpen.measurableSet).2 hw.weakIteratedFDeriv_ae_eq),
      eLpNorm_congr_ae ((ae_restrict_iff' Ω.isOpen.measurableSet).2
        (hw.congr_ae hfg (Filter.EventuallyEq.refl _ _)).weakIteratedFDeriv_ae_eq)]
  · have h' : ¬ ∃ w, HasWeakIteratedFDerivOn k g w Ω μ := fun ⟨w, hw⟩ ↦
      h ⟨w, hw.congr_ae hfg.symm (Filter.EventuallyEq.refl _ _)⟩
    simp only [sobolevSeminorm, weakIteratedFDeriv, dite_eq_right h, dite_eq_right h']

/-- The Sobolev seminorm of a function of `W^{k,p}(Ω)` is finite. -/
theorem MemSobolev.sobolevSeminorm_ne_top (hf : MemSobolev f k p Ω μ) :
    sobolevSeminorm f k p Ω μ ≠ ⊤ :=
  (hf.memLp_weakIteratedFDeriv le_rfl).eLpNorm_ne_top

/-- The Sobolev seminorm of a function of `W^{k,p}(Ω)` is finite. -/
theorem MemSobolev.sobolevSeminorm_lt_top (hf : MemSobolev f k p Ω μ) :
    sobolevSeminorm f k p Ω μ < ⊤ :=
  lt_top_iff_ne_top.2 hf.sobolevSeminorm_ne_top

/-- **The triangle inequality for the Sobolev seminorm** on `W^{k,p}(Ω)`, `1 ≤ p`. -/
theorem sobolevSeminorm_add_le (hp : 1 ≤ p) (hf : MemSobolev f k p Ω μ)
    (hg : MemSobolev g k p Ω μ) :
    sobolevSeminorm (f + g) k p Ω μ ≤ sobolevSeminorm f k p Ω μ + sobolevSeminorm g k p Ω μ := by
  have hw := (hf.hasWeakIteratedFDerivOn le_rfl).add (hg.hasWeakIteratedFDerivOn le_rfl)
  unfold sobolevSeminorm
  rw [hw.eLpNorm_weakIteratedFDeriv]
  exact eLpNorm_add_le_of_norm hp

/-- **The triangle inequality for the Sobolev seminorm of a difference** on `W^{k,p}(Ω)`,
`1 ≤ p`. -/
theorem sobolevSeminorm_sub_le (hp : 1 ≤ p) (hf : MemSobolev f k p Ω μ)
    (hg : MemSobolev g k p Ω μ) :
    sobolevSeminorm (f - g) k p Ω μ ≤ sobolevSeminorm f k p Ω μ + sobolevSeminorm g k p Ω μ := by
  have hw := (hf.hasWeakIteratedFDerivOn le_rfl).sub (hg.hasWeakIteratedFDerivOn le_rfl)
  unfold sobolevSeminorm
  rw [hw.eLpNorm_weakIteratedFDeriv]
  exact eLpNorm_sub_le_of_norm hp

/-- **Homogeneity of the Sobolev seminorm** on `W^{k,p}(Ω)`. -/
theorem sobolevSeminorm_const_smul (hf : MemSobolev f k p Ω μ) (c : ℝ) :
    sobolevSeminorm (c • f) k p Ω μ = ‖c‖ₑ * sobolevSeminorm f k p Ω μ := by
  have hw := (hf.hasWeakIteratedFDerivOn le_rfl).const_smul c
  unfold sobolevSeminorm
  rw [hw.eLpNorm_weakIteratedFDeriv, eLpNorm_const_smul]

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
/-- `W^{k,p}(Ω)` is closed under finite sums. -/
theorem MemSobolev.finsetSum [OpensMeasurableSpace E] {ι : Type*} {s : Finset ι} {f : ι → E → F}
    (hf : ∀ i ∈ s, MemSobolev (f i) k p Ω μ) : MemSobolev (∑ i ∈ s, f i) k p Ω μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using memSobolev_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- **The Sobolev seminorm of a finite linear combination** of functions of `W^{k,p}(Ω)`,
`1 ≤ p`, is bounded by the combination of their seminorms with the absolute values of the
coefficients. -/
theorem sobolevSeminorm_sum_smul_le (hp : 1 ≤ p) {ι : Type*} {s : Finset ι} {f : ι → E → F}
    (hf : ∀ i ∈ s, MemSobolev (f i) k p Ω μ) (c : ι → ℝ) :
    sobolevSeminorm (∑ i ∈ s, c i • f i) k p Ω μ
      ≤ ∑ i ∈ s, ‖c i‖ₑ * sobolevSeminorm (f i) k p Ω μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have hw : HasWeakIteratedFDerivOn k (0 : E → F) 0 Ω μ := HasWeakIteratedFDerivOn.zero
    unfold sobolevSeminorm
    rw [hw.eLpNorm_weakIteratedFDeriv, eLpNorm_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hmem : MemSobolev (∑ i ∈ s, c i • f i) k p Ω μ :=
      MemSobolev.finsetSum fun i hi ↦ (hf i (Finset.mem_insert_of_mem hi)).const_smul (c i)
    refine (sobolevSeminorm_add_le hp ((hf a (Finset.mem_insert_self a s)).const_smul (c a))
      hmem).trans ?_
    rw [sobolevSeminorm_const_smul (hf a (Finset.mem_insert_self a s))]
    exact add_le_add le_rfl (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- **The Sobolev norm is at most the sum of the seminorms of all orders**, `1 ≤ p < ∞`:
`‖f‖_{k,p,Ω} = (∑_{n ≤ k} |f|_{n,p,Ω}^p)^{1/p} ≤ ∑_{n ≤ k} |f|_{n,p,Ω}` (the `ℓ^p` norm is at
most the `ℓ^1` norm, `Real.rpow_sum_rpow_le_sum`). -/
theorem MemSobolev.sobolevNorm_le_sum_sobolevSeminorm [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hf : MemSobolev f k p Ω μ) :
    sobolevNorm f k p Ω μ ≤ ∑ n : Fin (k + 1), sobolevSeminorm f n p Ω μ := by
  have hfin : ∀ n : Fin (k + 1), sobolevSeminorm f n p Ω μ ≠ ⊤ := fun n ↦
    (hf.mono_order (by exact_mod_cast Nat.lt_succ_iff.1 n.2)).sobolevSeminorm_ne_top
  have hP : 0 ≤ p.toReal := ENNReal.toReal_nonneg
  have key : ∀ n : Fin (k + 1), eLpNorm (weakIteratedFDeriv n f Ω μ) p (μ.restrict (Ω : Set E))
      = ENNReal.ofReal (sobolevSeminorm f n p Ω μ).toReal := fun n ↦
    (ENNReal.ofReal_toReal (hfin n)).symm
  simp only [sobolevNorm, hp, ↓reduceIte]
  simp_rw [key]
  calc (∑ n : Fin (k + 1), ENNReal.ofReal (sobolevSeminorm f n p Ω μ).toReal ^ p.toReal)
        ^ (1 / p.toReal)
      = ENNReal.ofReal ((∑ n : Fin (k + 1), (sobolevSeminorm f n p Ω μ).toReal ^ p.toReal)
          ^ (1 / p.toReal)) := by
        rw [← ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun _ _ ↦ by positivity)
          (by positivity), ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ by positivity]
        congr 1
        exact Finset.sum_congr rfl fun n _ ↦
          ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hP
    _ ≤ ENNReal.ofReal (∑ n : Fin (k + 1), (sobolevSeminorm f n p Ω μ).toReal) :=
        ENNReal.ofReal_le_ofReal
          (Real.rpow_sum_rpow_le_sum (fun _ ↦ ENNReal.toReal_nonneg) hp)
    _ = ∑ n : Fin (k + 1), sobolevSeminorm f n p Ω μ := by
        rw [ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ ENNReal.toReal_nonneg]
        exact Finset.sum_congr rfl fun n _ ↦ ENNReal.ofReal_toReal (hfin n)

end Algebra

/-! ### A continuous multilinear map is bounded by its values on tuples of basis vectors -/

section Multilinear

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {ι : Type*} [Fintype ι]

/-- **A continuous multilinear map is bounded by its values on tuples of basis vectors**:
`‖T‖ ≤ ∑_m ‖basisCoordProd b m‖ ‖T (b ∘ m)‖`, the sum over the tuples `m : Fin n → ι`, by the
expansion `ContinuousMultilinearMap.apply_eq_sum_basis`. -/
theorem ContinuousMultilinearMap.norm_le_sum_norm_basisCoordProd_mul (b : Basis ι ℝ E) {n : ℕ}
    (T : E [×n]→L[ℝ] G) :
    ‖T‖ ≤ ∑ m : Fin n → ι, ‖basisCoordProd b m‖ * ‖T fun j ↦ b (m j)‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (Finset.sum_nonneg fun _ _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun y ↦ ?_
  rw [ContinuousMultilinearMap.apply_eq_sum_basis b T y, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ ↦ ?_)
  rw [norm_smul, ← basisCoordProd_apply, mul_assoc, mul_comm ‖T fun j ↦ b (m j)‖,
    ← mul_assoc]
  exact mul_le_mul_of_nonneg_right ((basisCoordProd b m).le_opNorm y) (norm_nonneg _)

end Multilinear

/-! ### The comparison of the two seminorms -/

section Compare

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E}

namespace SobolevMultiIndex

omit [FiniteDimensional ℝ E] [CompleteSpace F] [Fact (1 ≤ p)] in
/-- The function of an element of `W^{k,p}(Ω)` lies in `W^{k,p}(Ω)` in the tensor formulation. -/
theorem memSobolev_fn (u : SobolevMultiIndex F b k p Ω μ) : MemSobolev (fn u) k p Ω μ :=
  (memSobolevMultiIndex u).memSobolev

omit [Fact (1 ≤ p)] in
/-- **`∂^α u` is the tensor derivative of order `|α|` of `fn u` evaluated at the tuple naming
`α`**, almost everywhere on `Ω`. -/
theorem weakDeriv_ae_eq_weakIteratedFDeriv_apply (u : SobolevMultiIndex F b k p Ω μ)
    (α : MultiIndexLE ι k) :
    (weakDeriv u α : E → F) =ᵐ[μ.restrict (Ω : Set E)]
      fun x ↦ weakIteratedFDeriv (∑ i, α.1 i) (fn u) Ω μ x (multiIndexTuple (b : ι → E) α.1) := by
  have h1 := hasWeakIteratedLineDerivOn u α
  have h2 := ((memSobolev_fn u).hasWeakIteratedFDerivOn α.2).lineDeriv
    (multiIndexTuple (b : ι → E) α.1)
  exact (ae_restrict_iff' Ω.isOpen.measurableSet).2 (h1.ae_eq h2)

omit [Fact (1 ≤ p)] in
/-- **The tensor derivative of order `n` of `fn u` evaluated at an arbitrary tuple of basis
vectors is a weak derivative `∂^α u`**, for the multi-index `α` counting the occurrences of each
index in the tuple: the weak derivative is symmetric in its directions. -/
theorem weakDeriv_multiIndexCount_ae_eq (u : SobolevMultiIndex F b k p Ω μ) {n : ℕ} (hn : n ≤ k)
    (m : Fin n → ι) :
    (weakDeriv u ⟨multiIndexCount m, (sum_multiIndexCount m).le.trans hn⟩ : E → F)
      =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ weakIteratedFDeriv n (fn u) Ω μ x fun j ↦ b (m j) := by
  have hperm : (List.ofFn (multiIndexTuple (b : ι → E) (multiIndexCount m))).Perm
      (List.ofFn fun j ↦ b (m j)) := by
    rw [← multiIndexDirections_eq_ofFn]
    exact (multiIndexDirections_multiIndexCount_perm (b : ι → E) m).symm
  have h1 := (hasWeakIteratedLineDerivOn u ⟨multiIndexCount m,
    (sum_multiIndexCount m).le.trans hn⟩).of_perm hperm
  have h2 := ((memSobolev_fn u).hasWeakIteratedFDerivOn hn).lineDeriv fun j ↦ b (m j)
  exact (ae_restrict_iff' Ω.isOpen.measurableSet).2 (h1.ae_eq h2)

omit [FiniteDimensional ℝ E] [CompleteSpace F] [Fact (1 ≤ p)] in
/-- The `L^p(Ω)` norm of a weak derivative `∂^α u`, as an extended real, is its norm in
`L^p(Ω)`. -/
theorem eLpNorm_weakDeriv (u : SobolevMultiIndex F b k p Ω μ) (α : MultiIndexLE ι k) :
    eLpNorm (weakDeriv u α) p (μ.restrict (Ω : Set E)) = ENNReal.ofReal ‖weakDeriv u α‖ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]

/-- **The tensor seminorm is bounded by the multi-index norm**: for `u ∈ W^{k,p}(Ω)` and
`n ≤ k`, `‖∂^n (fn u)‖_{L^p(Ω)} ≤ (∑_{m : Fin n → ι} ‖basisCoordProd b m‖) ‖u‖_{k,p,Ω}`. The
tensor `∂^n (fn u)(x)` is bounded by its values on the tuples of basis vectors
(`ContinuousMultilinearMap.norm_le_sum_norm_basisCoordProd_mul`), which are the `∂^α u (x)`
(`weakDeriv_multiIndexCount_ae_eq`), each of `L^p(Ω)` norm at most `‖u‖`. -/
theorem sobolevSeminorm_fn_le (u : SobolevMultiIndex F b k p Ω μ) {n : ℕ} (hn : n ≤ k) :
    sobolevSeminorm (fn u) n p Ω μ
      ≤ ENNReal.ofReal (∑ m : Fin n → ι, ‖basisCoordProd b m‖) * ENNReal.ofReal ‖u‖ := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hae : ∀ᵐ x ∂μ.restrict (Ω : Set E), ‖weakIteratedFDeriv n (fn u) Ω μ x‖
      ≤ ∑ m : Fin n → ι, ‖basisCoordProd b m‖
        * ‖weakDeriv u ⟨multiIndexCount m, (sum_multiIndexCount m).le.trans hn⟩ x‖ := by
    filter_upwards [ae_all_iff.2 fun m : Fin n → ι ↦ weakDeriv_multiIndexCount_ae_eq u hn m]
      with x hx
    refine (ContinuousMultilinearMap.norm_le_sum_norm_basisCoordProd_mul b _).trans
      (Finset.sum_le_sum fun m _ ↦ ?_)
    rw [hx m]
  calc sobolevSeminorm (fn u) n p Ω μ
      ≤ eLpNorm (fun x ↦ ∑ m : Fin n → ι, ‖basisCoordProd b m‖
          * ‖weakDeriv u ⟨multiIndexCount m, (sum_multiIndexCount m).le.trans hn⟩ x‖) p
          (μ.restrict (Ω : Set E)) :=
        eLpNorm_mono_ae_real ((memSobolev_fn u).memLp_weakIteratedFDeriv hn).aestronglyMeasurable
          hae
    _ ≤ ∑ m : Fin n → ι, eLpNorm (fun x ↦ ‖basisCoordProd b m‖
          * ‖weakDeriv u ⟨multiIndexCount m, (sum_multiIndexCount m).le.trans hn⟩ x‖) p
          (μ.restrict (Ω : Set E)) := by
        have heq : (fun x ↦ ∑ m : Fin n → ι, ‖basisCoordProd b m‖
            * ‖weakDeriv u ⟨multiIndexCount m, (sum_multiIndexCount m).le.trans hn⟩ x‖)
            = ∑ m : Fin n → ι, fun x ↦ ‖basisCoordProd b m‖
              * ‖weakDeriv u ⟨multiIndexCount m, (sum_multiIndexCount m).le.trans hn⟩ x‖ := by
          funext x
          simp
        rw [heq]
        exact eLpNorm_sum_le_of_norm hp
    _ ≤ ∑ m : Fin n → ι, ENNReal.ofReal ‖basisCoordProd b m‖ * ENNReal.ofReal ‖u‖ := by
        refine Finset.sum_le_sum fun m _ ↦ ?_
        have hsmul : (fun x ↦ ‖basisCoordProd b m‖
            * ‖weakDeriv u ⟨multiIndexCount m, (sum_multiIndexCount m).le.trans hn⟩ x‖)
            = ‖basisCoordProd b m‖ • fun x ↦
              ‖weakDeriv u ⟨multiIndexCount m, (sum_multiIndexCount m).le.trans hn⟩ x‖ := by
          funext x
          simp
        rw [hsmul, eLpNorm_const_smul, Real.enorm_of_nonneg (norm_nonneg _),
          eLpNorm_norm _ (Lp.memLp _).aestronglyMeasurable, eLpNorm_weakDeriv]
        gcongr
        exact norm_weakDeriv_le u _
    _ = ENNReal.ofReal (∑ m : Fin n → ι, ‖basisCoordProd b m‖) * ENNReal.ofReal ‖u‖ := by
        rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ norm_nonneg _]

/-- **The multi-index top seminorm is bounded by the tensor seminorm**: for `u ∈ W^{k,p}(Ω)`,
`|u|_{k,p,Ω} ≤ (∑_{|α| = k} ∏_j ‖(e_α)_j‖) ‖∂^k (fn u)‖_{L^p(Ω)}`, where `e_α` is the tuple of
basis vectors naming `α`: `|u|_{k,p,Ω} ≤ ∑_{|α| = k} ‖∂^α u‖_p` (`PiLp.norm_le_sum_norm`) and
`∂^α u (x) = ∂^k (fn u)(x)(e_α)` has norm at most `‖∂^k (fn u)(x)‖ ∏_j ‖(e_α)_j‖`. -/
theorem ofReal_topSeminorm_le_sobolevSeminorm (u : SobolevMultiIndex F b k p Ω μ) :
    ENNReal.ofReal (topSeminorm F b k p Ω μ u)
      ≤ ENNReal.ofReal (∑ α : MultiIndexEq ι k, ∏ j, ‖multiIndexTuple (b : ι → E) α.1.1 j‖)
        * sobolevSeminorm (fn u) k p Ω μ := by
  have hterm : ∀ α : MultiIndexEq ι k, ENNReal.ofReal ‖weakDeriv u α.1‖
      ≤ ENNReal.ofReal (∏ j, ‖multiIndexTuple (b : ι → E) α.1.1 j‖)
        * sobolevSeminorm (fn u) k p Ω μ := by
    intro α
    rw [← eLpNorm_weakDeriv,
      eLpNorm_congr_ae (weakDeriv_ae_eq_weakIteratedFDeriv_apply u α.1)]
    have hae : ∀ᵐ x ∂μ.restrict (Ω : Set E),
        ‖weakIteratedFDeriv (∑ i, α.1.1 i) (fn u) Ω μ x (multiIndexTuple (b : ι → E) α.1.1)‖
          ≤ (∏ j, ‖multiIndexTuple (b : ι → E) α.1.1 j‖)
            * ‖weakIteratedFDeriv (∑ i, α.1.1 i) (fn u) Ω μ x‖ :=
      Eventually.of_forall fun x ↦ by
        rw [mul_comm]
        exact ContinuousMultilinearMap.le_opNorm _ _
    have hmeas : AEStronglyMeasurable (fun x ↦ weakIteratedFDeriv (∑ i, α.1.1 i) (fn u) Ω μ x
        (multiIndexTuple (b : ι → E) α.1.1)) (μ.restrict (Ω : Set E)) :=
      ((ContinuousMultilinearMap.apply ℝ (fun _ ↦ E) F
        (multiIndexTuple (b : ι → E) α.1.1)).comp_memLp'
        ((memSobolev_fn u).memLp_weakIteratedFDeriv α.1.2)).aestronglyMeasurable
    refine (eLpNorm_mono_ae_real hmeas hae).trans (le_of_eq ?_)
    have hsmul : (fun x ↦ (∏ j, ‖multiIndexTuple (b : ι → E) α.1.1 j‖)
        * ‖weakIteratedFDeriv (∑ i, α.1.1 i) (fn u) Ω μ x‖)
        = (∏ j, ‖multiIndexTuple (b : ι → E) α.1.1 j‖)
          • fun x ↦ ‖weakIteratedFDeriv (∑ i, α.1.1 i) (fn u) Ω μ x‖ := by
      funext x
      simp
    rw [hsmul, eLpNorm_const_smul,
      Real.enorm_of_nonneg (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)]
    have key : ∀ n, n = k → eLpNorm (fun x ↦ ‖weakIteratedFDeriv n (fn u) Ω μ x‖) p
        (μ.restrict (Ω : Set E)) = sobolevSeminorm (fn u) k p Ω μ := by
      rintro n rfl
      exact eLpNorm_norm _
        ((memSobolev_fn u).memLp_weakIteratedFDeriv le_rfl).aestronglyMeasurable
    rw [key _ α.2]
  calc ENNReal.ofReal (topSeminorm F b k p Ω μ u)
      ≤ ENNReal.ofReal (∑ α : MultiIndexEq ι k, ‖weakDeriv u α.1‖) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [topSeminorm_apply, topDeriv]
        exact PiLp.norm_le_sum_norm _
    _ = ∑ α : MultiIndexEq ι k, ENNReal.ofReal ‖weakDeriv u α.1‖ :=
        ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ norm_nonneg _
    _ ≤ ∑ α : MultiIndexEq ι k, ENNReal.ofReal (∏ j, ‖multiIndexTuple (b : ι → E) α.1.1 j‖)
          * sobolevSeminorm (fn u) k p Ω μ := Finset.sum_le_sum fun α _ ↦ hterm α
    _ = _ := by
        rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun _ _ ↦
          Finset.prod_nonneg fun _ _ ↦ norm_nonneg _]

/-- `SobolevMultiIndex.ofReal_topSeminorm_le_sobolevSeminorm` with real constants:
`|u|_{k,p,Ω} ≤ C'_k ‖∂^k (fn u)‖_{L^p(Ω)}`, the right-hand side finite. -/
theorem topSeminorm_le_mul_toReal_sobolevSeminorm (u : SobolevMultiIndex F b k p Ω μ) :
    topSeminorm F b k p Ω μ u
      ≤ (∑ α : MultiIndexEq ι k, ∏ j, ‖multiIndexTuple (b : ι → E) α.1.1 j‖)
        * (sobolevSeminorm (fn u) k p Ω μ).toReal := by
  have hfin : sobolevSeminorm (fn u) k p Ω μ ≠ ⊤ := (memSobolev_fn u).sobolevSeminorm_ne_top
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)
    (ofReal_topSeminorm_le_sobolevSeminorm u)
  rwa [ENNReal.toReal_ofReal (apply_nonneg _ _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)] at h

end SobolevMultiIndex

end Compare

end
