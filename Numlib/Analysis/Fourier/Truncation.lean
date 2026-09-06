import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Approximation.BestApprox

/-!
# The Fourier truncation projection on `L²` of the circle

The truncation of a Fourier series to the frequencies of absolute value at most `n` is the
orthogonal projection of `L²(AddCircle T)` onto the trigonometric polynomials of that degree. This
file packages it as a bounded operator, so that it can be fed to the projection method framework:
it is idempotent, of norm at most one, and it converges pointwise to the identity.

The Fourier–Galerkin method for an integral equation on the circle is the projection method for
this family, and the two facts a projection method asks for — uniform boundedness of the
projections and their pointwise convergence — are exactly the last two results below.

## Main definitions

* `trigPolyLp T n` is the subspace of `L²` spanned by the members of the real trigonometric system
  of index at most `n` in absolute value; it is the image in `L²` of the space `trigPolyLE T n` of
  continuous trigonometric polynomials.
* `trigProjCLM T n` is the orthogonal projection onto it, the Fourier truncation `P_n`.

## Main results

* `isIdempotentElem_trigProjCLM` and `norm_trigProjCLM_le_one`: `P_n` is a projection of norm at
  most one, so the family is uniformly bounded — with no Lebesgue constant, unlike the truncation
  read on the *continuous* functions, whose norm grows like `log n`.
* `tendsto_trigProjCLM`: `P_n f → f` in `L²` for every `f`, which is Parseval's identity read
  along the symmetric blocks of frequencies.

## References

The `L²` convergence of Fourier series is [han2009theoretical] Example 1.3.15, and the projection
method that consumes these facts is [han2009theoretical] §12.2.4 and §13.3.1.
-/

open AddCircle Filter MeasureTheory Submodule Topology

open scoped Real

variable {T : ℝ} [hT : Fact (0 < T)] {n : ℕ}

/-- **The trigonometric polynomials of degree at most `n` in `L²`**: the span of the members
`trigLp T m` of the real trigonometric system with `|m| ≤ n`. It is the `L²` counterpart of
`trigPolyLE`, and is `2 n + 1`-dimensional. -/
noncomputable def trigPolyLp (T : ℝ) [hT : Fact (0 < T)] (n : ℕ) :
    Submodule ℝ (Lp ℝ 2 (@haarAddCircle T hT)) :=
  span ℝ (trigLp T '' Set.Icc (-(n : ℤ)) n)

instance : FiniteDimensional ℝ (trigPolyLp T n) :=
  FiniteDimensional.span_of_finite ℝ ((Set.finite_Icc _ _).image _)

instance : (trigPolyLp T n).HasOrthogonalProjection :=
  HasOrthogonalProjection.ofCompleteSpace _

/-- Each member of the real trigonometric system of index at most `n` in absolute value is a
trigonometric polynomial of degree at most `n`. -/
theorem trigLp_mem_trigPolyLp {m : ℤ} (hm : m ∈ Finset.Icc (-(n : ℤ)) n) :
    trigLp T m ∈ trigPolyLp T n :=
  subset_span ⟨m, Set.mem_Icc.2 (Finset.mem_Icc.1 hm), rfl⟩

/-- The Fourier partial sum of an `L²` function is a trigonometric polynomial of degree at most
`n`. -/
theorem trigPartialSum_mem_trigPolyLp (n : ℕ) (f : Lp ℝ 2 (@haarAddCircle T hT)) :
    trigPartialSum n f ∈ trigPolyLp T n :=
  sum_mem fun _ hm => Submodule.smul_mem _ _ (trigLp_mem_trigPolyLp hm)

/-- **The Fourier truncation `P_n` on `L²` of the circle**: the orthogonal projection onto the
trigonometric polynomials of degree at most `n`.  It agrees with the partial sum
`trigPartialSum n`, which is what makes it computable from the Fourier coefficients; what is used
below is only that it is an orthogonal projection onto a space containing that partial sum. -/
noncomputable def trigProjCLM (T : ℝ) [hT : Fact (0 < T)] (n : ℕ) :
    Lp ℝ 2 (@haarAddCircle T hT) →L[ℝ] Lp ℝ 2 (@haarAddCircle T hT) :=
  (trigPolyLp T n).starProjection

/-- The Fourier truncation is a projection. -/
theorem isIdempotentElem_trigProjCLM (T : ℝ) [hT : Fact (0 < T)] (n : ℕ) :
    IsIdempotentElem (trigProjCLM T n) :=
  isIdempotentElem_starProjection _

/-- **The Fourier truncation has norm at most one on `L²`.**  It is an orthogonal projection, so
the family `P_n` is uniformly bounded for free — in contrast with the same truncation read on the
continuous periodic functions, whose norm is the Lebesgue constant `O(log n)`. -/
theorem norm_trigProjCLM_le_one (T : ℝ) [hT : Fact (0 < T)] (n : ℕ) : ‖trigProjCLM T n‖ ≤ 1 :=
  starProjection_norm_le _

/-- The symmetric blocks of frequencies are cofinal among the finite sets of integers. -/
private theorem tendsto_finset_Icc_neg_atTop :
    Tendsto (fun n : ℕ => Finset.Icc (-(n : ℤ)) (n : ℤ)) atTop atTop := by
  refine tendsto_atTop_finset_of_monotone (fun p q hpq m hm => ?_) fun m => ⟨m.natAbs, ?_⟩
  · rw [Finset.mem_Icc] at hm ⊢
    exact ⟨le_trans (neg_le_neg (Nat.cast_le.2 hpq)) hm.1, hm.2.trans (Nat.cast_le.2 hpq)⟩
  · rw [Finset.mem_Icc]
    omega

/-- The `L²` error of the Fourier partial sum tends to zero: this is Parseval's identity read along
the symmetric blocks of frequencies. -/
theorem tendsto_norm_sub_trigPartialSum (f : Lp ℝ 2 (@haarAddCircle T hT)) :
    Tendsto (fun n => ‖f - trigPartialSum n f‖) atTop (𝓝 0) := by
  have hpart : Tendsto (fun n : ℕ => ∑ m ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
      realFourierCoeff (f : AddCircle T → ℝ) m ^ 2) atTop (𝓝 (‖f‖ ^ 2)) :=
    (hasSum_sq_realFourierCoeff f).comp tendsto_finset_Icc_neg_atTop
  have hsq : Tendsto (fun n => ‖f - trigPartialSum n f‖ ^ 2) atTop (𝓝 0) := by
    have := tendsto_const_nhds (x := ‖f‖ ^ 2) (f := atTop (α := ℕ)) |>.sub hpart
    rw [sub_self] at this
    exact this.congr fun n => (norm_sub_trigPartialSum_sq n f).symm
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using
    (Real.continuous_sqrt.tendsto 0).comp hsq

/-- **The Fourier truncations converge pointwise to the identity on `L²`.**  Together with
`norm_trigProjCLM_le_one` this is everything a projection method asks of the family `P_n`.

The orthogonal projection is at least as good as the partial sum, which lies in the same subspace,
so the bound is the `L²` truncation error of the Fourier series. -/
theorem tendsto_trigProjCLM (f : Lp ℝ 2 (@haarAddCircle T hT)) :
    Tendsto (fun n => trigProjCLM T n f) atTop (𝓝 f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (tendsto_norm_sub_trigPartialSum f)
  rw [norm_sub_rev]
  exact (isBestApprox_starProjection (trigPolyLp T n) f).2 _
    (trigPartialSum_mem_trigPolyLp n f)
