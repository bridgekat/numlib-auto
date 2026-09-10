import Mathlib.Analysis.Distribution.Sobolev
import Numlib.Analysis.Sobolev.Tempered
import NumlibSurface.AtkinsonHan.Chapter07.Section03

/-!
# Atkinson–Han §7.4: the Fourier characterization of `H^k(ℝ^d)`

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §7.4.

Theorem 7.4.1 is here, in the two readings of Definition 7.2.2 that the chapter carries.
`theorem_7_4_1_complex` is the statement for the complex-valued functions that §7.4 allows
throughout ("All the functions in this section are allowed to be complex-valued"): an
`L^2(ℝ^d)` function lies in `W^{k,2}(ℝ^d)`, cut out by the weak derivatives `∂^α v` of order
`|α| ≤ k`, exactly when `(1 + |ξ|^2)^{k/2} ℱv` lies in `L^2(ℝ^d)`. `theorem_7_4_1` is the same
statement for a real-valued `v`, phrased over `definition_7_2_2_multiIndex`, with `ℱv` the Fourier
transform of the complexification of `v`. Both come from the backbone bridge of
`Numlib/Analysis/Sobolev/Tempered.lean`, which identifies the space of Definition 7.2.2 on the
whole space with Mathlib's Bessel potential space, composed with `equation_7_4_2`.

`equation_7_4_2` is the book's (7.4.2), which *defines* `H^s(ℝ^d)` for arbitrary real `s` by the
Fourier condition: for `v ∈ L^2(ℝ^d)` and `s ≥ 0`, `(1 + |ξ|^2)^{s/2} ℱv` lies in `L^2(ℝ^d)` —
`ℱv` being the `L^2` Fourier transform of `v` — exactly when `v` lies in the Bessel potential space
`TemperedDistribution.MemSobolev s 2`, the tempered distributions whose Bessel potential
`(1 - (2π)^{-2} Δ)^{s/2}` is an `L^2` function, which is the `H^s(ℝ^d)` Mathlib supports.
`equation_7_4_2_norm` is the matching norm identity: the `L^2` norm of the Bessel potential of `v`
*equals* — not merely is equivalent to — the `L^2` norm of `(1 + |ξ|^2)^{s/2} ℱv`, by Plancherel.
`s < 0` is excluded only because the proof reads the symbol off the `L^2` representative by
multiplying back by `(1 + |ξ|^2)^{-s/2}`, which is bounded exactly when `s ≥ 0`.

The book's (7.4.1), the *equivalence* of `‖(1 + |ξ|^2)^{k/2} ℱv‖_{L^2}` with the Sobolev norm
`[∑_{|α| ≤ k} ‖∂^α v‖_{L^2}^2]^{1/2}` of Definition 7.2.2, is a separate statement from
Theorem 7.4.1's membership criterion and is *not* proved here; the open node `equation_7_4_1`
records what it needs. `memSobolev_iteratedLineDerivOp` and `memLp_iteratedLineDerivOp` are the
derivative side of the criterion in the Bessel-potential reading, and delegate to the backbone.

Examples 7.4.2 and 7.4.3 are not formalized. Their Step 3 carries a whole-space estimate onto a
Lipschitz domain through the extension operator of Theorem 7.3.5, and their Step 2 is the density
of Theorem 7.3.4, so they are the §7.3 obstruction rather than the Fourier analysis; the same holds
for Exercises 7.4.3 and 7.4.4.
-/

open FourierTransform LineDeriv MeasureTheory TemperedDistribution TopologicalSpace

open scoped ENNReal SchwartzMap

namespace AtkinsonHan.Chapter07

section WholeSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Multiplying an `L^2` function by a symbol -/

/-- Multiplying an `L^2` function by a function of temperate growth is, on tempered distributions,
`TemperedDistribution.smulLeftCLM`: if `w` agrees almost everywhere with `g · u`, then `w` and
`g · u` are the same distribution. -/
private theorem toTemperedDistribution_eq_smulLeftCLM {g : E → ℂ} (hg : g.HasTemperateGrowth)
    {u w : Lp ℂ 2 (volume : Measure E)}
    (h : (w : E → ℂ) =ᵐ[volume] fun ξ ↦ g ξ * (u : E → ℂ) ξ) :
    (w : 𝓢'(E, ℂ)) = smulLeftCLM ℂ g (u : 𝓢'(E, ℂ)) := by
  ext f
  rw [Lp.toTemperedDistribution_apply, smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [h] with ξ hξ
  rw [hξ, SchwartzMap.smulLeftCLM_apply_apply hg]
  simp only [smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The symbol `(1 + |ξ|^2)^{s/2}` has temperate growth. -/
private theorem hasTemperateGrowth_symbol (s : ℝ) :
    (fun ξ : E ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop

/-- **Reading the symbol off the `L^2` representative.** If an `L^2` function `w` is, as a tempered
distribution, the product of the symbol `(1 + |ξ|^2)^{s/2}` with an `L^2` function `u`, and
`s ≥ 0`, then `w` is that product almost everywhere. The hypothesis `s ≥ 0` is what makes the
inverse symbol `(1 + |ξ|^2)^{-s/2}` bounded, so that multiplying the identity by it stays inside
`L^2`. -/
private theorem aeEq_of_smulLeftCLM_eq {s : ℝ} (hs : 0 ≤ s) {u w : Lp ℂ 2 (volume : Measure E)}
    (h : smulLeftCLM ℂ (fun ξ : E ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) (u : 𝓢'(E, ℂ)) =
      (w : 𝓢'(E, ℂ))) :
    (w : E → ℂ) =ᵐ[volume] fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (u : E → ℂ) ξ := by
  set g : E → ℂ := fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) with hgdef
  set g' : E → ℂ := fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ) with hg'def
  have hpos : ∀ ξ : E, (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := fun ξ ↦ by positivity
  have hg : g.HasTemperateGrowth := hasTemperateGrowth_symbol s
  have hg' : g'.HasTemperateGrowth := hasTemperateGrowth_symbol (-s)
  have hmul : ∀ ξ : E, g ξ * g' ξ = 1 := by
    intro ξ
    simp only [hgdef, hg'def, ← Complex.ofReal_mul, ← Real.rpow_add (hpos ξ)]
    rw [show s / 2 + -s / 2 = (0 : ℝ) by ring, Real.rpow_zero, Complex.ofReal_one]
  have hbdd : ∀ ξ : E, ‖g' ξ‖ ≤ 1 := by
    intro ξ
    simp only [hg'def, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (hpos ξ).le _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [norm_nonneg ξ]) (by linarith)
  have hb : MemLp (fun ξ ↦ g' ξ * (w : E → ℂ) ξ) 2 (volume : Measure E) := by
    refine (Lp.memLp w).mono (hg'.1.continuous.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable w)) ?_
    filter_upwards with ξ
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hbdd ξ)
  have hu : (hb.toLp _ : 𝓢'(E, ℂ)) = (u : 𝓢'(E, ℂ)) := by
    rw [toTemperedDistribution_eq_smulLeftCLM hg' hb.coeFn_toLp, ← h,
      smulLeftCLM_smulLeftCLM_apply hg hg', show g * g' = fun _ : E ↦ (1 : ℂ) from funext hmul,
      smulLeftCLM_const, one_smul]
  have hinj : Function.Injective (Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2) :=
    LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot
  have hueq : hb.toLp _ = u := hinj hu
  have huae : (u : E → ℂ) =ᵐ[volume] fun ξ ↦ g' ξ * (w : E → ℂ) ξ := by
    rw [← hueq]; exact hb.coeFn_toLp
  filter_upwards [huae] with ξ hξ
  rw [hξ, ← mul_assoc, hmul ξ, one_mul]

/-! ### The Fourier characterization -/

/-- **The Fourier characterization of `H^s(ℝ^d)` for `s ≥ 0`**: an `L^2` function `v` lies in the
Sobolev space of order `s` exactly when `(1 + |ξ|^2)^{s/2} ℱv` lies in `L^2`, where `ℱv` is the
`L^2` Fourier transform of `v`.

This is `TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier` with the multiplication by
the symbol made concrete: Mathlib states it as an equality of tempered distributions, and here the
`L^2` representative is identified pointwise almost everywhere, which is what the book displays. -/
theorem memSobolev_two_iff_memLp_symbol_mul_fourier {s : ℝ} (hs : 0 ≤ s)
    (v : Lp ℂ 2 (volume : Measure E)) :
    MemSobolev s 2 (v : 𝓢'(E, ℂ)) ↔
      MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2
        (volume : Measure E) := by
  rw [memSobolev_iff_exists_smulLeftCLM_fourier, Lp.fourier_toTemperedDistribution_eq]
  refine ⟨fun ⟨w, hw⟩ ↦ (Lp.memLp w).ae_eq (aeEq_of_smulLeftCLM_eq hs hw), fun hm ↦ ⟨hm.toLp _, ?_⟩⟩
  exact (toTemperedDistribution_eq_smulLeftCLM (hasTemperateGrowth_symbol s) hm.coeFn_toLp).symm

/-- **The Fourier transform of the Bessel potential.** If the Bessel potential of order `s ≥ 0` of
an `L^2` function `v` is the `L^2` function `w`, then `ℱw = (1 + |ξ|^2)^{s/2} ℱv` almost
everywhere. -/
theorem fourier_aeEq_symbol_mul_fourier_of_besselPotential_eq {s : ℝ} (hs : 0 ≤ s)
    {v w : Lp ℂ 2 (volume : Measure E)}
    (hw : besselPotential E ℂ s (v : 𝓢'(E, ℂ)) = (w : 𝓢'(E, ℂ))) :
    ((𝓕 w : Lp ℂ 2 (volume : Measure E)) : E → ℂ) =ᵐ[volume]
      fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (𝓕 v) ξ := by
  refine aeEq_of_smulLeftCLM_eq hs ?_
  rw [← Lp.fourier_toTemperedDistribution_eq, ← Lp.fourier_toTemperedDistribution_eq, ← hw,
    fourier_besselPotential_eq_smulLeftCLM_fourier_apply]

/-! ### Iterated derivatives -/

/-- **The directional derivatives of a Sobolev distribution.** If `f ∈ H^s(ℝ^d)` then the iterated
directional derivative `∂_{m_1} ⋯ ∂_{m_n} f` lies in `H^{s-n}(ℝ^d)`: Mathlib's
`TemperedDistribution.MemSobolev.lineDerivOp`, iterated, which is the backbone
`TemperedDistribution.MemSobolev.iteratedLineDerivOp`. -/
theorem memSobolev_iteratedLineDerivOp {s : ℝ} {f : 𝓢'(E, ℂ)} (hf : MemSobolev s 2 f) :
    ∀ (n : ℕ) (m : Fin n → E), MemSobolev (s - n) 2 (∂^{m} f) :=
  hf.iteratedLineDerivOp

/-- **The derivatives of order at most `k` of an element of `H^k(ℝ^d)` are `L^2` functions.** This
is the half of Theorem 7.4.1 that Mathlib's Bessel-potential Sobolev space gives directly; that
these distributional derivatives are the weak derivatives of Definition 7.1.3, and that the
converse holds, is the content of `theorem_7_4_1`. -/
theorem memLp_iteratedLineDerivOp {k n : ℕ} (hn : n ≤ k) {f : 𝓢'(E, ℂ)}
    (hf : MemSobolev (k : ℝ) 2 f) (m : Fin n → E) :
    ∃ w : Lp ℂ 2 (volume : Measure E), (∂^{m} f) = (w : 𝓢'(E, ℂ)) :=
  memSobolev_zero_iff.1 <| (memSobolev_iteratedLineDerivOp hf n m).mono <| by
    have : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hn
    linarith

end WholeSpace

/-! ### The Fourier definition (7.4.2) of `H^s(ℝ^d)` -/

variable {d : ℕ}

/-- **(7.4.2)**, the definition of `H^s(ℝ^d)` by the Fourier condition: for `v ∈ L^2(ℝ^d)` and a
real `s ≥ 0`, `(1 + |ξ|^2)^{s/2} ℱv` lies in `L^2(ℝ^d)` exactly when `v` lies in `H^s(ℝ^d)`.

`H^s(ℝ^d)` is read here as `TemperedDistribution.MemSobolev s 2`, the Bessel potential space: the
distributions whose Bessel potential of order `s` is an `L^2` function. At `s = 0` this is `L^2`
itself, by `TemperedDistribution.memSobolev_zero_iff`. This is *not* Theorem 7.4.1, whose left-hand
side is the `W^{k,2}(ℝ^d)` of `definition_7_2_2_multiIndex`, cut out by the weak derivatives; that
theorem is `theorem_7_4_1`, and it is this display composed with the bridge of
`Numlib/Analysis/Sobolev/Tempered.lean`. -/
theorem equation_7_4_2 {s : ℝ} (hs : 0 ≤ s)
    (v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    MemSobolev s 2 (v : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) ↔
      MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2 volume :=
  memSobolev_two_iff_memLp_symbol_mul_fourier hs v

/-- **The norm that goes with (7.4.2)**: for `v ∈ L^2(ℝ^d)` and `s ≥ 0`, if the Bessel potential of
order `s` of `v` is the `L^2` function `w` — so that `‖w‖_{L^2}` is the `H^s(ℝ^d)` norm of `v` in
the Bessel-potential reading — then

`‖w‖_{L^2(ℝ^d)} = ‖(1 + |ξ|^2)^{s/2} ℱv‖_{L^2(ℝ^d)}`,

by Plancherel. This is not the book's (7.4.1), which is the *equivalence* of the right-hand side
with the Sobolev norm `[∑_{|α| ≤ k} ‖∂^α v‖_{L^2}^2]^{1/2}` of Definition 7.2.2 and is the open
node `equation_7_4_1`. -/
theorem equation_7_4_2_norm {s : ℝ} (hs : 0 ≤ s)
    {v w : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))}
    (hw : besselPotential (EuclideanSpace ℝ (Fin d)) ℂ s (v : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
      (w : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) :
    ‖w‖ =
      (eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2 volume).toReal := by
  rw [← Lp.norm_fourier_eq w, Lp.norm_def]
  exact congrArg ENNReal.toReal
    (eLpNorm_congr_ae (fourier_aeEq_symbol_mul_fourier_of_besselPotential_eq hs hw))

/-! ### Theorem 7.4.1 -/

/-- **Theorem 7.4.1**, for the complex-valued functions that §7.4 allows throughout: a function
`v ∈ L^2(ℝ^d)` belongs to `H^k(ℝ^d) = W^{k,2}(ℝ^d)` — Definition 7.2.2, so cut out by the weak
derivatives `∂^α v` of order `|α| ≤ k` — exactly when `(1 + |ξ|^2)^{k/2} ℱv ∈ L^2(ℝ^d)`.

The left-hand side is `MemSobolevMultiIndex (stdBasis d) v k 2 ⊤ volume`, which is
`definition_7_2_2_multiIndex k 2 ⊤` read for complex-valued functions; `theorem_7_4_1` is the
real-valued form, over `definition_7_2_2_multiIndex` itself. The proof composes `equation_7_4_2`,
which is the Fourier condition against Mathlib's Bessel potential space, with the identification of
that space with `W^{k,2}(ℝ^d)` in `Numlib/Analysis/Sobolev/Tempered.lean`. -/
theorem theorem_7_4_1_complex {k : ℕ} (v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    MemSobolevMultiIndex (stdBasis d) (v : EuclideanSpace ℝ (Fin d) → ℂ) k 2 ⊤ volume ↔
      MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2 volume := by
  rw [← equation_7_4_2 (by positivity) v]
  exact memSobolevMultiIndex_iff_memSobolev (EuclideanSpace.basisFun (Fin d) ℝ)

/-- **Theorem 7.4.1**: a real function `v ∈ L^2(ℝ^d)` belongs to `H^k(ℝ^d)`, the `W^{k,2}(ℝ^d)` of
Definition 7.2.2, exactly when `(1 + |ξ|^2)^{k/2} ℱv ∈ L^2(ℝ^d)`.

Since the Fourier transform is complex, `ℱv` is read as the Fourier transform of the
complexification `Complex.ofRealCLM.compLp v` of `v`; §7.4 of the book allows the functions to be
complex-valued throughout, and `theorem_7_4_1_complex` is the statement for those. The *norm*
equivalence (7.4.1) that the book states next is the separate, open, `equation_7_4_1`. -/
theorem theorem_7_4_1 {k : ℕ} (v : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    definition_7_2_2_multiIndex k 2 ⊤ (v : EuclideanSpace ℝ (Fin d) → ℝ) ↔
      MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ)
        * (𝓕 (Complex.ofRealCLM.compLp v)) ξ) 2 volume := by
  rw [← theorem_7_4_1_complex (Complex.ofRealCLM.compLp v)]
  have hae : ((Complex.ofRealCLM.compLp v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
      : EuclideanSpace ℝ (Fin d) → ℂ)
        =ᵐ[volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin d))) : Set _)]
      fun x ↦ (((v : EuclideanSpace ℝ (Fin d) → ℝ) x : ℝ) : ℂ) := by
    rw [show ((⊤ : Opens (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)))
      = Set.univ from rfl, Measure.restrict_univ]
    filter_upwards [Complex.ofRealCLM.coeFn_compLp v] with x hx using hx
  exact ⟨fun h ↦ (memSobolevMultiIndex_ofReal_iff.2 h).congr_ae hae.symm,
    fun h ↦ memSobolevMultiIndex_ofReal_iff.1 (h.congr_ae hae)⟩

end AtkinsonHan.Chapter07
