import Numlib.Analysis.Wavelet.Haar

/-!
# Atkinson–Han §4.4: Haar wavelets

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §4.4.

Everything is the backbone `Numlib/Analysis/Wavelet/Haar`: the scaling function `φ = 1_[0,1)` and
its dilates and translates `Haar.scalingFun`, the scaling spaces `Haar.V`, the wavelet
`Haar.waveletFun` and the wavelet spaces `Haar.W`.

## Main results

* `equation_4_4_1` — (4.4.1): the scaling function, its dilates and translates, and `V_j`.
* `theorem_4_4_1_1` … `theorem_4_4_1_5` — the five properties of the scaling spaces.
* `theorem_4_4_2` — the characterization of `W_j` inside `V_{j+1}`, and (4.4.2).
* `equation_4_4_3` — the wavelet decomposition of `V_j` and of `L²(ℝ)`.
* `bookScalingFun`, `bookWaveletFun` — the book's unnormalised `φ(2^j x - k)` and `ψ(2^j x - k)`.
* `equation_4_4_6`, `equation_4_4_15` — (4.4.5)–(4.4.6) and (4.4.14)–(4.4.15), the two-scale
  relations in both directions.
* `theorem_4_4_3`, `theorem_4_4_4` — the decomposition and reconstruction steps, in the book's
  unnormalised coefficients.
* `equation_4_4_18` — (4.4.9)–(4.4.13) and (4.4.18), the multi-level transform: the analysis step
  iterated, with each piece expanded in its own system.
* `exercise_4_4_4` — the Haar wavelets of all levels are an orthonormal basis of `L²(ℝ)`.

## Conventions

The book's `V_j` is the set of *finite* linear combinations of the `φ(2^j x - k)`, which is not
closed in `L²(ℝ)`; the book itself remarks, in the paragraph after the definition, that one may
equally take the `ℓ²`-coefficient version. The closed subspace is the reading under which
"orthonormal basis of `V_j`" (Theorem 4.4.1 (1)) and `⋂ V_j = {0}` (Theorem 4.4.1 (5)) are true as
stated, so `Haar.V j` is the closed span and the book's span is its dense subspace — the last
clause of `equation_4_4_1`.

The book writes an element of `V_j` as `∑ a_k φ(2^j x - k)` in the **unnormalised** basis, whose
members have `L²` norm `2^{-j/2}`. Its coefficient `a_k^j` is therefore
`√(2^j) ⟪scalingFun j k, f⟫`, and that is how Theorems 4.4.3 and 4.4.4 are stated here; the halving
in (4.4.10)–(4.4.11) and its absence in (4.4.16)–(4.4.17) are exactly this normalisation. In the
orthonormal basis both steps carry the same factor `(√2)⁻¹`, which is the backbone's
`Haar.decomposition` and `Haar.reconstruction`.
-/

open MeasureTheory Real Submodule

namespace AtkinsonHan.Chapter04

/-! ### The scaling function and the scaling spaces -/

/-- **(4.4.1)** and the scaling spaces. The Haar scaling function is the unit step
`φ = 1_[0,1)`; its translate by `k` is the indicator of `[k, k + 1)`; the level-`j` scaling
function `2^{j/2} φ(2^j x - k)` is the dilation of that translate by `2^j`; and the scaling space
`V_j` is the closure in `L²(ℝ)` of the span of the level-`j` scaling functions, so that the book's
space of finite linear combinations is dense in it. -/
theorem equation_4_4_1 (j k : ℤ) :
    Haar.dyadic 0 0 = Set.Ico (0 : ℝ) 1 ∧
      Haar.scalingFun 0 0 = indicatorConstLp 2 (Haar.measurableSet_dyadic 0 0)
        (Haar.volume_dyadic_ne_top 0 0) 1 ∧
      Haar.dyadic 0 k = Set.Ico (k : ℝ) ((k : ℝ) + 1) ∧
      Haar.scalingFun j k = Lp.dilationₗᵢ ((2 : ℝ) ^ j) (zpow_ne_zero j two_ne_zero)
        (Haar.scalingFun 0 k) ∧
      (span ℝ (Set.range (Haar.scalingFun j))).topologicalClosure = Haar.V j :=
  ⟨Haar.dyadic_zero_zero, Haar.scalingFun_zero_zero, by simp [Haar.dyadic],
    Haar.scalingFun_eq_dilation j k, rfl⟩

/-- **Theorem 4.4.1 (1).** The functions `2^{j/2} φ(2^j x - k)`, `k ∈ ℤ`, form an orthonormal
basis of `V_j`: they are orthonormal and the closure of their span is `V_j`. -/
theorem theorem_4_4_1_1 (j : ℤ) :
    Orthonormal ℝ (Haar.scalingFun j) ∧
      (span ℝ (Set.range (Haar.scalingFun j))).topologicalClosure = Haar.V j :=
  ⟨Haar.orthonormal_scalingFun j, rfl⟩

/-- **Theorem 4.4.1 (2)** (scale invariance). `f ∈ V_j` if and only if `f(2^{-j} ·) ∈ V_0`: the
scaling space `V_j` is the image of `V_0` under the unitary dilation by `2^j`. -/
theorem theorem_4_4_1_2 (j : ℤ) :
    Haar.V j = (Haar.V 0).map
      (Lp.dilationₗᵢ ((2 : ℝ) ^ j) (zpow_ne_zero j two_ne_zero)).toLinearEquiv.toLinearMap :=
  Haar.V_eq_map_dilation j

/-- **Theorem 4.4.1 (3)** (nesting). `V_j ⊆ V_{j+1}`. -/
theorem theorem_4_4_1_3 (j : ℤ) : Haar.V j ≤ Haar.V (j + 1) :=
  Haar.V_le_V_succ j

/-- **Theorem 4.4.1 (4)** (density). The union of the scaling spaces is dense in `L²(ℝ)`. -/
theorem theorem_4_4_1_4 : (⨆ j : ℤ, Haar.V j).topologicalClosure = ⊤ :=
  Haar.topologicalClosure_iSup_V

/-- **Theorem 4.4.1 (5)** (separation). The intersection of the scaling spaces is `{0}`. -/
theorem theorem_4_4_1_5 : (⨅ j : ℤ, Haar.V j) = ⊥ :=
  Haar.iInf_V_eq_bot

/-! ### The wavelet and the wavelet spaces -/

/-- **Theorem 4.4.2** and **(4.4.2)**. An element `f = ∑ a_k φ(2^{j+1} x - k)` of `V_{j+1}` is
orthogonal to `V_j` — that is, lies in `W_j` — exactly when `a_{2k+1} = -a_{2k}` for every `k`;
so `W_j` is the orthogonal complement of `V_j` inside `V_{j+1}`, and it is the closed span of the
translates of the Haar wavelet `ψ = φ(2 ·) - φ(2 · - 1)`. -/
theorem theorem_4_4_2 (j : ℤ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    (f ∈ Haar.W j ↔ f ∈ Haar.V (j + 1) ∧ ∀ k : ℤ,
        inner ℝ (Haar.scalingFun (j + 1) (2 * k + 1)) f
          = -inner ℝ (Haar.scalingFun (j + 1) (2 * k)) f) ∧
      Haar.W j = Haar.V (j + 1) ⊓ (Haar.V j)ᗮ ∧
      (∀ k : ℤ, Haar.waveletFun j k =
        (√2)⁻¹ • (Haar.scalingFun (j + 1) (2 * k) - Haar.scalingFun (j + 1) (2 * k + 1))) ∧
      (span ℝ (Set.range (Haar.waveletFun j))).topologicalClosure = Haar.W j := by
  have hs2 : (√2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  refine ⟨?_, Haar.W_eq_inf_orthogonal j, fun k => Haar.waveletFun_eq j k, rfl⟩
  rw [Haar.mem_W_iff]
  refine and_congr_right fun _ => forall_congr' fun k => ?_
  rw [(Haar.decomposition j k f).1, mul_eq_zero, or_iff_right (inv_ne_zero hs2)]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-! ### The wavelet decomposition -/

/-- The scaling spaces increase with the level, by iterating `Haar.V_le_V_succ`. -/
private theorem V_mono {i j : ℤ} (h : i ≤ j) : Haar.V i ≤ Haar.V j := by
  induction j, h using Int.leInduction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (Haar.V_le_V_succ n)

/-- Telescoping `V_{l+1} = V_l ⊔ W_l` from level `i` up to level `j`. -/
private theorem V_eq_sup_iSup_W {i j : ℤ} (h : i ≤ j) :
    Haar.V j = Haar.V i ⊔ ⨆ l ∈ Set.Ico i j, Haar.W l := by
  induction j, h using Int.leInduction with
  | base => simp
  | succ n hn ih =>
      have hins : Set.Ico i (n + 1) = insert n (Set.Ico i n) := by
        ext x
        simp only [Set.mem_Ico, Set.mem_insert_iff]
        omega
      rw [← Haar.sup_V_W n, ih, hins, iSup_insert, sup_assoc]
      congr 1
      exact sup_comm _ _

/-- **(4.4.3)**, the wavelet decomposition. For `i ≤ j` the scaling space `V_j` is the orthogonal
direct sum `V_i ⊕ W_i ⊕ ⋯ ⊕ W_{j-1}`, the summands being pairwise orthogonal; and for every `j`
the sum `V_j ⊕ W_j ⊕ W_{j+1} ⊕ ⋯` is dense in `L²(ℝ)`. -/
theorem equation_4_4_3 (j : ℤ) :
    (∀ i ≤ j, Haar.V j = Haar.V i ⊔ ⨆ l ∈ Set.Ico i j, Haar.W l) ∧
      Haar.V j ≤ (Haar.W j)ᗮ ∧
      (∀ i < j, Haar.W i ≤ (Haar.W j)ᗮ) ∧
      (Haar.V j ⊔ ⨆ l ∈ Set.Ici j, Haar.W l).topologicalClosure = ⊤ := by
  refine ⟨fun i hi => V_eq_sup_iSup_W hi, Haar.V_le_orthogonal_W j, fun i hij => ?_, ?_⟩
  · exact ((Haar.W_le_V_succ i).trans (V_mono (by omega))).trans (Haar.V_le_orthogonal_W j)
  · have hle : (⨆ i : ℤ, Haar.V i) ≤ Haar.V j ⊔ ⨆ l ∈ Set.Ici j, Haar.W l := by
      refine iSup_le fun i => ?_
      rcases le_or_gt j i with h | h
      · rw [V_eq_sup_iSup_W h]
        refine sup_le le_sup_left (iSup₂_le fun l hl => ?_)
        exact le_sup_of_le_right (le_iSup₂ (f := fun l (_ : l ∈ Set.Ici j) => Haar.W l) l hl.1)
      · exact (V_mono h.le).trans le_sup_left
    have hmono := Submodule.topologicalClosure_mono hle
    rw [Haar.topologicalClosure_iSup_V] at hmono
    exact top_le_iff.mp hmono

/-! ### The two-scale relations -/

/-- The book's unnormalised scaling function `φ(2^j x - k)`, which is `2^{-j/2}` times the
normalised `Haar.scalingFun j k`: it is the indicator of the dyadic interval
`[k 2^{-j}, (k+1) 2^{-j})`, of `L²` norm `2^{-j/2}` rather than `1`.  Every displayed equation of
the section is written in this basis. -/
noncomputable abbrev bookScalingFun (j k : ℤ) : Lp ℝ 2 (volume : Measure ℝ) :=
  (√((2 : ℝ) ^ j))⁻¹ • Haar.scalingFun j k

/-- The book's unnormalised wavelet `ψ(2^j x - k)`, which is `2^{-j/2}` times the normalised
`Haar.waveletFun j k`. -/
noncomputable abbrev bookWaveletFun (j k : ℤ) : Lp ℝ 2 (volume : Measure ℝ) :=
  (√((2 : ℝ) ^ j))⁻¹ • Haar.waveletFun j k

private theorem inv_sqrt_zpow_mul (j : ℤ) :
    (√((2 : ℝ) ^ j))⁻¹ * (√2)⁻¹ = (√((2 : ℝ) ^ (j + 1)))⁻¹ := by
  rw [zpow_add_one₀ (two_ne_zero' ℝ), Real.sqrt_mul (by positivity), mul_inv]

private theorem inv_sqrt_zpow_succ_mul (j : ℤ) :
    (√((2 : ℝ) ^ (j + 1)))⁻¹ * (√2)⁻¹ = 2⁻¹ * (√((2 : ℝ) ^ j))⁻¹ := by
  have h2 : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2 : (√2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  rw [← inv_sqrt_zpow_mul, mul_assoc, ← mul_inv]
  rw [h2]
  ring

/-- **(4.4.5)–(4.4.6)**, the two-scale relations that read a fine scaling function off the coarse
pair: `φ(2^{j+1} x - 2k) = ½[φ(2^j x - k) + ψ(2^j x - k)]` and
`φ(2^{j+1} x - 2k - 1) = ½[φ(2^j x - k) - ψ(2^j x - k)]`.  These are the identities the book
derives Theorem 4.4.3 from; in the normalised basis they are `Haar.scalingFun_succ_eq`, where the
`½` is `(√2)⁻¹` twice over. -/
theorem equation_4_4_6 (j k : ℤ) :
    bookScalingFun (j + 1) (2 * k) = (2 : ℝ)⁻¹ • (bookScalingFun j k + bookWaveletFun j k) ∧
      bookScalingFun (j + 1) (2 * k + 1)
        = (2 : ℝ)⁻¹ • (bookScalingFun j k - bookWaveletFun j k) := by
  obtain ⟨h1, h2⟩ := Haar.scalingFun_succ_eq j k
  refine ⟨?_, ?_⟩
  · rw [show bookScalingFun (j + 1) (2 * k)
        = (√((2 : ℝ) ^ (j + 1)))⁻¹ • Haar.scalingFun (j + 1) (2 * k) from rfl, h1, smul_smul,
      inv_sqrt_zpow_succ_mul, smul_add, ← smul_smul, ← smul_smul, smul_add]
  · rw [show bookScalingFun (j + 1) (2 * k + 1)
        = (√((2 : ℝ) ^ (j + 1)))⁻¹ • Haar.scalingFun (j + 1) (2 * k + 1) from rfl, h2, smul_smul,
      inv_sqrt_zpow_succ_mul, smul_sub, ← smul_smul, ← smul_smul, smul_sub]

/-- **(4.4.14)–(4.4.15)**, the two-scale relations in the other direction:
`φ(2^j x - k) = φ(2^{j+1} x - 2k) + φ(2^{j+1} x - 2k - 1)` — a dyadic interval is the disjoint
union of its two halves — and `ψ(2^j x - k) = φ(2^{j+1} x - 2k) - φ(2^{j+1} x - 2k - 1)`, which is
the definition of the Haar wavelet.  With (4.4.5)–(4.4.6) they are what makes Theorem 4.4.4 the
inverse of Theorem 4.4.3. -/
theorem equation_4_4_15 (j k : ℤ) :
    bookScalingFun j k = bookScalingFun (j + 1) (2 * k) + bookScalingFun (j + 1) (2 * k + 1) ∧
      bookWaveletFun j k
        = bookScalingFun (j + 1) (2 * k) - bookScalingFun (j + 1) (2 * k + 1) := by
  refine ⟨?_, ?_⟩
  · rw [show bookScalingFun j k = (√((2 : ℝ) ^ j))⁻¹ • Haar.scalingFun j k from rfl,
      Haar.scalingFun_two_scale j k, smul_smul, inv_sqrt_zpow_mul, smul_add]
  · rw [show bookWaveletFun j k = (√((2 : ℝ) ^ j))⁻¹ • Haar.waveletFun j k from rfl,
      Haar.waveletFun_eq j k, smul_smul, inv_sqrt_zpow_mul, smul_sub]

/-! ### Decomposition and reconstruction -/

private theorem inv_sqrt_two : (√2 : ℝ)⁻¹ = √2 / 2 := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2 : (√2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp
  linarith [h2]

private theorem sqrt_zpow_succ (j : ℤ) : √((2 : ℝ) ^ (j + 1)) = √((2 : ℝ) ^ j) * √2 := by
  rw [zpow_add_one₀ (two_ne_zero' ℝ), Real.sqrt_mul (by positivity)]

/-- **Theorem 4.4.3** and **(4.4.10)–(4.4.11)**, the decomposition (analysis) step. Writing
`a_k^j = √(2^j) ⟪scalingFun j k, f⟫` for the book's coefficients in the unnormalised basis
`φ(2^j x - k)`, and `b_k^j` for the corresponding wavelet coefficients, one level of the Haar
transform is `a_k^{j} = (a_{2k}^{j+1} + a_{2k+1}^{j+1})/2` and
`b_k^{j} = (a_{2k}^{j+1} - a_{2k+1}^{j+1})/2`. -/
theorem theorem_4_4_3 (j k : ℤ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    √((2 : ℝ) ^ j) * inner ℝ (Haar.scalingFun j k) f =
        (√((2 : ℝ) ^ (j + 1)) * inner ℝ (Haar.scalingFun (j + 1) (2 * k)) f +
          √((2 : ℝ) ^ (j + 1)) * inner ℝ (Haar.scalingFun (j + 1) (2 * k + 1)) f) / 2 ∧
      √((2 : ℝ) ^ j) * inner ℝ (Haar.waveletFun j k) f =
        (√((2 : ℝ) ^ (j + 1)) * inner ℝ (Haar.scalingFun (j + 1) (2 * k)) f -
          √((2 : ℝ) ^ (j + 1)) * inner ℝ (Haar.scalingFun (j + 1) (2 * k + 1)) f) / 2 := by
  obtain ⟨ha, hb⟩ := Haar.decomposition j k f
  rw [ha, hb, sqrt_zpow_succ, inv_sqrt_two]
  constructor <;> ring

/-- **Theorem 4.4.4** and **(4.4.16)–(4.4.17)**, the reconstruction (synthesis) step, inverse to
Theorem 4.4.3: in the same unnormalised coefficients, `a_{2k}^{j+1} = a_k^j + b_k^j` and
`a_{2k+1}^{j+1} = a_k^j - b_k^j`. -/
theorem theorem_4_4_4 (j k : ℤ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    √((2 : ℝ) ^ (j + 1)) * inner ℝ (Haar.scalingFun (j + 1) (2 * k)) f =
        √((2 : ℝ) ^ j) * inner ℝ (Haar.scalingFun j k) f +
          √((2 : ℝ) ^ j) * inner ℝ (Haar.waveletFun j k) f ∧
      √((2 : ℝ) ^ (j + 1)) * inner ℝ (Haar.scalingFun (j + 1) (2 * k + 1)) f =
        √((2 : ℝ) ^ j) * inner ℝ (Haar.scalingFun j k) f -
          √((2 : ℝ) ^ j) * inner ℝ (Haar.waveletFun j k) f := by
  have h2 : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  obtain ⟨ha, hb⟩ := Haar.reconstruction j k f
  rw [ha, hb, sqrt_zpow_succ, inv_sqrt_two]
  constructor
  · linear_combination (√((2 : ℝ) ^ j) *
      (inner ℝ (Haar.scalingFun j k) f + inner ℝ (Haar.waveletFun j k) f) / 2) * h2
  · linear_combination (√((2 : ℝ) ^ j) *
      (inner ℝ (Haar.scalingFun j k) f - inner ℝ (Haar.waveletFun j k) f) / 2) * h2

/-! ### The multi-level transform -/

/-- **(4.4.9)–(4.4.13)** and **(4.4.18)**, the multi-level Haar transform. Iterating the analysis
step of Theorem 4.4.3 from level `J` down to level `i` writes an element of `V_J` as

`f_J = f_i + w_i + w_{i+1} + ⋯ + w_{J-1}`,

with `f_i` its orthogonal projection onto `V_i` and `w_l` its projection onto `W_l`; and each piece
is the expansion the book writes, `f_i = ∑_k a_k^i φ(2^i x - k)` and `w_l = ∑_k b_k^l ψ(2^l x - k)`,
in the unnormalised basis and with the coefficients `a_k^j = √(2^j) ⟪φ_{j,k}, f⟫` and
`b_k^j = √(2^j) ⟪ψ_{j,k}, f⟫` of Theorems 4.4.3–4.4.4.

Stated for the projections of an arbitrary `f`, which for `f ∈ V_J` is the book's statement about
`f` itself, since the projection onto `V_J` then fixes it. -/
theorem equation_4_4_18 {i J : ℤ} (h : i ≤ J) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    (Haar.V J).starProjection f
        = (Haar.V i).starProjection f
          + ∑ l ∈ Finset.Ico i J, (Haar.W l).starProjection f ∧
      HasSum (fun k : ℤ =>
          (√((2 : ℝ) ^ i) * inner ℝ (Haar.scalingFun i k) f) • bookScalingFun i k)
        ((Haar.V i).starProjection f) ∧
      ∀ l : ℤ, HasSum (fun k : ℤ =>
          (√((2 : ℝ) ^ l) * inner ℝ (Haar.waveletFun l k) f) • bookWaveletFun l k)
        ((Haar.W l).starProjection f) := by
  have hne : ∀ l : ℤ, √((2 : ℝ) ^ l) ≠ 0 := fun l => ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  refine ⟨Haar.starProjection_V_eq_sum h f, ?_, fun l => ?_⟩
  · refine (Haar.hasSum_inner_smul_starProjection_V i f).congr_fun fun k => ?_
    rw [show bookScalingFun i k = (√((2 : ℝ) ^ i))⁻¹ • Haar.scalingFun i k from rfl, smul_smul]
    congr 1
    field_simp
  · refine (Haar.hasSum_inner_smul_starProjection_W l f).congr_fun fun k => ?_
    rw [show bookWaveletFun l k = (√((2 : ℝ) ^ l))⁻¹ • Haar.waveletFun l k from rfl, smul_smul]
    congr 1
    field_simp

/-- **Exercise 4.4.4**: the rescaled Haar wavelets `ψ_{jk}(x) = 2^{j/2} ψ(2^j x - k)`, over all
`j, k ∈ ℤ`, form an orthonormal basis of `L²(ℝ)`: they satisfy `∫ ψ_{jk} ψ_{lm} = δ_{jl} δ_{km}`
and every `f ∈ L²(ℝ)` is the sum of its wavelet coefficients against them.

The expansion is stated rather than the bundled `Haar.hilbertBasis` because it is what a consumer
uses; the basis itself is the backbone declaration behind both clauses. -/
theorem exercise_4_4_4 :
    (∀ i j k l : ℤ, inner ℝ (Haar.waveletFun i k) (Haar.waveletFun j l)
        = if i = j then (if k = l then (1 : ℝ) else 0) else 0) ∧
      ∀ f : Lp ℝ 2 (volume : Measure ℝ),
        HasSum (fun p : ℤ × ℤ =>
          (inner ℝ (Haar.waveletFun p.1 p.2) f) • Haar.waveletFun p.1 p.2) f := by
  refine ⟨fun i j k l => ?_, fun f => ?_⟩
  · have h := orthonormal_iff_ite.mp Haar.orthonormal_waveletFun_prod (i, k) (j, l)
    rw [h]
    by_cases hij : i = j
    · subst hij
      by_cases hkl : k = l
      · subst hkl
        rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl]
      · rw [ite_eq_right (by simp [Prod.ext_iff, hkl]), ite_eq_left rfl, ite_eq_right hkl]
    · rw [ite_eq_right (by simp [Prod.ext_iff, hij]), ite_eq_right hij]
  · have h := Haar.hilbertBasis.hasSum_repr f
    refine h.congr_fun fun p => ?_
    simp only [HilbertBasis.repr_apply_apply, Haar.coe_hilbertBasis]

end AtkinsonHan.Chapter04
