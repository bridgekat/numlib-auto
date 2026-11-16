/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Wavelet.Haar

/-!
# Atkinson and Han, Section 4.4: Haar wavelets

This module formalizes Section 4.4 of [han2009theoretical], the Haar wavelets on $\mathbb{R}$. The
Haar scaling function is $\phi = 1_{[0,1)}$, and the Haar wavelet is
$\psi(x) = \phi(2x) - \phi(2x - 1)$. For $j, k \in \mathbb{Z}$, the normalized functions
$$\phi_{j,k}(x) = 2^{j/2} \phi(2^j x - k), \qquad \psi_{j,k}(x) = 2^{j/2} \psi(2^j x - k)$$
have norm $1$ in $L^2(\mathbb{R})$. The scaling space $V_j$ is the closed span of the $\phi_{j,k}$,
$k \in \mathbb{Z}$, and the wavelet space $W_j$ is the closed span of the $\psi_{j,k}$,
$k \in \mathbb{Z}$. The module proves the five properties of the scaling spaces (Theorem 4.4.1), the
characterization of $W_j$ as the orthogonal complement of $V_j$ in $V_{j+1}$ (Theorem 4.4.2), the
wavelet decomposition $V_j = V_i \oplus W_i \oplus \dots \oplus W_{j-1}$, the two-scale relations,
the decomposition and reconstruction steps (Theorems 4.4.3 and 4.4.4), the multi-level transform,
and the fact that the $\psi_{j,k}$ form an orthonormal basis of $L^2(\mathbb{R})$ (Exercise 4.4.4).

All results specialize the backbone module `Numlib.Analysis.Wavelet.Haar`. In that module, the
functions $\phi_{j,k}$ and $\psi_{j,k}$ are `Haar.scalingFun j k` and `Haar.waveletFun j k`, and the
spaces $V_j$ and $W_j$ are `Haar.V j` and `Haar.W j`.

## Main definitions

* `AtkinsonHan.Chapter04.bookScalingFun` and `AtkinsonHan.Chapter04.bookWaveletFun`: the book's
  functions $\phi(2^j x - k)$ and $\psi(2^j x - k)$, which are not normalized.

## Main results

* Equation (4.4.1), `AtkinsonHan.Chapter04.equation_4_4_1`: the scaling function, its translates and
  dilates, and the space $V_j$.
* Theorem 4.4.1(1), `AtkinsonHan.Chapter04.theorem_4_4_1_1`: the $\phi_{j,k}$, $k \in \mathbb{Z}$,
  form an orthonormal basis of $V_j$.
* Theorem 4.4.1(2), `AtkinsonHan.Chapter04.theorem_4_4_1_2`: $V_j$ is the image of $V_0$ under the
  dilation by $2^j$.
* Theorem 4.4.1(3), `AtkinsonHan.Chapter04.theorem_4_4_1_3`: $V_j \subseteq V_{j+1}$.
* Theorem 4.4.1(4), `AtkinsonHan.Chapter04.theorem_4_4_1_4`: $\bigcup_j V_j$ is dense in
  $L^2(\mathbb{R})$.
* Theorem 4.4.1(5), `AtkinsonHan.Chapter04.theorem_4_4_1_5`: $\bigcap_j V_j = \{0\}$.
* Theorem 4.4.2 and equation (4.4.2), `AtkinsonHan.Chapter04.theorem_4_4_2`: the characterization of
  $W_j$ inside $V_{j+1}$.
* Equation (4.4.3), `AtkinsonHan.Chapter04.equation_4_4_3`: the orthogonal decomposition of $V_j$,
  and the density of $V_j \oplus W_j \oplus W_{j+1} \oplus \cdots$ in $L^2(\mathbb{R})$.
* Equations (4.4.5)–(4.4.6), `AtkinsonHan.Chapter04.equation_4_4_6`: the fine scaling functions in
  terms of the coarse scaling function and wavelet.
* Theorem 4.4.3 and equations (4.4.10)–(4.4.11), `AtkinsonHan.Chapter04.theorem_4_4_3`: the
  decomposition step $a_k^j = (a_{2k}^{j+1} + a_{2k+1}^{j+1})/2$,
  $b_k^j = (a_{2k}^{j+1} - a_{2k+1}^{j+1})/2$.
* Equations (4.4.9)–(4.4.13) and (4.4.18), `AtkinsonHan.Chapter04.equation_4_4_18`: the multi-level
  transform.
* Equations (4.4.14)–(4.4.15), `AtkinsonHan.Chapter04.equation_4_4_15`: the coarse scaling function
  and wavelet in terms of the fine scaling functions.
* Theorem 4.4.4 and equations (4.4.16)–(4.4.17), `AtkinsonHan.Chapter04.theorem_4_4_4`: the
  reconstruction step $a_{2k}^{j+1} = a_k^j + b_k^j$, $a_{2k+1}^{j+1} = a_k^j - b_k^j$.
* Exercise 4.4.4, `AtkinsonHan.Chapter04.exercise_4_4_4`: the $\psi_{j,k}$, $j, k \in \mathbb{Z}$,
  form an orthonormal basis of $L^2(\mathbb{R})$.

## Conventions

* The book writes an element of $V_j$ as $\sum_k a_k \phi(2^j x - k)$, in the basis that is not
  normalized. Its members have $L^2$ norm $2^{-j/2}$. Therefore the book's coefficient is
  $a_k^j = 2^{j/2} (\phi_{j,k}, f)$, and the wavelet coefficient is
  $b_k^j = 2^{j/2} (\psi_{j,k}, f)$. Theorems 4.4.3 and 4.4.4 are stated with these coefficients.
  The factor $1/2$ in (4.4.10)–(4.4.11) and its absence in (4.4.16)–(4.4.17) come from this
  normalization. In the orthonormal basis both steps carry the same factor $2^{-1/2}$; these forms
  are `Haar.decomposition` and `Haar.reconstruction`.
* The dilation of $f \in L^2(\mathbb{R})$ by $c \ne 0$ is the unitary map
  $f \mapsto |c|^{1/2} f(c \, \cdot)$, which is `MeasureTheory.Lp.dilationₗᵢ c`.

## Deviations from the source

* **Definition of $V_j$** (reading). The book defines $V_j$ as the set of finite linear combinations
  of the $\phi(2^j x - k)$. Here $V_j$ is the closure of this set in $L^2(\mathbb{R})$. See
  `AtkinsonHan.Chapter04.equation_4_4_1`.
-/

open MeasureTheory Real Submodule

namespace AtkinsonHan.Chapter04

/-! ### The scaling function and the scaling spaces -/

/-- **Equation (4.4.1)** of [han2009theoretical], the scaling function and the scaling spaces. For
$j, k \in \mathbb{Z}$:

1. the dyadic interval of level $0$ and index $0$ is $[0, 1)$, and the Haar scaling function
   $\phi_{0,0}$ is the indicator function $\phi = 1_{[0,1)}$ as an element of $L^2(\mathbb{R})$;
2. the dyadic interval of level $0$ and index $k$ is $[k, k + 1)$, so
   $\phi_{0,k}(x) = \phi(x - k)$ is its indicator function;
3. $\phi_{j,k}(x) = 2^{j/2} \phi(2^j x - k)$ is the dilation of $\phi_{0,k}$ by $2^j$, that is,
   $\phi_{j,k}(x) = 2^{j/2} \phi_{0,k}(2^j x)$;
4. the closure in $L^2(\mathbb{R})$ of the span of the $\phi_{j,k}$, $k \in \mathbb{Z}$, is
   $V_j$.

**Reading.** The book defines $V_j$ as the set of finite linear combinations of the functions
$\phi(2^j x - k)$, $k \in \mathbb{Z}$. This set is not closed in $L^2(\mathbb{R})$. In the
paragraph after the definition, the book remarks that one may equally take the combinations with
square-summable coefficients. Here $V_j$ (`Haar.V j`) is the closed span. With this reading, the
claims "orthonormal basis of $V_j$" (Theorem 4.4.1(1)) and $\bigcap_j V_j = \{0\}$ (Theorem
4.4.1(5)) are true as stated. The book's space of finite linear combinations is a dense subspace
of $V_j$, by part 4.

The dyadic interval of level $j$ and index $k$ is `Haar.dyadic j k`
$= [k 2^{-j}, (k+1) 2^{-j})$, and $\phi_{j,k}$ is `Haar.scalingFun j k`. The dilation is
`MeasureTheory.Lp.dilationₗᵢ`. -/
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

/-- **Theorem 4.4.1(1)** of [han2009theoretical]. For every $j \in \mathbb{Z}$, the functions
$\phi_{j,k}(x) = 2^{j/2} \phi(2^j x - k)$, $k \in \mathbb{Z}$, form an orthonormal basis of
$V_j$: they are orthonormal in $L^2(\mathbb{R})$, and the closure of their span is $V_j$. -/
theorem theorem_4_4_1_1 (j : ℤ) :
    Orthonormal ℝ (Haar.scalingFun j) ∧
      (span ℝ (Set.range (Haar.scalingFun j))).topologicalClosure = Haar.V j :=
  ⟨Haar.orthonormal_scalingFun j, rfl⟩

/-- **Theorem 4.4.1(2)** of [han2009theoretical] (scale invariance). For every $j \in \mathbb{Z}$,
the scaling space $V_j$ is the image of $V_0$ under the dilation
$g \mapsto 2^{j/2} g(2^j \, \cdot)$. Equivalently, $f \in V_j$ if and only if
$f(2^{-j} \, \cdot) \in V_0$.

The dilation is the unitary map `MeasureTheory.Lp.dilationₗᵢ (2 ^ j)` of $L^2(\mathbb{R})$. -/
theorem theorem_4_4_1_2 (j : ℤ) :
    Haar.V j = (Haar.V 0).map
      (Lp.dilationₗᵢ ((2 : ℝ) ^ j) (zpow_ne_zero j two_ne_zero)).toLinearEquiv.toLinearMap :=
  Haar.V_eq_map_dilation j

/-- **Theorem 4.4.1(3)** of [han2009theoretical] (nesting). For every $j \in \mathbb{Z}$,
$V_j \subseteq V_{j+1}$. -/
theorem theorem_4_4_1_3 (j : ℤ) : Haar.V j ≤ Haar.V (j + 1) :=
  Haar.V_le_V_succ j

/-- **Theorem 4.4.1(4)** of [han2009theoretical] (density). The union
$\bigcup_{j \in \mathbb{Z}} V_j$ is dense in $L^2(\mathbb{R})$: the closure of the sum of the
spaces $V_j$ is $L^2(\mathbb{R})$.

Since the $V_j$ increase with $j$, their sum is their union. -/
theorem theorem_4_4_1_4 : (⨆ j : ℤ, Haar.V j).topologicalClosure = ⊤ :=
  Haar.topologicalClosure_iSup_V

/-- **Theorem 4.4.1(5)** of [han2009theoretical] (separation). The intersection of the scaling
spaces is trivial: $\bigcap_{j \in \mathbb{Z}} V_j = \{0\}$. -/
theorem theorem_4_4_1_5 : (⨅ j : ℤ, Haar.V j) = ⊥ :=
  Haar.iInf_V_eq_bot

/-! ### The wavelet and the wavelet spaces -/

/-- **Theorem 4.4.2** and **equation (4.4.2)** of [han2009theoretical]. Let $j \in \mathbb{Z}$ and
$f \in L^2(\mathbb{R})$. Then:

1. $f \in W_j$ if and only if $f \in V_{j+1}$ and $(\phi_{j+1,2k+1}, f) = -(\phi_{j+1,2k}, f)$
   for every $k \in \mathbb{Z}$;
2. $W_j = V_{j+1} \cap V_j^\perp$, the orthogonal complement of $V_j$ in $V_{j+1}$;
3. $\psi_{j,k} = 2^{-1/2} (\phi_{j+1,2k} - \phi_{j+1,2k+1})$ for every $k \in \mathbb{Z}$, which
   is $2^{j/2} \psi(2^j x - k)$ for the Haar wavelet $\psi(x) = \phi(2x) - \phi(2x - 1)$;
4. the closure of the span of the $\psi_{j,k}$, $k \in \mathbb{Z}$, is $W_j$.

In the book's form, an element $f = \sum_k a_k \phi(2^{j+1} x - k)$ of $V_{j+1}$ lies in $W_j$
exactly when $a_{2k+1} = -a_{2k}$ for every $k$. The coefficients $a_k$ are a common multiple of
the inner products $(\phi_{j+1,k}, f)$, so part 1 is this condition. In the backbone, $W_j$
(`Haar.W j`) is defined as the closed span of part 4. -/
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

/-- For $i \le j$, $V_i \subseteq V_j$. -/
private theorem V_mono {i j : ℤ} (h : i ≤ j) : Haar.V i ≤ Haar.V j := by
  induction j, h using Int.leInduction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (Haar.V_le_V_succ n)

/-- For $i \le j$, $V_j = V_i + W_i + W_{i+1} + \dots + W_{j-1}$. -/
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

/-- **Equation (4.4.3)** of [han2009theoretical], the wavelet decomposition. Let $j \in \mathbb{Z}$.
Then:

1. for every $i \le j$, $V_j = V_i + W_i + W_{i+1} + \dots + W_{j-1}$;
2. $V_j$ is orthogonal to $W_j$;
3. for every $i < j$, $W_i$ is orthogonal to $W_j$;
4. the sum $V_j + W_j + W_{j+1} + \cdots$ is dense in $L^2(\mathbb{R})$.

By parts 2 and 3 the summands in parts 1 and 4 are pairwise orthogonal, so the sums are the
orthogonal direct sums $V_j = V_i \oplus W_i \oplus \dots \oplus W_{j-1}$ and
$V_j \oplus W_j \oplus W_{j+1} \oplus \cdots$ of the book. The sums are sums of subspaces,
without closure; the closure is taken only in part 4. -/
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

/-- The book's scaling function $\phi(2^j x - k)$, which is not normalized: it is
$2^{-j/2} \phi_{j,k}$, the indicator function of the dyadic interval $[k 2^{-j}, (k+1) 2^{-j})$,
with $L^2$ norm $2^{-j/2}$.

The displayed equations of Section 4.4 of [han2009theoretical] use this basis. The normalized
function $\phi_{j,k}$ is `Haar.scalingFun j k`. -/
noncomputable abbrev bookScalingFun (j k : ℤ) : Lp ℝ 2 (volume : Measure ℝ) :=
  (√((2 : ℝ) ^ j))⁻¹ • Haar.scalingFun j k

/-- The book's wavelet $\psi(2^j x - k)$, which is not normalized: it is $2^{-j/2} \psi_{j,k}$,
where $\psi_{j,k}$ is the normalized wavelet `Haar.waveletFun j k`.

This function supports the displayed equations of Section 4.4 of [han2009theoretical]. -/
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

/-- **Equations (4.4.5)–(4.4.6)** of [han2009theoretical], the two-scale relations that give a fine
scaling function in terms of the coarse pair. For $j, k \in \mathbb{Z}$,
$$\phi(2^{j+1} x - 2k) = \tfrac12 \bigl[\phi(2^j x - k) + \psi(2^j x - k)\bigr], \qquad
  \phi(2^{j+1} x - 2k - 1) = \tfrac12 \bigl[\phi(2^j x - k) - \psi(2^j x - k)\bigr].$$

The book derives Theorem 4.4.3 from these identities. In the normalized basis they are
`Haar.scalingFun_succ_eq`, where the factor $\tfrac12$ is $2^{-1/2} \cdot 2^{-1/2}$. -/
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

/-- **Equations (4.4.14)–(4.4.15)** of [han2009theoretical], the two-scale relations in the other
direction. For $j, k \in \mathbb{Z}$,
$$\phi(2^j x - k) = \phi(2^{j+1} x - 2k) + \phi(2^{j+1} x - 2k - 1), \qquad \psi(2^j x - k) =
  \phi(2^{j+1} x - 2k) - \phi(2^{j+1} x - 2k - 1).$$

The first identity says that a dyadic interval is the disjoint union of its two halves, and the
second is the definition of the Haar wavelet. Together with (4.4.5)–(4.4.6), they make Theorem
4.4.4 the inverse of Theorem 4.4.3. -/
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

/-- **Theorem 4.4.3** and **equations (4.4.10)–(4.4.11)** of [han2009theoretical], the decomposition
(analysis) step. Let $j, k \in \mathbb{Z}$ and $f \in L^2(\mathbb{R})$, and define the
coefficients $a_k^j = 2^{j/2} (\phi_{j,k}, f)$ and $b_k^j = 2^{j/2} (\psi_{j,k}, f)$. Then
$$a_k^j = \tfrac12 \bigl(a_{2k}^{j+1} + a_{2k+1}^{j+1}\bigr), \qquad b_k^j = \tfrac12
  \bigl(a_{2k}^{j+1} - a_{2k+1}^{j+1}\bigr).$$

For $f \in V_{j+1}$, the numbers $a_k^{j+1}$ are the book's coefficients of $f$ in the basis
$\phi(2^{j+1} x - k)$, and $a_k^j$, $b_k^j$ are the coefficients of its components in $V_j$ and
$W_j$. The identities hold for every $f \in L^2(\mathbb{R})$. In the orthonormal basis this is
`Haar.decomposition`. -/
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

/-- **Theorem 4.4.4** and **equations (4.4.16)–(4.4.17)** of [han2009theoretical], the
reconstruction (synthesis) step, which inverts Theorem 4.4.3. Let $j, k \in \mathbb{Z}$ and
$f \in L^2(\mathbb{R})$, with the coefficients $a_k^j = 2^{j/2} (\phi_{j,k}, f)$ and
$b_k^j = 2^{j/2} (\psi_{j,k}, f)$ of `AtkinsonHan.Chapter04.theorem_4_4_3`. Then
$$a_{2k}^{j+1} = a_k^j + b_k^j, \qquad a_{2k+1}^{j+1} = a_k^j - b_k^j.$$

In the orthonormal basis this is `Haar.reconstruction`. -/
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

/-- **Equations (4.4.9)–(4.4.13) and (4.4.18)** of [han2009theoretical], the multi-level Haar
transform. Let $i \le J$ be integers and $f \in L^2(\mathbb{R})$. Write $P_U$ for the orthogonal
projection onto a closed subspace $U$, and let $a_k^j = 2^{j/2} (\phi_{j,k}, f)$ and
$b_k^j = 2^{j/2} (\psi_{j,k}, f)$. Then
$$P_{V_J} f = P_{V_i} f + \sum_{l=i}^{J-1} P_{W_l} f,$$
and each term is the expansion that the book writes:
$$P_{V_i} f = \sum_{k \in \mathbb{Z}} a_k^i \, \phi(2^i x - k), \qquad P_{W_l} f = \sum_{k \in
  \mathbb{Z}} b_k^l \, \psi(2^l x - k) \quad \text{for every } l \in \mathbb{Z},$$
with both series convergent in $L^2(\mathbb{R})$.

This is the analysis step of Theorem 4.4.3 iterated from level $J$ down to level $i$. The book
states it for $f \in V_J$, written $f_J = f_i + w_i + \dots + w_{J-1}$. That is the case
$f \in V_J$ of this statement, since then $P_{V_J} f = f$. The series converge unconditionally
(`HasSum`). -/
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

/-- **Exercise 4.4.4** of [han2009theoretical]. The wavelets
$\psi_{j,k}(x) = 2^{j/2} \psi(2^j x - k)$, $j, k \in \mathbb{Z}$, form an orthonormal basis of
$L^2(\mathbb{R})$:

1. $(\psi_{i,k}, \psi_{j,l}) = \delta_{ij} \delta_{kl}$ for all $i, j, k, l \in \mathbb{Z}$;
2. every $f \in L^2(\mathbb{R})$ is the sum of the series $\sum_{(j,k) \in \mathbb{Z}^2}
   (\psi_{j,k}, f) \, \psi_{j,k}$, which converges unconditionally in $L^2(\mathbb{R})$.

The statement gives the expansion, and not the bundled basis `Haar.hilbertBasis`, because the
expansion is the form that a user needs. The proof uses `Haar.hilbertBasis`. -/
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
