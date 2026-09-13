import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Polynomial.CauchyBound
import Numlib.RingTheory.Polynomial.Horner
import Numlib.RingTheory.Polynomial.RuleOfSigns
import NumlibSurface.QuarteroniSaccoSaleri.Chapter06.Section03

/-!
# Quarteroni–Sacco–Saleri §6.4: zeros of algebraic equations

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §6.4: Descartes' rule of signs (Property 6.5) and Cauchy's bound
(Property 6.6) for localizing the zeros of a real polynomial, Horner's scheme (6.25)–(6.27) and
synthetic division (6.28), the deflation identity, the Newton–Horner method (6.29) with
`p'(z) = q(z; z)`, and Muller's method (6.30) with its cited order. Polynomials are `ℝ[X]`, the
book's real coefficients; the associated polynomial `q_{n-1}(·; z)` is `p /ₘ (X - C z)`. The
backbone is `Numlib/RingTheory/Polynomial/{Horner, RuleOfSigns}` over Mathlib's
`Polynomial.divByMonic`, `signVariations` and `cauchyBound`.

## Readings

* Property 6.5: Mathlib's `signVariations` ignores zero coefficients, as the book's "number of
  sign changes in `{a_j}`" must; the parity clause is the backbone's
  `even_signVariations_sub_roots_countP_pos`.
* Property 6.6 is stated for the complex zeros of the real polynomial through
  `p.map Complex.ofRealHom`; Mathlib's `cauchyBound` gives the strict inequality, the book's `≤`.
* (6.28): `g_m ∈ P_m` is read as a polynomial of degree exactly `m` (otherwise the remainder is not
  unique), and `ρ ∈ P_{m-1}` as `degree ρ < m`, which also covers `m = 0`.
* Muller's order `p ≈ 1.84` (`muller_order`) is not formalized: the book cites Hildebrand without
  proof and nothing depends on it.
-/

open Filter Polynomial Set Topology

namespace QuarteroniSaccoSaleri.Chapter06

/-! ### Localization of the zeros -/

section Localization

variable (p : ℝ[X])

/-- **Property 6.5 (Descartes' rule of signs), first half.** The number `k` of positive real roots
of `p`, counted with multiplicity, is at most the number `ν` of sign changes in its coefficients.
Mathlib's `Polynomial.roots_countP_pos_le_signVariations`. -/
theorem property_6_5 : p.roots.countP (0 < ·) ≤ p.signVariations :=
  roots_countP_pos_le_signVariations p

/-- **Property 6.5, second half.** `ν - k` is even. The backbone's
`Polynomial.even_signVariations_sub_roots_countP_pos`. -/
theorem property_6_5_parity (hp : p ≠ 0) : Even (p.signVariations - p.roots.countP (0 < ·)) :=
  even_signVariations_sub_roots_countP_pos hp

/-- **Property 6.6 (Cauchy's theorem).** All zeros of `p_n`, `n ≥ 1`, lie in the disc
`|z| ≤ 1 + η`, `η = max_{0 ≤ k ≤ n-1} |a_k / a_n|`. Mathlib's
`Polynomial.IsRoot.norm_lt_cauchyBound`, whose bound `sup ‖a_k‖₊ / ‖a_n‖₊ + 1` is `1 + η` and whose
inequality is strict. -/
theorem property_6_6 (hn : 0 < p.natDegree) {z : ℂ} (hz : (p.map Complex.ofRealHom).IsRoot z) :
    ‖z‖ ≤ 1 + (Finset.range p.natDegree).sup' (Finset.nonempty_range_iff.2 hn.ne')
      (fun k => |p.coeff k / p.leadingCoeff|) := by
  set η := (Finset.range p.natDegree).sup' (Finset.nonempty_range_iff.2 hn.ne')
    (fun k => |p.coeff k / p.leadingCoeff|) with hη
  have hp : p ≠ 0 := ne_zero_of_natDegree_gt hn
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hp
  have hbound := hz.norm_lt_cauchyBound (map_ne_zero hp)
  have hη0 : 0 ≤ η :=
    (abs_nonneg _).trans (Finset.le_sup' (fun k => |p.coeff k / p.leadingCoeff|)
      (Finset.mem_range.2 hn))
  -- the Cauchy bound of the complexified polynomial is at most `1 + η`
  have hcb : (cauchyBound (p.map Complex.ofRealHom) : ℝ) ≤ 1 + η := by
    rw [cauchyBound, NNReal.coe_add, NNReal.coe_one, NNReal.coe_div, add_comm]
    gcongr
    rw [div_le_iff₀ (by simpa [leadingCoeff_map, Complex.nnnorm_real] using hlc),
      leadingCoeff_map, Complex.ofRealHom_eq_coe, Complex.nnnorm_real, coe_nnnorm,
      Real.norm_eq_abs]
    have hη0' : 0 ≤ η * |p.leadingCoeff| := mul_nonneg hη0 (abs_nonneg _)
    have hS : ((Finset.range (p.map Complex.ofRealHom).natDegree).sup
        fun k => ‖(p.map Complex.ofRealHom).coeff k‖₊) ≤ (η * |p.leadingCoeff|).toNNReal := by
      refine Finset.sup_le fun k hk => ?_
      rw [natDegree_map] at hk
      rw [Real.le_toNNReal_iff_coe_le hη0', coe_nnnorm, coeff_map, Complex.ofRealHom_eq_coe,
        Complex.norm_real, Real.norm_eq_abs]
      calc |p.coeff k| = |p.coeff k / p.leadingCoeff| * |p.leadingCoeff| := by
            rw [abs_div, div_mul_cancel₀ _ (abs_ne_zero.2 hlc)]
        _ ≤ η * |p.leadingCoeff| := by
            gcongr
            exact Finset.le_sup' (fun k => |p.coeff k / p.leadingCoeff|) hk
    have := NNReal.coe_le_coe.2 hS
    rwa [Real.coe_toNNReal _ hη0'] at this
  calc ‖z‖ = (‖z‖₊ : ℝ) := (coe_nnnorm z).symm
    _ ≤ (cauchyBound (p.map Complex.ofRealHom) : ℝ) := by exact_mod_cast hbound.le
    _ ≤ 1 + η := hcb

end Localization

/-! ### §6.4.1 The Horner method and deflation -/

section Horner

variable (p : ℝ[X]) (z : ℝ)

/-- **(6.25)–(6.26), Horner's scheme and synthetic division.** The nested form
`a₀ + x (a₁ + x (a₂ + … ))` evaluates the polynomial (`Polynomial.hornerEval_coeffList`), and the
intermediate values `bₙ = aₙ`, `bₖ = aₖ + bₖ₊₁ z` of the synthetic division algorithm are the
coefficients of the quotient by `x - z` followed by `b₀ = p(z)`
(`Polynomial.hornerScan_coeffList`). -/
theorem equation_6_26 :
    hornerEval p.coeffList z = p.eval z ∧
      (p ≠ 0 → hornerScan p.coeffList z = (p /ₘ (X - C z)).coeffList ++ [p.eval z]) :=
  ⟨hornerEval_coeffList p z, fun hp => hornerScan_coeffList hp z⟩

/-- **(6.27), the associated polynomial** `q_{n-1}(x; z) = ∑_{k=1}^n b_k x^{k-1}` of `p_n`: the
quotient `p /ₘ (X - C z)` of the division by `x - z`. -/
noncomputable def equation_6_27 (p : ℝ[X]) (z : ℝ) : ℝ[X] := p /ₘ (X - C z)

/-- The associated polynomial of `p_n`, `n ≥ 1`, has degree `n - 1`.
`Polynomial.natDegree_divByMonic_X_sub_C`. -/
theorem equation_6_27_natDegree (hn : 0 < p.natDegree) :
    (equation_6_27 p z).natDegree = p.natDegree - 1 :=
  (natDegree_divByMonic_X_sub_C hn z).2

/-- The coefficients of the associated polynomial are the `b_k`, `k ≥ 1`, of (6.26): the `i`-th
entry of the synthetic division scan `[bₙ, …, b₁, b₀]` is `q.coeff (n - 1 - i)` for `i < n`.
`Polynomial.hornerEval_take_coeffList`. -/
theorem equation_6_27_coeff {i : ℕ} (hi : i < p.natDegree) :
    (hornerScan p.coeffList z)[i]'(by simp [coeffList,
      withBotSucc_degree_eq_natDegree_add_one (ne_zero_of_natDegree_gt hi)]; omega) =
      (equation_6_27 p z).coeff (p.natDegree - 1 - i) := by
  rw [getElem_hornerScan _ _ (by simp [coeffList,
    withBotSucc_degree_eq_natDegree_add_one (ne_zero_of_natDegree_gt hi)]; omega),
    hornerEval_take_coeffList p z hi]
  rfl

/-- **(6.28), division of polynomials.** Given `h_n ∈ P_n` and `g_m` of degree `m ≤ n`, there are
a unique `δ ∈ P_{n-m}` and a unique `ρ ∈ P_{m-1}` (i.e. `degree ρ < m`) with
`h_n = g_m δ + ρ`. Mathlib's `divByMonic`/`modByMonic` of the monic multiple `g · lc(g)⁻¹`, with
`div_modByMonic_unique` for the uniqueness. -/
theorem equation_6_28 {h g : ℝ[X]} {n m : ℕ} (hh : h.degree ≤ n) (hg : g.degree = m)
    (_hmn : m ≤ n) :
    ∃! δρ : ℝ[X] × ℝ[X], δρ.1.degree ≤ (n - m : ℕ) ∧ δρ.2.degree < m ∧ h = g * δρ.1 + δρ.2 := by
  have hg0 : g ≠ 0 := fun h0 => by simp [h0] at hg
  set g' : ℝ[X] := g * C g.leadingCoeff⁻¹ with hg'
  have hmonic : g'.Monic := monic_mul_leadingCoeff_inv hg0
  have hg'deg : g'.degree = m := by rw [hg', degree_mul_leadingCoeff_inv g hg0, hg]
  have hg'nat : g'.natDegree = m := natDegree_eq_of_degree_eq_some hg'deg
  have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hg0
  -- `g * (C lc⁻¹ * q) = g' * q`
  have hgq : ∀ q : ℝ[X], g * (C g.leadingCoeff⁻¹ * q) = g' * q := fun q => by
    rw [hg', mul_assoc]
  refine ⟨(C g.leadingCoeff⁻¹ * (h /ₘ g'), h %ₘ g'), ⟨?_, ?_, ?_⟩, ?_⟩
  · -- the degree of the quotient
    refine (degree_mul_le _ _).trans ?_
    rw [degree_C (inv_ne_zero hlc), zero_add]
    refine degree_le_natDegree.trans ?_
    rw [natDegree_divByMonic _ hmonic, hg'nat]
    exact_mod_cast Nat.sub_le_sub_right (natDegree_le_of_degree_le hh) m
  · rw [← hg'deg]
    exact degree_modByMonic_lt h hmonic
  · rw [hgq]
    conv_lhs => rw [← h.modByMonic_add_div g']
    exact add_comm _ _
  · rintro ⟨δ, ρ⟩ ⟨-, hρ, heq⟩
    have hunique := div_modByMonic_unique (f := h) (g := g') (C g.leadingCoeff * δ) ρ hmonic
      ⟨by rw [hg', mul_assoc, ← mul_assoc (C _), ← C_mul, inv_mul_cancel₀ hlc, C_1, one_mul,
        add_comm, heq], by rwa [hg'deg]⟩
    refine Prod.ext ?_ hunique.2.symm
    simp only
    rw [hunique.1, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hlc, C_1, one_mul]

/-- **The display after (6.28), synthetic division**: dividing `p_n` by `x - z` gives the
quotient `q_{n-1}(·; z)` and the remainder `b₀ = p_n(z)`,
`p_n(x) = b₀ + (x - z) q_{n-1}(x; z)`. `Polynomial.eq_X_sub_C_mul_divByMonic_add_C_eval`. -/
theorem hornerDivision : p = C (p.eval z) + (X - C z) * equation_6_27 p z := by
  rw [add_comm]
  exact eq_X_sub_C_mul_divByMonic_add_C_eval p z

/-- **Deflation** (§6.4.1). If `z` is a zero of `p_n` then `p_n(x) = (x - z) q_{n-1}(x; z)`
(Mathlib's `mul_divByMonic_eq_iff_isRoot`), and the equation `q_{n-1}(x; z) = 0` yields the
remaining `n - 1` roots of `p_n`, with multiplicities
(`Polynomial.roots_divByMonic_X_sub_C`). -/
theorem deflation (hz : p.IsRoot z) :
    p = (X - C z) * equation_6_27 p z ∧
      (p ≠ 0 → p.roots = (equation_6_27 p z).roots + {z}) :=
  ⟨(mul_divByMonic_eq_iff_isRoot.2 hz).symm, fun hp => roots_divByMonic_X_sub_C hp hz⟩

end Horner

/-! ### §6.4.2 The Newton–Horner method -/

section NewtonHorner

variable (p : ℝ[X]) (z : ℝ)

/-- **§6.4.2, `p_n'(z) = q_{n-1}(z; z)`**: since `p_n' = q_{n-1} + (x - z) q_{n-1}'`, the derivative
at `z` is the value of the associated polynomial at `z`.
`Polynomial.eval_divByMonic_X_sub_C_self`. -/
theorem derivative_eq_associatedPolynomial :
    p.derivative.eval z = (equation_6_27 p z).eval z :=
  (eval_divByMonic_X_sub_C_self p z).symm

/-- **(6.29), the Newton–Horner method**:
`r^{(k+1)} = r^{(k)} - p_n(r^{(k)}) / q_{n-1}(r^{(k)}; r^{(k)})`, the derivative supplied by
synthetic division. The iteration of the backbone's `NewtonHorner.step`; the complex-arithmetic
variant the book recommends for complex roots is the same definition over `ℂ[X]`. -/
noncomputable def equation_6_29 (p : ℝ[X]) (r₀ : ℝ) (k : ℕ) : ℝ := (NewtonHorner.step p)^[k] r₀

/-- The Newton–Horner method is Newton's method (6.16) for `f = p_n`: `NewtonHorner.step_eq`. So
`newton_order_two` and `equation_6_22` (with `Polynomial.isRootOfMultiplicity_eval_iff`) describe
its convergence. -/
theorem equation_6_29_eq_newton (r₀ : ℝ) (k : ℕ) :
    equation_6_29 p r₀ k = newton (fun x => p.eval x) (fun x => p.derivative.eval x) r₀ k := by
  rw [equation_6_29, newton]
  congr 1
  funext x
  rw [NewtonHorner.step_eq]
  rfl

end NewtonHorner

/-! ### §6.4.3 The Muller method -/

section Muller

/-- **(6.30), Muller's method**: from three distinct starting values `x^{(0)}, x^{(1)}, x^{(2)}`,
`x^{(k+1)} = x^{(k)} - 2 f(x^{(k)}) / (w ∓ √(w² - 4 f(x^{(k)}) f[x^{(k)}, x^{(k-1)}, x^{(k-2)}]))`,
the zero of the quadratic interpolant through the last three iterates with the sign maximizing the
modulus of the denominator. Real arithmetic only (`Muller.step`). -/
noncomputable def equation_6_30 (f : ℝ → ℝ) (x₀ x₁ x₂ : ℝ) (k : ℕ) : ℝ :=
  ((Muller.step f)^[k] (x₀, x₁, x₂)).2.2

end Muller

end QuarteroniSaccoSaleri.Chapter06
