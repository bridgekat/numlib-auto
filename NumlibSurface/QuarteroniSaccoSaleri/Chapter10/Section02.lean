import NumlibSurface.QuarteroniSaccoSaleri.Chapter10.Section01

/-!
# Quarteroni–Sacco–Saleri §10.2: Gaussian integration and interpolation

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §10.2.

For `n + 1` distinct nodes `x₀, …, x_n` of `[-1, 1]` and a weight `w`, the section studies the
weighted quadrature rules `I_{n,w}(f) = ∑ αᵢ f(xᵢ)` (10.13) and their *degree of exactness* `r`
with respect to `w` (`E_{n,w}(p) = I_w(p) - I_{n,w}(p) = 0` for every `p ∈ ℙ_r`): interpolatory
weights `αᵢ = ∫ lᵢ w` give degree of exactness at least `n` (10.14); Jacobi's theorem (Theorem
10.1) characterizes degree `n + m` by the orthogonality of the nodal polynomial `ω_{n+1}` to
`ℙ_{m-1}` (10.15); the maximal degree is `2n + 1` (Corollary 10.1), attained exactly by the Gauss
nodes, the zeros of `p_{n+1}` (10.16), whose weights are positive and whose nodes are interior;
the Gauss–Lobatto rule (10.17)–(10.18) includes the endpoints and has degree `2n - 1`, with its
interpolant (10.19); Remark 10.2 identifies its interior nodes for a Jacobi weight with the
extremants of the `n`-th Jacobi polynomial; Gaussian integration converges for every continuous
integrand; and Remark 10.3 transports a rule from `[-1, 1]` to `[a, b]`.

The backbone is the measure-level exactness theory of `Numlib/Approximation/Quadrature` —
`Quadrature.IsExactOnMeasure`, `Quadrature.IsInterpolatoryMeasure`, Jacobi's theorem
`Quadrature.isExactOnMeasure_add_iff` and its consequences, `Quadrature.exists_gauss`, the bridge
`Quadrature.isExactOnMeasure_iff_isExactOn` to the Szegő–Pólya criterion
`Quadrature.tendsto_of_nonneg`, and the affine transport
`Quadrature.isExactOnMeasure_volume_Icc_of_affine` — together with the Gauss–Lobatto construction
`Quadrature.exists_gaussLobatto` and the Jacobi identity
`Quadrature.derivative_family_jacobiMeasure` of `Numlib/Approximation/GaussLobatto`.

## Main results

* `isExactOnMeasure_iff_forall_sub_eq_zero` — "degree of exactness `r` with respect to `w`" as the
  book phrases it, `E_{n,w}(p) = 0` for all `p ∈ ℙ_r`.
* `equation_10_14` — interpolatory weights give degree of exactness at least `n`, and conversely;
  the rule is then the integral of the Lagrange interpolant.
* `theorem_10_1` — Jacobi's theorem; `corollary_10_1` — the maximal degree of exactness is
  `2n + 1`; `exists_gauss_nodes`, `equation_10_16` — the Gauss nodes are the `n + 1` zeros of
  `p_{n+1}`, and they alone give degree `2n + 1`; `gauss_weights_pos_nodes_mem_Ioo` — positivity of
  the Gauss weights and interiority of the Gauss nodes.
* `equation_10_18` — the Gauss–Lobatto rule: the nodes `x̄₀ = -1, …, x̄_n = 1` are the roots of
  `ω̄_{n+1} = p_{n+1} + a p_n + b p_{n-1}` with `ω̄_{n+1}(±1) = 0`, the weights `ᾱᵢ = ∫ l̄ᵢ w` are
  positive, and the degree of exactness is `2n - 1`; `equation_10_19` — its interpolant.
* `remark_10_2` — for a Jacobi weight the interior Gauss–Lobatto nodes are the zeros of
  `(J_n^{(α,β)})'`.
* `tendsto_of_isExactOnMeasure`, `gauss_tendsto`, `gaussLobatto_tendsto` — convergence of
  Gaussian and Gauss–Lobatto integration for every `f ∈ C⁰([-1, 1])`.
* `remark_10_3` — integration over an arbitrary interval.

## Conventions

A rule with `n + 1` nodes is a pair `x α : Fin (n + 1) → ℝ` of nodes and weights, "distinct" is
`Function.Injective x`, the weight `w(x) dx` is a measure `μ` with `OrthogonalPolynomial.IsWeight μ`
carried by `[-1, 1]` (`μ (Icc (-1) 1)ᶜ = 0`) where the interval matters, and "degree of exactness
`r`" is `Quadrature.IsExactOnMeasure μ α x r`: `∑ αᵢ p(xᵢ) = ∫ p ∂μ` for every real polynomial `p`
of degree at most `r`. The characteristic Lagrange polynomials `lᵢ` and the nodal polynomial
`ω_{n+1}` are Mathlib's `Lagrange.basis Finset.univ x i` and `Lagrange.nodal Finset.univ x`, as in
§8.1, and `{p_k}` is the monic orthogonal family `OrthogonalPolynomial.family μ` of §10.1. The
Gauss–Lobatto nodes are produced as an injective enumeration with `x̄ 0 = -1` and `x̄ n = 1`, the
book's labelling; the book's `J_n^{(α,β)}` is read as the monic `family (jacobiMeasure α β) n`,
which has the same zeros and the same extremants. Continuous functions on `[-1, 1]` are `ℝ → ℝ`
with `ContinuousOn f (Icc (-1) 1)`.
-/

open MeasureTheory Polynomial OrthogonalPolynomial Quadrature Real Set Filter Topology

namespace QuarteroniSaccoSaleri.Chapter10

variable {μ : Measure ℝ} {n : ℕ}

/-! ### Degree of exactness with respect to a weight, and interpolatory rules (10.13)–(10.14) -/

/-- **§10.2, the degree of exactness with respect to a weight**: the rule (10.13),
`I_{n,w}(f) = ∑ᵢ αᵢ f(xᵢ)`, has degree of exactness `r` with respect to `w` when the error
`E_{n,w}(p) = I_w(p) - I_{n,w}(p)` vanishes for every `p ∈ ℙ_r`. This is
`Quadrature.IsExactOnMeasure μ α x r`, the form used throughout the chapter. -/
theorem isExactOnMeasure_iff_forall_sub_eq_zero {m : ℕ} (α x : Fin m → ℝ) (r : ℕ) :
    IsExactOnMeasure μ α x r ↔
      ∀ p : ℝ[X], p.degree ≤ r → (∫ t, p.eval t ∂μ) - ∑ i, α i * p.eval (x i) = 0 :=
  forall₂_congr fun _ _ => by rw [sub_eq_zero, eq_comm]

-- TODO(backbone): an interpolatory rule is the integral of the Lagrange interpolant, at the
-- measure level; `Quadrature.isExactOn_iff_functional_eq` is the functional-level form.
/-- An interpolatory rule — weights `αᵢ = ∫ lᵢ ∂μ` — is the integral of the Lagrange
interpolant: `∑ᵢ αᵢ f(xᵢ) = ∫ Π_n f ∂μ` for every function `f`. -/
theorem sum_mul_eq_integral_interpolate (hw : IsWeight μ) {x α : Fin (n + 1) → ℝ}
    (hint : IsInterpolatoryMeasure μ α x) (f : ℝ → ℝ) :
    ∑ i, α i * f (x i) =
      ∫ t, (Lagrange.interpolate Finset.univ x fun i => f (x i)).eval t ∂μ := by
  simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C]
  rw [integral_finsetSum _ fun i _ => (hw.integrable_eval _).const_mul _]
  exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul, hint i, mul_comm]

/-- **(10.13)–(10.14).** For `n + 1` distinct nodes `x₀, …, x_n` and a weight `w`, the rule
`I_{n,w}(f) = ∑ᵢ αᵢ f(xᵢ)` has degree of exactness at least `n` exactly when its weights are

`αᵢ = ∫_{-1}^1 lᵢ(x) w(x) dx`, `i = 0, …, n`, (10.14)

with `lᵢ` the characteristic Lagrange polynomials of the nodes, and then
`I_{n,w}(f) = ∫_{-1}^1 Π_n f(x) w(x) dx` with `Π_n f` the Lagrange interpolant of `f` (8.4). The
backbone's `Quadrature.isInterpolatoryMeasure_iff_isExactOnMeasure`; the book states the
sufficiency, the converse being the remark of §9.1 that a formula on `n + 1` distinct nodes exact
on `ℙ_n` is interpolatory. -/
theorem equation_10_14 (hw : IsWeight μ) {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (α : Fin (n + 1) → ℝ) :
    ((∀ i, α i = ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂μ) ↔ IsExactOnMeasure μ α x n) ∧
      ((∀ i, α i = ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂μ) → ∀ f : ℝ → ℝ,
        ∑ i, α i * f (x i) =
          ∫ t, (Lagrange.interpolate Finset.univ x fun i => f (x i)).eval t ∂μ) :=
  ⟨isInterpolatoryMeasure_iff_isExactOnMeasure hw hx, fun hint f =>
    sum_mul_eq_integral_interpolate hw hint f⟩

/-! ### Theorem 10.1, Corollary 10.1 and the Gauss nodes (10.15)–(10.16) -/

/-- **Theorem 10.1 (Jacobi).** For a given `m > 0`, the quadrature formula (10.13) on `n + 1`
distinct nodes has degree of exactness `n + m` if and only if it is of interpolatory type and the
nodal polynomial `ω_{n+1}` (8.6) associated with the nodes satisfies

`∫_{-1}^1 ω_{n+1}(x) p(x) w(x) dx = 0` for all `p ∈ ℙ_{m-1}`. (10.15)

The backbone's `Quadrature.isExactOnMeasure_add_iff`. -/
theorem theorem_10_1 (hw : IsWeight μ) {m : ℕ} (hm : 0 < m) {x : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) (α : Fin (n + 1) → ℝ) :
    IsExactOnMeasure μ α x (n + m) ↔
      (∀ i, α i = ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂μ) ∧
        ∀ p : ℝ[X], p.degree ≤ ((m - 1 : ℕ) : WithBot ℕ) →
          ∫ t, (Lagrange.nodal Finset.univ x).eval t * p.eval t ∂μ = 0 :=
  isExactOnMeasure_add_iff hw hm hx α

/-- **Corollary 10.1.** The maximum degree of exactness of a quadrature formula (10.13) with
`n + 1` distinct nodes is `2n + 1`: no such rule is exact on `ℙ_{2n+2}`
(`Quadrature.not_isExactOnMeasure_two_mul_add_two`), and the Gauss rule
(`Quadrature.exists_gauss`) attains `2n + 1`. -/
theorem corollary_10_1 (hw : IsWeight μ) (n : ℕ) :
    IsGreatest {r | ∃ x α : Fin (n + 1) → ℝ, Function.Injective x ∧ IsExactOnMeasure μ α x r}
      (2 * n + 1) := by
  constructor
  · obtain ⟨x, α, hx, -, hexact⟩ := exists_gauss hw (n + 1)
    refine ⟨x, α, hx, isExactOnMeasure_iff_forall_degree_lt.mpr fun p hp => hexact p ?_⟩
    rwa [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]
  · rintro r ⟨x, α, -, hexact⟩
    by_contra hlt
    push Not at hlt
    exact not_isExactOnMeasure_two_mul_add_two hw α x (hexact.mono (by omega))

/-- **The Gauss nodes exist**: `p_{n+1}` has `n + 1` distinct real zeros, the abscissae (10.16).
The backbone's `OrthogonalPolynomial.exists_injective_family_eq_prod`. -/
theorem exists_gauss_nodes (hw : IsWeight μ) (n : ℕ) :
    ∃ x : Fin (n + 1) → ℝ, Function.Injective x ∧ ∀ j, (family μ (n + 1)).eval (x j) = 0 := by
  obtain ⟨x, hx, hprod⟩ := exists_injective_family_eq_prod hw (n + 1)
  refine ⟨x, hx, fun j => ?_⟩
  rw [hprod, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)

/-- **(10.16), the Gauss nodes.** A rule with `n + 1` distinct nodes has degree of exactness
`2n + 1` — the maximum of Corollary 10.1 — if and only if its nodes are the zeros of the
orthogonal polynomial `p_{n+1}`, `p_{n+1}(x_j) = 0` for `j = 0, …, n`, and its weights are given
by (10.14): this is the *Gauss quadrature formula*. The backbone's
`Quadrature.isExactOnMeasure_two_mul_add_one_iff`, the condition `ω_{n+1} = p_{n+1}` there being
equivalent, for distinct nodes, to `p_{n+1}` vanishing at every node
(`Quadrature.nodal_eq_family_of_forall_eval_eq_zero`). -/
theorem equation_10_16 (hw : IsWeight μ) {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (α : Fin (n + 1) → ℝ) :
    IsExactOnMeasure μ α x (2 * n + 1) ↔
      (∀ j, (family μ (n + 1)).eval (x j) = 0) ∧
        ∀ i, α i = ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂μ := by
  rw [isExactOnMeasure_two_mul_add_one_iff hw hx α]
  refine and_congr_left' ⟨fun h j => ?_, fun h => nodal_eq_family_of_forall_eval_eq_zero μ hx h⟩
  rw [← h]
  exact Lagrange.eval_nodal_at_node (Finset.mem_univ j)

-- TODO(backbone): `Quadrature.nodal_eq_family_of_forall_eval_eq_zero` for an arbitrary monic
-- polynomial of degree `n + 1` in place of `family μ (n + 1)`.
/-- A monic polynomial of degree `n + 1` vanishing at `n + 1` distinct points is their nodal
polynomial. -/
theorem nodal_eq_of_forall_eval_eq_zero {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    {q : ℝ[X]} (hq : q.Monic) (hdeg : q.natDegree = n + 1) (hroot : ∀ i, q.eval (x i) = 0) :
    Lagrange.nodal Finset.univ x = q := by
  refine sub_eq_zero.mp (Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ
    hx.injOn ?_ fun i _ => ?_)
  · have := degree_sub_lt_left (p := Lagrange.nodal Finset.univ x) (q := q)
      (by rw [Lagrange.degree_nodal, degree_eq_natDegree hq.ne_zero, hdeg]; simp)
      Lagrange.nodal_ne_zero (by rw [Lagrange.nodal_monic.leadingCoeff, hq.leadingCoeff])
    rwa [Lagrange.degree_nodal] at this
  · rw [eval_sub, hroot i, Lagrange.eval_nodal_at_node (Finset.mem_univ i), sub_zero]

/-- A point is a node of an injective family exactly when the nodal polynomial vanishes there. -/
theorem exists_eq_iff_eval_nodal_eq_zero (x : Fin (n + 1) → ℝ) (t : ℝ) :
    (∃ i, x i = t) ↔ (Lagrange.nodal Finset.univ x).eval t = 0 := by
  rw [Lagrange.eval_nodal, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, sub_eq_zero]
  exact exists_congr fun i => eq_comm

-- TODO(backbone): the weights of a rule with `n + 1` distinct nodes exact to degree `≥ 2n` are
-- positive (the test polynomial `lᵢ²` in `Quadrature.pos_of_isExactOnMeasure`); the Gauss and
-- Gauss–Lobatto rules are both instances.
/-- The weights of a rule with `n + 1` distinct nodes and degree of exactness at least `2n` are
positive: exactness on `lᵢ² ∈ ℙ_{2n}` gives `αᵢ = ∫ lᵢ² ∂μ > 0`. -/
theorem pos_of_isExactOnMeasure_of_le (hw : IsWeight μ) {x α : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) {d : ℕ} (hd : 2 * n ≤ d) (hexact : IsExactOnMeasure μ α x d)
    (i : Fin (n + 1)) : 0 < α i := by
  refine pos_of_isExactOnMeasure hw hexact (p := Lagrange.basis Finset.univ x i ^ 2) ?_
    (pow_ne_zero 2 (Lagrange.basis_ne_zero hx.injOn (Finset.mem_univ i)))
    (Eventually.of_forall fun t => by rw [eval_pow]; positivity) i (fun k hk => ?_) ?_
  · refine degree_le_of_natDegree_le ?_
    rw [natDegree_pow, Lagrange.natDegree_basis hx.injOn (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin, Nat.add_sub_cancel]
    exact hd
  · rw [eval_pow, Lagrange.eval_basis_of_ne (Ne.symm hk) (Finset.mem_univ k)]
    norm_num
  · rw [eval_pow, Lagrange.eval_basis_self hx.injOn (Finset.mem_univ i)]
    norm_num

/-- **§10.2, after (10.16).** The weights of the Gauss quadrature formula — a rule with `n + 1`
distinct nodes and degree of exactness `2n + 1` — are all positive, and its nodes are internal to
the interval `(-1, 1)` when the weight is carried by `[-1, 1]` (the book cites [CHQZ88], p. 56).
Positivity is exactness on `lᵢ²`; the location is
`OrthogonalPolynomial.root_family_mem_Ioo`, the nodes being the zeros of `p_{n+1}` by (10.16). -/
theorem gauss_weights_pos_nodes_mem_Ioo (hw : IsWeight μ) (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0)
    {x α : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (hexact : IsExactOnMeasure μ α x (2 * n + 1)) :
    (∀ i, 0 < α i) ∧ ∀ i, x i ∈ Ioo (-1 : ℝ) 1 :=
  ⟨pos_of_isExactOnMeasure_of_le hw hx (by omega) hexact, fun i =>
    root_family_mem_Ioo hw hsupp (((equation_10_16 hw hx α).mp hexact).1 i)⟩

/-! ### The Gauss–Lobatto formula (10.17)–(10.19) -/

/-- **(10.17)–(10.18), the Gauss–Lobatto formula.** For a weight `w` on `[-1, 1]` and `n ≥ 1`, the
polynomial `ω̄_{n+1} = p_{n+1} + a p_n + b p_{n-1}` (10.17), with the constants `a`, `b` selected
so that `ω̄_{n+1}(-1) = ω̄_{n+1}(1) = 0` — which determines `ω̄_{n+1}` — has `n + 1` distinct real
roots `x̄₀ = -1, x̄₁, …, x̄_n = 1` in `[-1, 1]`; with the weights `ᾱᵢ = ∫_{-1}^1 l̄ᵢ w` of (10.14),
which are positive, the formula

`I^{GL}_{n,w}(f) = ∑ᵢ ᾱᵢ f(x̄ᵢ)` (10.18)

is the *Gauss–Lobatto formula* with `n + 1` nodes and has degree of exactness `2n - 1`. The
backbone's `Quadrature.exists_gaussLobatto`, with `Quadrature.lobattoNodal_eq_add_smul` and
`Quadrature.eq_lobattoNodal_of_eval_eq_zero` for the form (10.17) of the nodal polynomial. -/
theorem equation_10_18 (hw : IsWeight μ) (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0) (hn : 1 ≤ n) :
    ∃ x α : Fin (n + 1) → ℝ, Function.Injective x ∧ x 0 = -1 ∧ x (Fin.last n) = 1 ∧
      (∀ i, x i ∈ Icc (-1 : ℝ) 1) ∧
      (∃ a b : ℝ, Lagrange.nodal Finset.univ x =
          family μ (n + 1) + C a * family μ n + C b * family μ (n - 1) ∧
        (family μ (n + 1) + C a * family μ n + C b * family μ (n - 1)).eval (-1) = 0 ∧
        (family μ (n + 1) + C a * family μ n + C b * family μ (n - 1)).eval 1 = 0) ∧
      (∀ a b : ℝ, (family μ (n + 1) + C a * family μ n + C b * family μ (n - 1)).eval (-1) = 0 →
        (family μ (n + 1) + C a * family μ n + C b * family μ (n - 1)).eval 1 = 0 →
        family μ (n + 1) + C a * family μ n + C b * family μ (n - 1) =
          Lagrange.nodal Finset.univ x) ∧
      (∀ i, α i = ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂μ) ∧ (∀ i, 0 < α i) ∧
      IsExactOnMeasure μ α x (2 * n - 1) := by
  obtain ⟨x, α, hxinj, hx0, hxlast, hxmem, hpos, hexact, hnodal, hint⟩ :=
    exists_gaussLobatto hw hsupp hn
  obtain ⟨a, b, hab⟩ := lobattoNodal_eq_add_smul hw hsupp hn
  refine ⟨x, α, hxinj, hx0, hxlast, hxmem, ⟨a, b, hnodal.trans hab, ?_, ?_⟩, ?_, hint, hpos, hexact⟩
  · rw [← hab]
    exact lobattoNodal_eval_neg_one μ n
  · rw [← hab]
    exact lobattoNodal_eval_one μ n
  · intro a' b' h1 h2
    rw [hnodal]
    exact eq_lobattoNodal_of_eval_eq_zero hw hsupp hn h2 h1

/-- **(10.19).** Denoting by `Π^{GL}_{n,w} f` the polynomial of degree `n` that interpolates `f` at
the Gauss–Lobatto nodes `x̄ⱼ`, `Π^{GL}_{n,w} f(x) = ∑ᵢ f(x̄ᵢ) l̄ᵢ(x)`, and the Gauss–Lobatto formula
is its integral: `I^{GL}_{n,w}(f) = ∫_{-1}^1 Π^{GL}_{n,w} f(x) w(x) dx`. Stated for any rule with
the interpolatory weights `ᾱᵢ = ∫ l̄ᵢ w`, which the Gauss–Lobatto rule of `equation_10_18` has. -/
theorem equation_10_19 (hw : IsWeight μ) {x α : Fin (n + 1) → ℝ}
    (hint : ∀ i, α i = ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂μ) (f : ℝ → ℝ) :
    (Lagrange.interpolate Finset.univ x fun i => f (x i)) =
        ∑ i, C (f (x i)) * Lagrange.basis Finset.univ x i ∧
      ∑ i, α i * f (x i) =
        ∫ t, (Lagrange.interpolate Finset.univ x fun i => f (x i)).eval t ∂μ :=
  ⟨Lagrange.interpolate_apply _ _ _, sum_mul_eq_integral_interpolate hw hint f⟩

/-! ### Remark 10.2: the Gauss–Lobatto nodes of a Jacobi weight -/

-- TODO(backbone): the Jacobi weights are carried by `[-1, 1]`; belongs beside
-- `OrthogonalPolynomial.isWeight_jacobiMeasure`.
/-- The Jacobi weight `(1 - x)^α (1 + x)^β dx` on `(-1, 1)` gives no mass outside `[-1, 1]`. -/
theorem jacobiMeasure_compl_Icc (α β : ℝ) : jacobiMeasure α β (Icc (-1 : ℝ) 1)ᶜ = 0 := by
  refine withDensity_absolutelyContinuous _ _ ?_
  rw [Measure.restrict_apply' measurableSet_Ioo]
  have hempty : (Icc (-1 : ℝ) 1)ᶜ ∩ Ioo (-1 : ℝ) 1 = ∅ :=
    Set.eq_empty_of_forall_notMem fun t ht => ht.1 (Ioo_subset_Icc_self ht.2)
  rw [hempty, measure_empty]

-- TODO(backbone): the modified weight `(1 - x²) · jacobiMeasure α β` is
-- `jacobiMeasure (α + 1) (β + 1)`; `OrthogonalPolynomial.jacobiMeasure_one_one` is the case
-- `α = β = 0` of it, and `Quadrature.derivative_family_jacobiMeasure` is stated through it.
/-- The Lobatto weight of a Jacobi weight is the Jacobi weight with both exponents raised by
one. -/
theorem lobattoMeasure_jacobiMeasure (α β : ℝ) :
    lobattoMeasure (jacobiMeasure α β) = jacobiMeasure (α + 1) (β + 1) := by
  rw [lobattoMeasure, jacobiMeasure, jacobiMeasure, ← withDensity_mul _ (by fun_prop) (by fun_prop)]
  refine withDensity_congr_ae ?_
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  refine Eventually.of_forall fun x hx => ?_
  have h1 : 1 - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx.2)
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h1' : 0 ≤ 1 - x := by linarith [hx.2]
  have h2' : 0 ≤ 1 + x := by linarith [hx.1]
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (by positivity), rpow_add_one h1, rpow_add_one h2]
  congr 1
  ring

/-- **Remark 10.2.** For the Gauss–Lobatto quadrature with respect to the Jacobi weight
`w(x) = (1 - x)^α (1 + x)^β`, `α, β > -1` (the book prints `(1 - x)^α (1 - x)^β`), the internal
nodes `x̄₁, …, x̄_{n-1}` are the roots of the polynomial `(J_n^{(α,β)})'`, the extremants of the
`n`-th Jacobi polynomial: a point of `(-1, 1)` is a node exactly when it is a zero of the derivative
of the `n`-th orthogonal polynomial of the weight. The nodes are described as in (10.17), the
`n + 1` distinct roots of `p_{n+1} + a p_n + b p_{n-1}` with the combination vanishing at `±1`.
The backbone's `Quadrature.derivative_family_jacobiMeasure`:
`(J_n^{(α,β)})' = n J_{n-1}^{(α+1,β+1)}` for the monic families, and the Lobatto nodal polynomial is
`(x² - 1) J_{n-1}^{(α+1,β+1)}`. -/
theorem remark_10_2 {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (hn : 1 ≤ n) {a b : ℝ}
    (h1 : (family (jacobiMeasure α β) (n + 1) + C a * family (jacobiMeasure α β) n +
      C b * family (jacobiMeasure α β) (n - 1)).eval (-1) = 0)
    (h2 : (family (jacobiMeasure α β) (n + 1) + C a * family (jacobiMeasure α β) n +
      C b * family (jacobiMeasure α β) (n - 1)).eval 1 = 0)
    {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (hroot : ∀ i, (family (jacobiMeasure α β) (n + 1) + C a * family (jacobiMeasure α β) n +
      C b * family (jacobiMeasure α β) (n - 1)).eval (x i) = 0) :
    ∀ t ∈ Ioo (-1 : ℝ) 1,
      (∃ i, x i = t) ↔ (derivative (family (jacobiMeasure α β) n)).eval t = 0 := by
  have hw := isWeight_jacobiMeasure hα hβ
  have hsupp := jacobiMeasure_compl_Icc α β
  have hω := eq_lobattoNodal_of_eval_eq_zero hw hsupp hn h2 h1
  rw [hω] at hroot
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hder := derivative_family_jacobiMeasure hα hβ hn
  rw [← lobattoMeasure_jacobiMeasure] at hder
  intro t ht
  have ht' : t ^ 2 - 1 ≠ 0 := by nlinarith [ht.1, ht.2]
  -- `t` is a node iff `ω̄_{n+1}(t) = 0`
  have hnodal : Lagrange.nodal Finset.univ x = lobattoNodal (jacobiMeasure α β) n :=
    nodal_eq_of_forall_eval_eq_zero hx (lobattoNodal_monic _ _)
      (natDegree_eq_of_degree_eq_some (degree_lobattoNodal _ hn)) hroot
  rw [exists_eq_iff_eval_nodal_eq_zero, hnodal, lobattoNodal, hder, eval_mul, eval_mul, eval_sub,
    eval_pow, eval_X, eval_one, eval_C, mul_eq_zero, mul_eq_zero, or_iff_right ht',
    or_iff_right hnR]

/-! ### Convergence of Gaussian integration -/

/-- The integral against a finite measure on `[a, b]` as a bounded functional on `C([a, b], ℝ)`.
-/
private noncomputable def integralCLM {a b : ℝ} (ν : Measure (Icc a b)) [IsFiniteMeasure ν] :
    C(Icc a b, ℝ) →L[ℝ] ℝ :=
  (L1.integralCLM (α := Icc a b) (E := ℝ) (μ := ν)).comp (ContinuousMap.toLp 1 ν ℝ)

private theorem integralCLM_apply {a b : ℝ} (ν : Measure (Icc a b)) [IsFiniteMeasure ν]
    (f : C(Icc a b, ℝ)) : integralCLM ν f = ∫ t, f t ∂ν := by
  rw [integralCLM, ContinuousLinearMap.comp_apply, ← L1.integral_eq, L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (μ := ν) (𝕜 := ℝ) f)

-- TODO(backbone): the Szegő–Pólya criterion `Quadrature.tendsto_of_nonneg` read at the measure
-- level for real functions continuous on `[a, b]`, through
-- `Quadrature.isExactOnMeasure_iff_isExactOn`; the Gauss, Gauss–Lobatto, Chebyshev and Legendre
-- convergence statements are all instances.
/-- **Convergence of quadrature rules with nonnegative weights.** For a finite weight `μ` carried
by `[a, b]`, rules with distinct nodes in `[a, b]`, nonnegative weights and degrees of exactness
`d k → ∞` for `μ` converge to `∫ f ∂μ` for every `f` continuous on `[a, b]`. -/
theorem tendsto_of_isExactOnMeasure [IsFiniteMeasure μ] {a b : ℝ} (hsupp : μ (Icc a b)ᶜ = 0)
    {m d : ℕ → ℕ} {x α : ∀ k, Fin (m k) → ℝ} (hx : ∀ k, Function.Injective (x k))
    (hmem : ∀ k i, x k i ∈ Icc a b) (hα : ∀ k i, 0 ≤ α k i) (hd : Tendsto d atTop atTop)
    (hexact : ∀ k, IsExactOnMeasure μ (α k) (x k) (d k)) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun k => ∑ i, α k i * f (x k i)) atTop (𝓝 (∫ t, f t ∂μ)) := by
  set ν : Measure (Icc a b) := μ.comap Subtype.val with hν
  set L : C(Icc a b, ℝ) →L[ℝ] ℝ := integralCLM ν with hL
  have hLapply : ∀ g : C(Icc a b, ℝ), L g = ∫ t, g t ∂(μ.comap Subtype.val) := fun g =>
    integralCLM_apply ν g
  set x' : ∀ k, Fin (m k) → Icc a b := fun k i => ⟨x k i, hmem k i⟩ with hx'
  have hx'inj : ∀ k, Function.Injective (x' k) := fun k i j h =>
    hx k (congrArg Subtype.val h)
  have hexact' : ∀ k, IsExactOn L (α k) (x' k) (d k) := fun k =>
    (isExactOnMeasure_iff_isExactOn hsupp (α k) (x' k) hLapply (d k)).mp (hexact k)
  set g : C(Icc a b, ℝ) := ⟨fun t => f t, hf.domRestrict⟩ with hg
  have hae : ∀ᵐ t ∂μ, t ∈ Icc a b := by
    rw [MeasureTheory.ae_iff]
    exact hsupp
  have hLg : L g = ∫ t, f t ∂μ := by
    rw [hLapply]
    have h1 := integral_subtype_comap (μ := μ) (s := Icc a b) measurableSet_Icc fun t => f t
    rw [Measure.restrict_eq_self_of_ae_mem hae] at h1
    exact h1
  have h := tendsto_of_nonneg hx'inj hd hexact' hα g
  rw [hLg] at h
  refine h.congr fun k => ?_
  rw [functional_apply]
  rfl

/-- **§10.2, the convergence of Gaussian integration** (the book cites [Atk89], Chapter 5). For a
weight `w` carried by `[-1, 1]`, the Gauss formulae with `n + 1` nodes — rules with `n + 1`
distinct nodes and degree of exactness `2n + 1` — satisfy

`lim_{n → ∞} |∫_{-1}^1 f(x) w(x) dx - ∑ⱼ αⱼ f(xⱼ)| = 0` for all `f ∈ C⁰([-1, 1])`.

The Szegő–Pólya criterion `tendsto_of_isExactOnMeasure`, the weights being positive and the nodes
interior by `gauss_weights_pos_nodes_mem_Ioo`. -/
theorem gauss_tendsto (hw : IsWeight μ) (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0)
    {x α : ∀ k : ℕ, Fin (k + 1) → ℝ} (hx : ∀ k, Function.Injective (x k))
    (hexact : ∀ k, IsExactOnMeasure μ (α k) (x k) (2 * k + 1)) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    Tendsto (fun k => |(∫ t, f t ∂μ) - ∑ j, α k j * f (x k j)|) atTop (𝓝 0) := by
  have := hw.isFiniteMeasure
  have h := tendsto_of_isExactOnMeasure hsupp hx
    (fun k i => Ioo_subset_Icc_self ((gauss_weights_pos_nodes_mem_Ioo hw hsupp (hx k)
      (hexact k)).2 i))
    (fun k i => ((gauss_weights_pos_nodes_mem_Ioo hw hsupp (hx k) (hexact k)).1 i).le)
    (tendsto_atTop_atTop.mpr fun N => ⟨N, fun k hk => by omega⟩) hexact hf
  rw [tendsto_iff_norm_sub_tendsto_zero] at h
  refine h.congr fun k => ?_
  rw [Real.norm_eq_abs, abs_sub_comm]

/-- **§10.2, "a similar result also holds for Gauss–Lobatto integration"**: for a weight carried
by `[-1, 1]` and the Gauss–Lobatto formulae with `n + 1` nodes, `n ≥ 1` — rules with distinct
nodes in `[-1, 1]`, positive weights and degree of exactness `2n - 1`, as `equation_10_18`
provides — `∑ⱼ ᾱⱼ f(x̄ⱼ) → ∫_{-1}^1 f w` for every `f ∈ C⁰([-1, 1])`. Indexed by `k = n - 1`. -/
theorem gaussLobatto_tendsto (hw : IsWeight μ) (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0)
    {x α : ∀ k : ℕ, Fin (k + 2) → ℝ} (hx : ∀ k, Function.Injective (x k))
    (hmem : ∀ k i, x k i ∈ Icc (-1 : ℝ) 1) (hα : ∀ k i, 0 < α k i)
    (hexact : ∀ k, IsExactOnMeasure μ (α k) (x k) (2 * (k + 1) - 1)) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    Tendsto (fun k => |(∫ t, f t ∂μ) - ∑ j, α k j * f (x k j)|) atTop (𝓝 0) := by
  have := hw.isFiniteMeasure
  have h := tendsto_of_isExactOnMeasure hsupp hx hmem (fun k i => (hα k i).le)
    (tendsto_atTop_atTop.mpr fun N => ⟨N, fun k hk => by omega⟩) hexact hf
  rw [tendsto_iff_norm_sub_tendsto_zero] at h
  refine h.congr fun k => ?_
  rw [Real.norm_eq_abs, abs_sub_comm]

/-! ### Remark 10.3: integration over an arbitrary interval -/

/-- **Remark 10.3 (integration over an arbitrary interval).** A quadrature formula with nodes `ξⱼ`
and coefficients `βⱼ` over `[-1, 1]` can be mapped onto any interval `[a, b]`: with the affine map
`φ(ξ) = ((b - a)/2) ξ + (a + b)/2` from `[-1, 1]` onto `[a, b]`,

`∫_a^b f(x) dx = ((b - a)/2) ∫_{-1}^1 (f ∘ φ)(ξ) dξ`,

so the formula with nodes `xⱼ = φ(ξⱼ)` and weights `αⱼ = ((b - a)/2) βⱼ` maintains on `[a, b]` the
degree of exactness `r` of the generating formula. The backbone's
`Quadrature.isExactOnMeasure_volume_Icc_of_affine`. Erratum: the book prints the map as
`φ(ξ) = ((a + b)/2) ξ + (b - a)/2` and the factor as `(a + b)/2`; both read as here, the printed map
not sending `[-1, 1]` onto `[a, b]`. -/
theorem remark_10_3 {a b : ℝ} (hab : a < b) {m : ℕ} {ξ β : Fin m → ℝ} {r : ℕ}
    (h : ∀ p : ℝ[X], p.degree ≤ r → ∑ j, p.eval (ξ j) * β j = ∫ t in (-1 : ℝ)..1, p.eval t) :
    (∀ f : ℝ → ℝ, ∫ t in a..b, f t =
        (b - a) / 2 * ∫ t in (-1 : ℝ)..1, f ((b - a) / 2 * t + (a + b) / 2)) ∧
      ∀ q : ℝ[X], q.degree ≤ r →
        ∑ j, q.eval ((b - a) / 2 * ξ j + (a + b) / 2) * ((b - a) / 2 * β j) =
          ∫ t in a..b, q.eval t := by
  have hIcc : ∀ (c d : ℝ) (g : ℝ → ℝ), c ≤ d → ∫ t in Icc c d, g t = ∫ t in c..d, g t := by
    intro c d g hcd
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcd]
  constructor
  · intro f
    rw [← smul_eq_mul, intervalIntegral.smul_integral_comp_mul_add,
      show (b - a) / 2 * (-1) + (a + b) / 2 = a by ring,
      show (b - a) / 2 * 1 + (a + b) / 2 = b by ring]
  · have h' : IsExactOnMeasure (volume.restrict (Icc (-1 : ℝ) 1)) β ξ r := fun p hp => by
      rw [hIcc _ _ _ (by norm_num), ← h p hp]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    intro q hq
    have := isExactOnMeasure_volume_Icc_of_affine hab h' q hq
    rw [hIcc _ _ _ hab.le] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end QuarteroniSaccoSaleri.Chapter10
