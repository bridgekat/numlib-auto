import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ChebyshevGauss
import NumlibSurface.QuarteroniSaccoSaleri.Chapter10.Section02
import NumlibSurface.QuarteroniSaccoSaleri.Chapter10.Section08

/-!
# Quarteroni–Sacco–Saleri §10.3: Chebyshev integration and interpolation

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §10.3.

For the Chebyshev weight `w(x) = (1 - x²)^{-1/2}` the Gauss nodes and weights are
`xⱼ = -cos((2j + 1)π/(2(n + 1)))`, `αⱼ = π/(n + 1)` (10.20) — the zeros of `T_{n+1}` — and the
Gauss–Lobatto nodes and weights are `x̄ⱼ = -cos(πj/n)`, `ᾱⱼ = π/(dⱼ n)` with `d₀ = d_n = 2`,
`dⱼ = 1` otherwise (10.21), the interior nodes being the zeros of `T_n' = n U_{n-1}`. The section
then quotes the weighted-Sobolev estimates (10.22), (10.24), (10.26)–(10.27) for the norm
`‖f‖_{s,w}` (10.23) and the Lebesgue-constant bound (10.25), states that the Gauss–Lobatto formula
converges, introduces the discrete scalar product `(f, g)_n = I^{GL}_{n,w}(fg)` (10.28), and derives
the Chebyshev discrete transform: the interpolant at the Gauss–Lobatto nodes is
`∑_{k ≤ n} f̃_k T_k` (10.29) with `f̃_k = (2/(n d_k)) ∑_{j ≤ n} dⱼ⁻¹ cos(kjπ/n) f(x̄ⱼ)` (10.31), and
`f(x̄ⱼ) = ∑_k cos(kjπ/n) f̃_k` (10.30).

The Gauss rule is Mathlib's `Polynomial.Chebyshev.integral_eq_sumZeroes`; the Gauss–Lobatto rule,
the discrete norms of the `T_k` and the discrete transform are
`Polynomial.Chebyshev.integral_eq_sumExtrema`, `discreteInner_T_T` and `interpolate_eq_sum_cdt` of
`Numlib/Approximation/GaussLobatto`, stated there at Mathlib's nodes `cos(jπ/n)`
(`Polynomial.Chebyshev.node`); the book's nodes are these reversed, `x̄ⱼ = node n (n - j)`, and
every statement here is transported along `j ↦ n - j`. Convergence is the Szegő–Pólya criterion in
the form `tendsto_of_isExactOnMeasure` of §10.2.

## Main definitions

* `chebyshevGaussNode n j`, `chebyshevLobattoNode n j` — the nodes (10.20) and (10.21) with the
  book's sign; the weights and the factors `dⱼ` are the backbone's
  `Polynomial.Chebyshev.lobattoWeight` and `lobattoFactor`, whose values are restated.
* `equation_10_23 μ s f` — the weighted Sobolev norm `‖f‖_{s,μ}` of (10.23) (and (10.35)).
* `equation_10_28 n f g` — the discrete scalar product `(f, g)_n` of the Gauss–Lobatto rule.
* `chebyshevDiscreteCoeff n f k` — the discrete coefficients `f̃_k` of (10.31).

## Main results

* `equation_10_20` — the Chebyshev–Gauss formula: increasing nodes, the zeros of `T_{n+1}`, exact
  on `ℙ_{2n+1}`.
* `equation_10_21` — the Chebyshev–Gauss–Lobatto formula: increasing nodes from `-1` to `1`, the
  factors `dⱼ` and weights, exactness on `ℙ_{2n-1}`, and the interior nodes as zeros of
  `T_n' = n U_{n-1}`.
* `chebyshevGaussNode_mem_Icc`, `equation_10_25_interpolation_error` — the first half of (10.25),
  `‖f - Π^G_n f‖_∞ ≤ (1 + Λ_n) E_n^*(f)` at the Chebyshev nodes, from §10.8.
* `lobatto_tendsto` — `I^{GL}_{n,w}(f) → ∫_{-1}^1 f (1 - x²)^{-1/2} dx` for `f ∈ C⁰([-1, 1])`.
* `equation_10_31` — the Chebyshev discrete transform (10.29)–(10.31) and the identification of
  the interpolant with the discrete truncation `f_n^*` of (10.4).

## Not formalized

`equation_10_22`, `equation_10_24`, `equation_10_27` are the weighted-Sobolev estimates quoted from
[CHQZ88] without proof; `equation_10_25` waits on the bound `Λ_n ≤ (2/π) log(n + 1) + 1` for the
Lebesgue constant of the Chebyshev nodes (`Lagrange.norm_interpolateCLM_chebyshev_le`, an open
backbone node), its first inequality being `equation_10_25_interpolation_error`. The plan carries
them.

## Conventions

The book's node index `j` runs over `Fin (n + 1)`; the nodes are increasing in `j`, so the book's
`x̄₀ = -1`, `x̄_n = 1`. Erratum: (10.30)–(10.31) are printed with `cos(kjπ/n)`, which is
`T_k(cos(jπ/n)) = T_k(x̄_{n-j})`, not `T_k(x̄ⱼ)`; with the node ordering of (10.21) both formulas
read with `cos(k(n - j)π/n) = (-1)^k cos(kjπ/n)`, equivalently they are the formulas for the
nodes `cos(jπ/n)`. They are stated here in the corrected form.
-/

open MeasureTheory Polynomial OrthogonalPolynomial Quadrature Real Set Filter Topology

namespace QuarteroniSaccoSaleri.Chapter10

variable {n : ℕ}

/-! ### Reindexing a quadrature rule -/

-- TODO(backbone): exactness is invariant under a permutation of the nodes.
/-- Permuting the nodes and weights of a rule together does not change its exactness. -/
theorem isExactOnMeasure_comp_equiv {μ : Measure ℝ} {m : ℕ} {w x : Fin m → ℝ}
    (σ : Equiv.Perm (Fin m)) {d : ℕ} :
    IsExactOnMeasure μ (w ∘ σ) (x ∘ σ) d ↔ IsExactOnMeasure μ w x d := by
  simp only [IsExactOnMeasure, Function.comp_apply]
  exact forall₂_congr fun p _ => by rw [Equiv.sum_comp σ fun i => w i * p.eval (x i)]

-- TODO(backbone): the Lagrange interpolant does not depend on the enumeration of the nodes.
/-- The interpolant at a reindexed family of nodes is the interpolant at the original family. -/
theorem interpolate_comp_equiv {m : ℕ} {x : Fin m → ℝ} (hx : Function.Injective x)
    (σ : Equiv.Perm (Fin m)) (f : ℝ → ℝ) :
    (Lagrange.interpolate Finset.univ (x ∘ σ) fun i => f ((x ∘ σ) i)) =
      Lagrange.interpolate Finset.univ x fun i => f (x i) := by
  have hxσ : Function.Injective (x ∘ σ) := hx.comp σ.injective
  have hdeg : (Lagrange.interpolate Finset.univ (x ∘ σ) fun i => f ((x ∘ σ) i)).degree <
      (Finset.univ : Finset (Fin m)).card :=
    Lagrange.degree_interpolate_lt _ hxσ.injOn
  have hev : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      (Lagrange.interpolate Finset.univ (x ∘ σ) fun i => f ((x ∘ σ) i)).eval (x i) = f (x i) := by
    intro i _
    have h := Lagrange.eval_interpolate_at_node (fun i => f ((x ∘ σ) i)) hxσ.injOn
      (Finset.mem_univ (σ.symm i))
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at h
    exact h
  exact Lagrange.eq_interpolate_of_eval_eq _ hx.injOn hdeg hev

/-! ### The Chebyshev–Gauss formula (10.20) -/

/-- **(10.20), the Chebyshev–Gauss nodes** `xⱼ = -cos((2j + 1)π/(2(n + 1)))`, `0 ≤ j ≤ n`. -/
noncomputable def chebyshevGaussNode (n j : ℕ) : ℝ := -cos ((2 * j + 1) * π / (2 * (n + 1)))

/-- The book's Gauss node `xⱼ` is Mathlib's node `cos((2(n - j) + 1)/(2(n + 1)) π)` of
`Polynomial.Chebyshev.sumZeroes`: the same set of points, enumerated in the opposite order. -/
theorem chebyshevGaussNode_eq {j : ℕ} (hj : j ≤ n) :
    chebyshevGaussNode n j = cos ((2 * ((n - j : ℕ) : ℝ) + 1) / (2 * ((n + 1 : ℕ) : ℝ)) * π) := by
  rw [chebyshevGaussNode, ← cos_pi_sub, Nat.cast_sub hj]
  congr 1
  have : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- The angle `(2j + 1)π/(2(n + 1))` lies in `[0, π]` for `j ≤ n`. -/
private theorem gaussAngle_mem_Icc {j : ℕ} (hj : j ≤ n) :
    (2 * (j : ℝ) + 1) * π / (2 * ((n : ℝ) + 1)) ∈ Icc 0 π := by
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  have : (j : ℝ) ≤ n := by exact_mod_cast hj
  nlinarith [pi_pos]

/-- **(10.20).** For the Chebyshev weight `w(x) = (1 - x²)^{-1/2}` the Gauss nodes and
coefficients are

`xⱼ = -cos((2j + 1)π/(2(n + 1)))`, `αⱼ = π/(n + 1)`, `0 ≤ j ≤ n`:

the nodes increase with `j`, they are the zeros of the Chebyshev polynomial `T_{n+1} ∈ ℙ_{n+1}`,
and the formula has degree of exactness `2n + 1`. Mathlib's
`Polynomial.Chebyshev.integral_eq_sumZeroes`, whose nodes `cos((2i + 1)π/(2(n + 1)))` are the
book's under `j ↦ n - j`. -/
theorem equation_10_20 (n : ℕ) :
    StrictMono (fun j : Fin (n + 1) => chebyshevGaussNode n j) ∧
      (∀ j : Fin (n + 1), (Chebyshev.T ℝ (n + 1)).eval (chebyshevGaussNode n j) = 0) ∧
      IsExactOnMeasure chebyshevMeasure (fun _ : Fin (n + 1) => π / (n + 1))
        (fun j : Fin (n + 1) => chebyshevGaussNode n j) (2 * n + 1) := by
  refine ⟨?_, fun j => ?_, fun p hp => ?_⟩
  · refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    simp only [chebyshevGaussNode, Fin.val_castSucc, Fin.val_succ, neg_lt_neg_iff]
    refine strictAntiOn_cos (gaussAngle_mem_Icc (by omega : (i : ℕ) ≤ n))
      (gaussAngle_mem_Icc (by omega : (i : ℕ) + 1 ≤ n)) ?_
    push_cast
    gcongr
    linarith
  · rw [chebyshevGaussNode_eq (Nat.lt_succ_iff.mp j.2), Chebyshev.T_real_cos, cos_eq_zero_iff]
    refine ⟨((n - j : ℕ) : ℤ), ?_⟩
    have : ((n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  · have hdeg : p.degree < ((2 * (n + 1) : ℕ) : WithBot ℕ) :=
      hp.trans_lt (by exact_mod_cast (by omega : 2 * n + 1 < 2 * (n + 1)))
    rw [chebyshevMeasure, Chebyshev.integral_eq_sumZeroes (n := n + 1) (Nat.succ_ne_zero n)
      (by exact_mod_cast hdeg), Chebyshev.sumZeroes, Finset.mul_sum,
      ← Finset.sum_range_reflect (fun i => π / ((n + 1 : ℕ) : ℝ) *
        p.eval (cos ((2 * (i : ℝ) + 1) / (2 * ((n + 1 : ℕ) : ℝ)) * π))) (n + 1),
      ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only
    rw [chebyshevGaussNode_eq (Nat.lt_succ_iff.mp j.2), Nat.add_sub_cancel, Nat.cast_succ]

/-- The Chebyshev–Gauss nodes lie in `[-1, 1]`. -/
theorem chebyshevGaussNode_mem_Icc (n j : ℕ) : chebyshevGaussNode n j ∈ Icc (-1 : ℝ) 1 :=
  ⟨neg_le_neg (cos_le_one _), by
    rw [chebyshevGaussNode, neg_le]
    exact neg_one_le_cos _⟩

/-- **(10.25), the first inequality.** For the interpolant `Π^G_n f` of `f ∈ C⁰([-1, 1])` at the
`n + 1` Chebyshev–Gauss nodes (10.20), `‖f - Π^G_n f‖_∞ ≤ (1 + Λ_n) E_n^*(f)`, where `Λ_n` is the
Lebesgue constant of the Chebyshev nodes and `E_n^*(f)` the best approximation error of §10.8:
the bound `interpolation_error_le_lebesgue` of §10.8 at these nodes. The second part of (10.25),
Rivlin's estimate `Λ_n ≤ (2/π) log(n + 1) + 1`, is the open `equation_10_25`. -/
theorem equation_10_25_interpolation_error (n : ℕ) (f : C(Icc (-1 : ℝ) 1, ℝ)) :
    ‖f - Lagrange.interpolateCLM
        (fun j : Fin (n + 1) => (⟨chebyshevGaussNode n j, chebyshevGaussNode_mem_Icc n j⟩ :
          Icc (-1 : ℝ) 1)) f‖ ≤
      (1 + sSup (Set.range fun t : Icc (-1 : ℝ) 1 => ∑ i, |Lagrange.basisCM
          (fun j : Fin (n + 1) => (⟨chebyshevGaussNode n j, chebyshevGaussNode_mem_Icc n j⟩ :
            Icc (-1 : ℝ) 1)) i t|)) * bestApproximationError (-1) 1 n f :=
  interpolation_error_le_lebesgue (fun _ _ h =>
    (equation_10_20 n).1.injective (congrArg Subtype.val h)) f

/-! ### The Chebyshev–Gauss–Lobatto formula (10.21) -/

/-- **(10.21), the Chebyshev–Gauss–Lobatto nodes** `x̄ⱼ = -cos(πj/n)`, `0 ≤ j ≤ n`, `n ≥ 1`. -/
noncomputable def chebyshevLobattoNode (n j : ℕ) : ℝ := -cos (j * π / n)

/-- The book's Gauss–Lobatto node `x̄ⱼ` is Mathlib's extremum `cos((n - j)π/n)` of `T_n`
(`Polynomial.Chebyshev.node`): the same points, enumerated in the opposite order. -/
theorem chebyshevLobattoNode_eq_node (hn : n ≠ 0) {j : ℕ} (hj : j ≤ n) :
    chebyshevLobattoNode n j = Chebyshev.node n (n - j) := by
  rw [chebyshevLobattoNode, Chebyshev.node, ← cos_pi_sub, Nat.cast_sub hj]
  congr 1
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

/-- The factors `dⱼ` of (10.21) are symmetric under `j ↦ n - j`. -/
theorem lobattoFactor_sub {j : ℕ} (hj : j ≤ n) :
    Chebyshev.lobattoFactor n (n - j) = Chebyshev.lobattoFactor n j := by
  unfold Chebyshev.lobattoFactor
  split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)

/-- The weights `ᾱⱼ` of (10.21) are symmetric under `j ↦ n - j`. -/
theorem lobattoWeight_sub {j : ℕ} (hj : j ≤ n) :
    Chebyshev.lobattoWeight n (n - j) = Chebyshev.lobattoWeight n j := by
  simp only [Chebyshev.lobattoWeight, lobattoFactor_sub hj]

/-- The book's node `x̄_{n-j}` is Mathlib's `cos(jπ/n)`, indexed through `Fin.rev`. -/
theorem chebyshevLobattoNode_rev (hn : n ≠ 0) (j : Fin (n + 1)) :
    chebyshevLobattoNode n (Fin.rev j) = Chebyshev.node n j := by
  rw [chebyshevLobattoNode_eq_node hn (Nat.lt_succ_iff.mp (Fin.rev j).2)]
  congr 1
  rw [Fin.val_rev]
  omega

/-- The weights `ᾱⱼ` are symmetric under `Fin.rev`. -/
theorem lobattoWeight_rev (j : Fin (n + 1)) :
    Chebyshev.lobattoWeight n (Fin.rev j) = Chebyshev.lobattoWeight n j := by
  rw [Fin.val_rev, show n + 1 - ((j : ℕ) + 1) = n - j by omega,
    lobattoWeight_sub (Nat.lt_succ_iff.mp j.2)]

/-- The Chebyshev–Gauss–Lobatto rule in the book's enumeration of the nodes. -/
theorem isExactOnMeasure_chebyshevLobatto (hn : n ≠ 0) :
    IsExactOnMeasure chebyshevMeasure (fun j : Fin (n + 1) => Chebyshev.lobattoWeight n j)
      (fun j : Fin (n + 1) => chebyshevLobattoNode n j) (2 * n - 1) := by
  have h := (isExactOnMeasure_comp_equiv (μ := chebyshevMeasure)
    (w := fun j : Fin (n + 1) => Chebyshev.lobattoWeight n j)
    (x := fun j : Fin (n + 1) => Chebyshev.node n j) Fin.revPerm (d := 2 * n - 1)).mpr
    (Chebyshev.isExactOnMeasure_lobattoWeight_node hn)
  have hw' : (fun j : Fin (n + 1) => Chebyshev.lobattoWeight n j) =
      (fun j : Fin (n + 1) => Chebyshev.lobattoWeight n j) ∘ Fin.revPerm := by
    ext j
    exact (lobattoWeight_rev j).symm
  have hx' : (fun j : Fin (n + 1) => chebyshevLobattoNode n j) =
      (fun j : Fin (n + 1) => Chebyshev.node n j) ∘ Fin.revPerm := by
    ext j
    rw [Function.comp_apply, Fin.revPerm_apply, ← chebyshevLobattoNode_rev hn (Fin.rev j),
      Fin.rev_rev]
  rwa [← hw', ← hx'] at h

/-- The Chebyshev–Gauss–Lobatto nodes are distinct. -/
theorem injective_chebyshevLobattoNode (hn : n ≠ 0) :
    Function.Injective fun j : Fin (n + 1) => chebyshevLobattoNode n j := by
  intro i j hij
  have hi := Nat.lt_succ_iff.mp i.2
  have hj := Nat.lt_succ_iff.mp j.2
  simp only [chebyshevLobattoNode_eq_node hn hi, chebyshevLobattoNode_eq_node hn hj] at hij
  have := (Chebyshev.strictAntiOn_node n).injOn
    (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega : n - i < n + 1)))
    (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega : n - j < n + 1))) hij
  exact Fin.ext (by omega)

/-- **(10.21).** For `n ≥ 1` the Chebyshev–Gauss–Lobatto nodes and weights are

`x̄ⱼ = -cos(πj/n)`, `ᾱⱼ = π/(dⱼ n)`, `0 ≤ j ≤ n`, with `d₀ = d_n = 2` and `dⱼ = 1` for
`j = 1, …, n - 1`:

the nodes increase from `x̄₀ = -1` to `x̄_n = 1`, the formula has degree of exactness `2n - 1`, and
the internal nodes `x̄₁, …, x̄_{n-1}` are the zeros of `T_n' = n U_{n-1}`, as anticipated in
Remark 10.2. The backbone's `Polynomial.Chebyshev.integral_eq_sumExtrema` at the nodes
`cos(jπ/n)`, reversed, with Mathlib's `T_derivative_eq_U` and `U_real_cos`. -/
theorem equation_10_21 (hn : 1 ≤ n) :
    StrictMono (fun j : Fin (n + 1) => chebyshevLobattoNode n j) ∧
      chebyshevLobattoNode n 0 = -1 ∧ chebyshevLobattoNode n n = 1 ∧
      (∀ j, Chebyshev.lobattoWeight n j = π / (Chebyshev.lobattoFactor n j * n)) ∧
      Chebyshev.lobattoFactor n 0 = 2 ∧ Chebyshev.lobattoFactor n n = 2 ∧
      (∀ j, 0 < j → j < n → Chebyshev.lobattoFactor n j = 1) ∧
      IsExactOnMeasure chebyshevMeasure (fun j : Fin (n + 1) => Chebyshev.lobattoWeight n j)
        (fun j : Fin (n + 1) => chebyshevLobattoNode n j) (2 * n - 1) ∧
      derivative (Chebyshev.T ℝ n) = (n : ℝ[X]) * Chebyshev.U ℝ (n - 1) ∧
      ∀ j, 0 < j → j < n → (derivative (Chebyshev.T ℝ n)).eval (chebyshevLobattoNode n j) = 0 := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  have hder : derivative (Chebyshev.T ℝ n) = (n : ℝ[X]) * Chebyshev.U ℝ (n - 1) := by
    rw [Chebyshev.T_derivative_eq_U]
    push_cast [Nat.cast_sub hn]
    rfl
  refine ⟨?_, ?_, ?_, fun j => rfl, by simp [Chebyshev.lobattoFactor],
    by simp [Chebyshev.lobattoFactor], fun j hj0 hjn => Chebyshev.lobattoFactor_of_ne (by omega)
      (by omega), isExactOnMeasure_chebyshevLobatto hn0, hder, fun j hj0 hjn => ?_⟩
  · refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    change chebyshevLobattoNode n i.castSucc < chebyshevLobattoNode n i.succ
    rw [chebyshevLobattoNode_eq_node hn0 (Nat.lt_succ_iff.mp i.castSucc.2),
      chebyshevLobattoNode_eq_node hn0 (Nat.lt_succ_iff.mp i.succ.2), Fin.val_castSucc,
      Fin.val_succ]
    exact Chebyshev.node_lt (i := n - ((i : ℕ) + 1)) (j := n - i) (by omega) (by omega)
  · simp [chebyshevLobattoNode]
  · rw [chebyshevLobattoNode, mul_div_cancel_left₀ π hnR, cos_pi]
    norm_num
  · -- `x̄ⱼ = cos θ` with `θ = (n - j)π/n ∈ (0, π)`, and `sin(nθ) = sin((n - j)π) = 0`
    have hθ : chebyshevLobattoNode n j = cos (((n - j : ℕ) : ℝ) * π / n) :=
      chebyshevLobattoNode_eq_node hn0 hjn.le
    have hnj : (0 : ℝ) < ((n - j : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - j)
    have hsin : sin (((n - j : ℕ) : ℝ) * π / n) ≠ 0 := by
      refine (sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
      rw [div_lt_iff₀ (by positivity), Nat.cast_sub hjn.le]
      have : (0 : ℝ) < j := by exact_mod_cast hj0
      nlinarith [pi_pos]
    have hU := Chebyshev.U_real_cos (θ := ((n - j : ℕ) : ℝ) * π / n) (n := (n : ℤ) - 1)
    push_cast at hU
    rw [sub_add_cancel, show (n : ℝ) * (((n - j : ℕ) : ℝ) * π / n) = ((n - j : ℕ) : ℝ) * π by
      field_simp, sin_nat_mul_pi] at hU
    have hUzero := (mul_eq_zero.mp hU).resolve_right hsin
    rw [hder, eval_mul, hθ, eval_natCast, hUzero, mul_zero]

/-! ### The weighted Sobolev norm (10.23) -/

/-- **(10.23) and (10.35), the weighted Sobolev norm** `‖f‖_{s,w} = (∑_{k=0}^s ‖f^{(k)}‖_w²)^{1/2}`
of order `s` of a function `f`, for a weight `μ`: the book's `‖·‖_{s,w}` is the case
`μ = chebyshevMeasure`, and the `‖·‖_s` of (10.35) the case `μ = legendreMeasure`. It is only a
definition on smooth functions, enough to state the quoted estimates. -/
noncomputable def equation_10_23 (μ : Measure ℝ) (s : ℕ) (f : ℝ → ℝ) : ℝ :=
  √(∑ k ∈ Finset.range (s + 1), ∫ x, (iteratedDeriv k f x) ^ 2 ∂μ)

/-! ### Convergence of the Chebyshev–Gauss–Lobatto formula -/

-- TODO(backbone): the Chebyshev weight is carried by `[-1, 1]`; belongs beside
-- `OrthogonalPolynomial.isWeight_chebyshevMeasure`.
/-- The Chebyshev weight gives no mass outside `[-1, 1]`. -/
theorem chebyshevMeasure_compl_Icc : chebyshevMeasure (Icc (-1 : ℝ) 1)ᶜ = 0 := by
  rw [chebyshevMeasure, Chebyshev.measureT, Measure.restrict_apply' measurableSet_Ioc]
  have hempty : (Icc (-1 : ℝ) 1)ᶜ ∩ Ioc (-1 : ℝ) 1 = ∅ :=
    Set.eq_empty_of_forall_notMem fun t ht => ht.1 (Ioc_subset_Icc_self ht.2)
  rw [hempty, measure_empty]

/-- **§10.3, the convergence of the Chebyshev–Gauss–Lobatto formula** (the book cites [Sze67],
p. 342, for every `f` with finite weighted integral; stated for `f ∈ C⁰([-1, 1])`):

`∫_{-1}^1 f(x) (1 - x²)^{-1/2} dx = lim_{n → ∞} I^{GL}_{n,w}(f)`.

The Szegő–Pólya criterion `tendsto_of_isExactOnMeasure`, the weights `π/(dⱼ n)` being positive and
the degree of exactness `2n - 1` unbounded. -/
theorem lobatto_tendsto {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    Tendsto (fun n => ∑ j : Fin (n + 1), Chebyshev.lobattoWeight n j * f (chebyshevLobattoNode n j))
      atTop (𝓝 (∫ x in (-1 : ℝ)..1, f x / √(1 - x ^ 2))) := by
  have := isWeight_chebyshevMeasure.isFiniteMeasure
  have hint : ∫ x in (-1 : ℝ)..1, f x / √(1 - x ^ 2) = ∫ x, f x ∂chebyshevMeasure := by
    rw [chebyshevMeasure, Chebyshev.integral_measureT]
    simp only [div_eq_mul_inv, Real.sqrt_inv]
  rw [hint, ← tendsto_add_atTop_iff_nat 1]
  exact tendsto_of_isExactOnMeasure chebyshevMeasure_compl_Icc
    (x := fun k (j : Fin (k + 1 + 1)) => chebyshevLobattoNode (k + 1) j)
    (α := fun k (j : Fin (k + 1 + 1)) => Chebyshev.lobattoWeight (k + 1) j)
    (fun k => injective_chebyshevLobattoNode (Nat.succ_ne_zero k))
    (fun k j => by
      rw [chebyshevLobattoNode_eq_node (Nat.succ_ne_zero k) (Nat.lt_succ_iff.mp j.2)]
      exact Chebyshev.node_mem_Icc)
    (fun k j => (Chebyshev.lobattoWeight_pos (Nat.succ_ne_zero k) j).le)
    (d := fun k => 2 * (k + 1) - 1) (tendsto_atTop_atTop.mpr fun N => ⟨N, fun k hk => by omega⟩)
    (fun k => isExactOnMeasure_chebyshevLobatto (Nat.succ_ne_zero k)) hf

/-! ### The discrete scalar product (10.28) and the Chebyshev discrete transform (10.29)–(10.31) -/

/-- **(10.28), the discrete scalar product** of the Chebyshev–Gauss–Lobatto formula,
`(f, g)_n = ∑ⱼ ᾱⱼ f(x̄ⱼ) g(x̄ⱼ) = I^{GL}_{n,w}(fg)`: the backbone's `Quadrature.discreteInner` at
the weights and nodes (10.21). -/
noncomputable def equation_10_28 (n : ℕ) (f g : ℝ → ℝ) : ℝ :=
  discreteInner (fun j : Fin (n + 1) => Chebyshev.lobattoWeight n j)
    (fun j : Fin (n + 1) => chebyshevLobattoNode n j) f g

/-- (10.28) written out: `(f, g)_n = ∑ⱼ ᾱⱼ f(x̄ⱼ) g(x̄ⱼ) = I^{GL}_{n,w}(fg)`. -/
theorem equation_10_28_eq (n : ℕ) (f g : ℝ → ℝ) :
    equation_10_28 n f g =
        ∑ j : Fin (n + 1), Chebyshev.lobattoWeight n j * f (chebyshevLobattoNode n j) *
          g (chebyshevLobattoNode n j) ∧
      equation_10_28 n f g =
        ∑ j : Fin (n + 1), Chebyshev.lobattoWeight n j * (f * g) (chebyshevLobattoNode n j) :=
  ⟨rfl, by
    unfold equation_10_28 discreteInner
    exact Finset.sum_congr rfl fun j _ => by rw [Pi.mul_apply, mul_assoc]⟩

/-- **(10.31), the discrete coefficients**
`f̃_k = (2/(n d_k)) ∑_{j=0}^n dⱼ⁻¹ cos(k(n - j)π/n) f(x̄ⱼ)` of the Chebyshev discrete transform
(CDT), `k = 0, …, n`, with the cosine `T_k(x̄ⱼ)` written for the node ordering of (10.21) (the book
prints `cos(kjπ/n)`, see the module docstring). -/
noncomputable def chebyshevDiscreteCoeff (n : ℕ) (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  2 / (n * Chebyshev.lobattoFactor n k) * ∑ j ∈ Finset.range (n + 1),
    (Chebyshev.lobattoFactor n j)⁻¹ * cos ((k : ℝ) * ((n - j : ℕ) : ℝ) * π / n) *
      f (chebyshevLobattoNode n j)

/-- The discrete coefficients in the book's enumeration are those of the backbone's
`Polynomial.Chebyshev.interpolate_eq_sum_cdt` at the nodes `cos(jπ/n)`: the sums agree under
`j ↦ n - j`. -/
theorem chebyshevDiscreteCoeff_eq (hn : n ≠ 0) (f : ℝ → ℝ) (k : ℕ) :
    chebyshevDiscreteCoeff n f k = 2 / (n * Chebyshev.lobattoFactor n k) *
      ∑ j ∈ Finset.range (n + 1), (Chebyshev.lobattoFactor n j)⁻¹ *
        cos ((k : ℝ) * (j : ℝ) * π / n) * f (Chebyshev.node n j) := by
  rw [chebyshevDiscreteCoeff, ← Finset.sum_range_reflect (fun j => (Chebyshev.lobattoFactor n j)⁻¹ *
    cos ((k : ℝ) * (j : ℝ) * π / n) * f (Chebyshev.node n j)) (n + 1)]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [show n + 1 - 1 - j = n - j by omega, lobattoFactor_sub hj',
    chebyshevLobattoNode_eq_node hn hj']

/-- **(10.29)–(10.31), the Chebyshev discrete transform (Exercise 2).** For `n ≥ 1` the
interpolating polynomial `Π^{GL}_{n,w} f` at the `n + 1` Gauss–Lobatto nodes (10.21) is

`Π^{GL}_{n,w} f = ∑_{k=0}^n f̃_k T_k` (10.29), with
`f̃_k = (2/(n d_k)) ∑_{j=0}^n dⱼ⁻¹ T_k(x̄ⱼ) f(x̄ⱼ)` (10.31),

the CDT; its inverse is `f(x̄ⱼ) = ∑_{k=0}^n T_k(x̄ⱼ) f̃_k` (10.30), where
`T_k(x̄ⱼ) = cos(k(n - j)π/n)`; and `Π^{GL}_{n,w} f` coincides with the discrete truncation `f_n^*`
of (10.4) for the discrete scalar product (10.28). The backbone's
`Polynomial.Chebyshev.interpolate_eq_sum_cdt` (whose ingredients are the discrete norms
`Polynomial.Chebyshev.discreteInner_T_T` of the exercise's hint), reindexed, and
`Quadrature.interpolate_eq_sum_discreteInner_smul`. -/
theorem equation_10_31 (hn : 1 ≤ n) (f : ℝ → ℝ) :
    (Lagrange.interpolate Finset.univ (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
        fun j => f (chebyshevLobattoNode n j)) =
      ∑ k ∈ Finset.range (n + 1), C (chebyshevDiscreteCoeff n f k) * Chebyshev.T ℝ k ∧
    (∀ j : Fin (n + 1), f (chebyshevLobattoNode n j) = ∑ k ∈ Finset.range (n + 1),
      cos ((k : ℝ) * ((n - j : ℕ) : ℝ) * π / n) * chebyshevDiscreteCoeff n f k) ∧
    (Lagrange.interpolate Finset.univ (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
        fun j => f (chebyshevLobattoNode n j)) =
      discreteTruncation chebyshevMeasure (fun j : Fin (n + 1) => Chebyshev.lobattoWeight n j)
        (fun j : Fin (n + 1) => chebyshevLobattoNode n j) n f := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  have hinj := injective_chebyshevLobattoNode hn0
  -- (10.29), from the backbone's transform at the reversed nodes
  have hcdt : (Lagrange.interpolate Finset.univ (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
      fun j => f (chebyshevLobattoNode n j)) =
      ∑ k ∈ Finset.range (n + 1), C (chebyshevDiscreteCoeff n f k) * Chebyshev.T ℝ k := by
    have h := Chebyshev.interpolate_eq_sum_cdt hn0 f
    have hnodes : (fun j : Fin (n + 1) => Chebyshev.node n j) =
        (fun j : Fin (n + 1) => chebyshevLobattoNode n j) ∘ Fin.revPerm := by
      ext j
      exact (chebyshevLobattoNode_rev hn0 j).symm
    have hvals : (fun j : Fin (n + 1) => f (Chebyshev.node n j)) =
        fun j => f (((fun j : Fin (n + 1) => chebyshevLobattoNode n j) ∘ Fin.revPerm) j) := by
      ext j
      exact congrArg f (chebyshevLobattoNode_rev hn0 j).symm
    rw [hnodes, hvals, interpolate_comp_equiv hinj Fin.revPerm f] at h
    rw [h]
    exact Finset.sum_congr rfl fun k _ => by rw [chebyshevDiscreteCoeff_eq hn0]
  refine ⟨hcdt, fun j => ?_, ?_⟩
  · -- (10.30): evaluate (10.29) at `x̄ⱼ`
    have hj := Nat.lt_succ_iff.mp j.2
    have hev := Lagrange.eval_interpolate_at_node
      (fun j : Fin (n + 1) => f (chebyshevLobattoNode n j)) hinj.injOn (Finset.mem_univ j)
    rw [hcdt] at hev
    rw [← hev, eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eval_mul, eval_C, chebyshevLobattoNode_eq_node hn0 hj, Chebyshev.node, Chebyshev.T_real_cos,
      mul_comm]
    congr 2
    push_cast
    ring
  · exact interpolate_eq_sum_discreteInner_smul isWeight_chebyshevMeasure hn hinj
      (fun j => Chebyshev.lobattoWeight_pos hn0 j) (isExactOnMeasure_chebyshevLobatto hn0) f

end QuarteroniSaccoSaleri.Chapter10
