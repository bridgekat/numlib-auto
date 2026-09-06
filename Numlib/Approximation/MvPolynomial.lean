import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Topology.Algebra.MvPolynomial
import Numlib.Approximation.OrthogonalDecomposition

/-!
# Multivariate polynomials in `L²` of a domain

The spaces of multivariable approximation theory: `Π_n^d`, the polynomials in `d` variables of
total degree at most `n`, viewed inside `L²(μ)` for a measure `μ` on `ℝ^d`, and the orthogonal
components the chain of those spaces induces.

Two things have to hold of `μ` for this to be a faithful picture, and they are the two clauses of
`Approximation.IsMvWeight`: every polynomial must be square integrable, and no nonzero polynomial
may vanish `μ`-almost everywhere. The second is what makes the `L²(μ)` inner product *definite* on
polynomials, so that `Π_n^d` sits inside `L²(μ)` with its dimension intact. Both hold for the
volume of a compact set with nonempty interior — the unit ball, the unit cube, the simplex — which
is `Approximation.isMvWeight_restrict`.

The same polynomials also sit inside `C(D, ℝ)` for a set `D ⊆ ℝ^d`, as `Approximation.mvPolyLE`,
and the distance to that subspace is the minimax error `E_n(f)`. Both pictures rest on the same
fact, `MvPolynomial.eq_zero_of_eval_eq_zero_of_mem_interior`: a polynomial vanishing on a set with
nonempty interior is the zero polynomial.

## Main definitions

* `Approximation.IsMvWeight μ`: the standing hypothesis on `μ` described above.
* `Approximation.IsMvWeight.toL2`: the linear map taking a polynomial to its class in `L²(μ)`.
* `Approximation.IsMvWeight.polyLE hw n`: the image of the polynomials of total degree at most `n`,
  a subspace of `L²(μ)`. `Approximation.orthogonalComponent hw.polyLE n` is then the space of
  "orthogonal polynomials of exact degree `n`" for `μ`.
* `Approximation.toContinuousMapOn D` and `Approximation.mvPolyLE D n`: the same passage into
  `C(D, ℝ)`, where the sup norm makes the distance to `mvPolyLE D n` the minimax error `E_n(f)`.

## Main results

* `MvPolynomial.finrank_restrictTotalDegree`: `dim Π_n^d = C(n + d, d)`, by the stars-and-bars
  bijection between the monomials of degree at most `n` in `d` variables and the monomials of
  degree exactly `n` in `d + 1` variables.
* `Approximation.IsMvWeight.toL2_injective` and `Approximation.IsMvWeight.finrank_polyLE`: the
  passage to `L²(μ)` loses nothing, so the dimension of the image is again `C(n + d, d)`; and
  `Approximation.toContinuousMapOn_injective` with `Approximation.finrank_mvPolyLE` say the same of
  the passage to `C(D, ℝ)`.
* `Approximation.IsMvWeight.inner_toL2_mul_left`: multiplication by a polynomial is symmetric for
  the `L²(μ)` inner product.
* `Approximation.IsMvWeight.finrank_orthogonalComponent_add`: the `n + 1`-st orthogonal component
  has the dimension of the space of homogeneous polynomials of degree `n + 1`.
-/

open Finset MeasureTheory Module

namespace MvPolynomial

section Card

variable (σ : Type*) [Fintype σ] (n : ℕ)

/-- Stars and bars: adding one slack coordinate matches the exponent vectors in `σ` of total degree
at most `n` with those in `Option σ` of total degree exactly `n`. -/
noncomputable def slackEquiv [DecidableEq σ] :
    ↑{m : σ →₀ ℕ | m.sum (fun _ e => e) ≤ n} ≃
      ((univ : Finset (Option σ)).finsuppAntidiag n : Finset (Option σ →₀ ℕ)) where
  toFun m := ⟨Finsupp.equivFunOnFinite.symm
      (fun o => o.elim (n - ∑ i, m.1 i) m.1), by
    have h : ∑ i, m.1 i ≤ n := by simpa [Finsupp.sum_fintype] using m.2
    simp [Finset.mem_finsuppAntidiag, Fintype.sum_option]
    omega⟩
  invFun g := ⟨Finsupp.equivFunOnFinite.symm (fun i => g.1 (some i)), by
    have h := (Finset.mem_finsuppAntidiag.1 g.2).1
    rw [Fintype.sum_option] at h
    simp [Finsupp.sum_fintype]
    omega⟩
  left_inv m := by ext i; simp
  right_inv g := by
    have h := (Finset.mem_finsuppAntidiag.1 g.2).1
    rw [Fintype.sum_option] at h
    ext o
    cases o with
    | none => simp; omega
    | some i => simp

/-- The number of monomials in `σ` of total degree at most `n` is `C(n + d, n)`, `d = #σ`. -/
theorem card_setOf_sum_le :
    Nat.card ↑{m : σ →₀ ℕ | m.sum (fun _ e => e) ≤ n} = (n + Fintype.card σ).choose n := by
  classical
  rw [Nat.card_congr (slackEquiv σ n), Nat.card_eq_finsetCard,
    Finset.card_finsuppAntidiag_nat_eq_choose]
  simp [Nat.add_comm]

/-- **The dimension of `Π_n^d`**: the polynomials in `d = #σ` variables of total degree at most `n`
form a free module of rank `C(n + d, d)`. -/
theorem finrank_restrictTotalDegree (R : Type*) [CommRing R] [StrongRankCondition R] :
    finrank R (restrictTotalDegree σ R n) = (n + Fintype.card σ).choose (Fintype.card σ) := by
  classical
  have hfin : Fintype ↑{m : σ →₀ ℕ | m.sum (fun _ e => e) ≤ n} :=
    Fintype.ofEquiv _ (slackEquiv σ n).symm
  rw [show restrictTotalDegree σ R n
      = restrictSupport R {m : σ →₀ ℕ | m.sum (fun _ e => e) ≤ n} from rfl,
    finrank_eq_card_basis (basisRestrictSupport R {m : σ →₀ ℕ | m.sum (fun _ e => e) ≤ n}),
    ← Nat.card_eq_fintype_card, card_setOf_sum_le,
    ← Nat.choose_symm (Nat.le_add_right n (Fintype.card σ))]
  congr 1
  omega

end Card

/-- The spaces of polynomials of bounded total degree increase with the bound. -/
theorem restrictTotalDegree_mono (σ R : Type*) [CommSemiring R] {m n : ℕ} (h : m ≤ n) :
    restrictTotalDegree σ R m ≤ restrictTotalDegree σ R n := by
  intro p hp
  rw [mem_restrictTotalDegree] at hp ⊢
  exact hp.trans h

/-- A real polynomial vanishing on a set with nonempty interior is the zero polynomial: the
interior contains a box whose sides are infinite sets, and a polynomial is determined by its values
on such a box. -/
theorem eq_zero_of_eval_eq_zero_of_mem_interior {ι : Type*} {D : Set (ι → ℝ)}
    (hint : (interior D).Nonempty) {p : MvPolynomial ι ℝ}
    (h : ∀ x ∈ interior D, eval x p = 0) : p = 0 := by
  classical
  obtain ⟨x₀, hx₀⟩ := hint
  obtain ⟨I, u, hu, hbox⟩ := isOpen_pi_iff.1 isOpen_interior x₀ hx₀
  have hsI : ∀ i ∈ I, (if i ∈ I then u i else Set.univ) = u i := fun i hi => by simp [hi]
  have hsinf : ∀ i, (if i ∈ I then u i else Set.univ : Set ℝ).Infinite := by
    intro i
    by_cases hi : i ∈ I
    · rw [hsI i hi]
      obtain ⟨a, b, hab, hsub⟩ :=
        mem_nhds_iff_exists_Ioo_subset.1 ((hu i hi).1.mem_nhds (hu i hi).2)
      exact Set.Infinite.mono hsub (Set.Ioo_infinite (hab.1.trans hab.2))
    · simp [hi, Set.infinite_univ]
  refine funext_set _ hsinf (q := 0) fun x hx => ?_
  rw [map_zero]
  refine h x (hbox fun i hi => ?_)
  rw [← hsI i hi]
  exact hx i (Set.mem_univ i)

end MvPolynomial

namespace Approximation

section ContinuousMap

variable {ι : Type*}

/-- Polynomial evaluation restricted to a set `D ⊆ ℝ^ι`, as a linear map into `C(D, ℝ)`. -/
noncomputable def toContinuousMapOn (D : Set (ι → ℝ)) : MvPolynomial ι ℝ →ₗ[ℝ] C(D, ℝ) where
  toFun p := ⟨fun x => MvPolynomial.eval (x : ι → ℝ) p,
    (MvPolynomial.continuous_eval p).comp continuous_subtype_val⟩
  map_add' _ _ := by ext x; simp
  map_smul' _ _ := by ext x; simp

@[simp]
theorem toContinuousMapOn_apply {D : Set (ι → ℝ)} (p : MvPolynomial ι ℝ) (x : D) :
    toContinuousMapOn D p x = MvPolynomial.eval (x : ι → ℝ) p := rfl

/-- `Π_n^d` inside `C(D, ℝ)`: the restrictions to `D` of the polynomials of total degree at most
`n`. Its distance to `f` is the minimax error `E_n(f)` of multivariable approximation theory, and it
is the multivariate counterpart of `Approximation.Chebyshev.polyLE`. -/
noncomputable def mvPolyLE (D : Set (ι → ℝ)) (n : ℕ) : Submodule ℝ C(D, ℝ) :=
  (MvPolynomial.restrictTotalDegree ι ℝ n).map (toContinuousMapOn D)

theorem mem_mvPolyLE_iff {D : Set (ι → ℝ)} {n : ℕ} {f : C(D, ℝ)} :
    f ∈ mvPolyLE D n ↔ ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ n ∧ toContinuousMapOn D p = f := by
  simp only [mvPolyLE, Submodule.mem_map, MvPolynomial.mem_restrictTotalDegree]

theorem mvPolyLE_mono {D : Set (ι → ℝ)} : Monotone (mvPolyLE D) := fun _ _ h =>
  Submodule.map_mono (MvPolynomial.restrictTotalDegree_mono ι ℝ h)

/-- A polynomial is determined by its restriction to a set with nonempty interior. -/
theorem toContinuousMapOn_injective {D : Set (ι → ℝ)} (hint : (interior D).Nonempty) :
    Function.Injective (toContinuousMapOn D) := by
  refine (injective_iff_map_eq_zero _).2 fun p hp => ?_
  refine MvPolynomial.eq_zero_of_eval_eq_zero_of_mem_interior hint fun x hx => ?_
  exact congrFun (congrArg DFunLike.coe hp) ⟨x, interior_subset hx⟩

/-- The dimension of `Π_n^d` inside `C(D, ℝ)` is the algebraic one, `C(n + d, d)`. -/
theorem finrank_mvPolyLE [Fintype ι] {D : Set (ι → ℝ)} (hint : (interior D).Nonempty) (n : ℕ) :
    finrank ℝ (mvPolyLE D n) = (n + Fintype.card ι).choose (Fintype.card ι) := by
  rw [← MvPolynomial.finrank_restrictTotalDegree ι n ℝ]
  exact (LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective _ (toContinuousMapOn_injective hint) _)).symm

end ContinuousMap

variable {ι : Type*} [MeasurableSpace (ι → ℝ)] {μ : Measure (ι → ℝ)}

/-- A measure on `ℝ^ι` for which the `L²` theory of polynomials is faithful: every polynomial is
square integrable, and no nonzero polynomial vanishes almost everywhere. The second clause is the
`d`-dimensional counterpart of the second clause of `Approximation.OrthogonalPolynomial.IsWeight`,
which asks that a one-variable weight not be carried by a finite set; here the exceptional sets are
the zero sets of polynomials, which are the algebraic hypersurfaces. -/
structure IsMvWeight (μ : Measure (ι → ℝ)) : Prop where
  /-- Every polynomial is square integrable. -/
  memLp_eval (p : MvPolynomial ι ℝ) : MemLp (fun x => MvPolynomial.eval x p) 2 μ
  /-- Only the zero polynomial vanishes almost everywhere. -/
  eq_zero_of_ae_eq_zero {p : MvPolynomial ι ℝ}
    (h : (fun x => MvPolynomial.eval x p) =ᵐ[μ] 0) : p = 0

namespace IsMvWeight

variable (hw : IsMvWeight μ)

/-- The class in `L²(μ)` of a polynomial, as a linear map. -/
noncomputable def toL2 : MvPolynomial ι ℝ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun p := (hw.memLp_eval p).toLp _
  map_add' p q := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (by filter_upwards with x; simp)
  map_smul' c p := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (by filter_upwards with x; simp)

theorem coeFn_toL2 (p : MvPolynomial ι ℝ) :
    hw.toL2 p =ᵐ[μ] fun x => MvPolynomial.eval x p :=
  MemLp.coeFn_toLp (hw.memLp_eval p)

/-- The `L²(μ)` inner product of two polynomials is the integral of their product. -/
theorem inner_toL2 (p q : MvPolynomial ι ℝ) :
    inner ℝ (hw.toL2 p) (hw.toL2 q) =
      ∫ x, MvPolynomial.eval x p * MvPolynomial.eval x q ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hw.coeFn_toL2 p, hw.coeFn_toL2 q] with x hp hq
  simp [hp, hq, mul_comm]

/-- Multiplication by a polynomial is symmetric for the `L²(μ)` inner product,
`(r p, q) = (p, r q)`. This is the one analytic input of a three-term recursion for multivariable
orthogonal polynomials, and it holds of an integral inner product for no reason beyond
commutativity. -/
theorem inner_toL2_mul_left (r p q : MvPolynomial ι ℝ) :
    inner ℝ (hw.toL2 (r * p)) (hw.toL2 q) = inner ℝ (hw.toL2 p) (hw.toL2 (r * q)) := by
  rw [hw.inner_toL2, hw.inner_toL2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_mul]
  ring

@[simp]
theorem toL2_eq_zero_iff {p : MvPolynomial ι ℝ} : hw.toL2 p = 0 ↔ p = 0 := by
  refine ⟨fun h => hw.eq_zero_of_ae_eq_zero ?_, fun h => by simp [h, map_zero]⟩
  have h0 : ⇑(hw.toL2 p) =ᵐ[μ] 0 := by rw [h]; exact Lp.coeFn_zero ℝ 2 μ
  exact (hw.coeFn_toL2 p).symm.trans h0

/-- Distinct polynomials have distinct classes in `L²(μ)`. -/
theorem toL2_injective : Function.Injective hw.toL2 :=
  (injective_iff_map_eq_zero _).2 fun _ h => hw.toL2_eq_zero_iff.1 h

/-- `Π_n^d` inside `L²(μ)`: the classes of the polynomials of total degree at most `n`. -/
noncomputable def polyLE (n : ℕ) : Submodule ℝ (Lp ℝ 2 μ) :=
  (MvPolynomial.restrictTotalDegree ι ℝ n).map hw.toL2

theorem mem_polyLE_iff {n : ℕ} {f : Lp ℝ 2 μ} :
    f ∈ hw.polyLE n ↔ ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ n ∧ hw.toL2 p = f := by
  simp only [polyLE, Submodule.mem_map, MvPolynomial.mem_restrictTotalDegree]

theorem toL2_mem_polyLE {n : ℕ} {p : MvPolynomial ι ℝ} (hp : p.totalDegree ≤ n) :
    hw.toL2 p ∈ hw.polyLE n :=
  hw.mem_polyLE_iff.2 ⟨p, hp, rfl⟩

theorem monotone_polyLE : Monotone hw.polyLE := fun _ _ h =>
  Submodule.map_mono (MvPolynomial.restrictTotalDegree_mono ι ℝ h)

instance finiteDimensional_polyLE [Finite ι] (n : ℕ) : FiniteDimensional ℝ (hw.polyLE n) := by
  have h : Module.Finite ℝ (MvPolynomial.restrictTotalDegree ι ℝ n) := inferInstance
  exact Module.Finite.equiv (Submodule.equivMapOfInjective _ hw.toL2_injective _)

/-- The dimension of `Π_n^d` inside `L²(μ)` is the algebraic one, `C(n + d, d)`. -/
theorem finrank_polyLE [Fintype ι] (n : ℕ) :
    finrank ℝ (hw.polyLE n) = (n + Fintype.card ι).choose (Fintype.card ι) := by
  rw [← MvPolynomial.finrank_restrictTotalDegree ι n ℝ]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hw.toL2_injective _)).symm

/-- The `n + 1`-st orthogonal component of the chain `Π_0^d ⊆ Π_1^d ⊆ ⋯` has the dimension of the
space of homogeneous polynomials of degree `n + 1`, namely `C(n + d, d - 1)`. -/
theorem finrank_orthogonalComponent_add [Fintype ι] (n : ℕ) :
    finrank ℝ (orthogonalComponent hw.polyLE (n + 1)) +
        (n + Fintype.card ι).choose (Fintype.card ι) =
      (n + 1 + Fintype.card ι).choose (Fintype.card ι) := by
  rw [← hw.finrank_polyLE n, ← hw.finrank_polyLE (n + 1)]
  exact Approximation.finrank_orthogonalComponent_add hw.monotone_polyLE
    (fun _ => inferInstance) n

end IsMvWeight

/-- A measure charging every nonempty open set, restricted to a compact set of finite measure with
nonempty interior, is a weight: polynomials are bounded on that set, so square integrable, and a
polynomial vanishing almost everywhere on it vanishes on a box, so it is the zero polynomial. The
motivating instance is Lebesgue measure on the closed unit ball of `ℝ^d`. -/
theorem isMvWeight_restrict [OpensMeasurableSpace (ι → ℝ)] [μ.IsOpenPosMeasure]
    {D : Set (ι → ℝ)} (hD : IsCompact D) (hDm : MeasurableSet D) (hμ : μ D ≠ ⊤)
    (hint : (interior D).Nonempty) :
    IsMvWeight (μ.restrict D) := by
  have hfin : IsFiniteMeasure (μ.restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hμ⟩
  refine ⟨fun p => ?_, fun {p} hp => ?_⟩
  · obtain ⟨C, hC⟩ := hD.exists_bound_of_continuousOn (MvPolynomial.continuous_eval p).continuousOn
    exact MemLp.of_bound (MvPolynomial.continuous_eval p).aestronglyMeasurable C
      ((ae_restrict_iff' hDm).2 (Filter.Eventually.of_forall hC))
  · have hzero : ∀ x ∈ interior D, MvPolynomial.eval x p = 0 := by
      have hae : ∀ᵐ x ∂μ, x ∈ D → MvPolynomial.eval x p = 0 := by
        rw [← ae_restrict_iff' hDm]
        filter_upwards [hp] with x hx using hx
      have hnull : μ {x | x ∈ interior D ∧ MvPolynomial.eval x p ≠ 0} = 0 := by
        refine measure_mono_null ?_ (ae_iff.1 hae)
        rintro x ⟨hx1, hx2⟩
        simp only [Set.mem_ofPred_eq, Classical.not_imp]
        exact ⟨interior_subset hx1, hx2⟩
      have hopen : IsOpen {x | x ∈ interior D ∧ MvPolynomial.eval x p ≠ 0} :=
        isOpen_interior.inter (isOpen_ne_fun (MvPolynomial.continuous_eval p) continuous_const)
      have hempty := (IsOpen.measure_eq_zero_iff μ hopen).1 hnull
      intro x hx
      by_contra hne
      exact Set.eq_empty_iff_forall_notMem.1 hempty x ⟨hx, hne⟩
    exact MvPolynomial.eq_zero_of_eval_eq_zero_of_mem_interior hint hzero

end Approximation
