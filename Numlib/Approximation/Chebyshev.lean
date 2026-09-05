import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.IntermediateValue
import Numlib.Approximation.BestApprox

/-!
# Best uniform approximation and equioscillation

Best uniform approximation of a continuous function on a compact subset of the line by
polynomials of degree at most `n`, and the alternation (equioscillation) that characterizes it.

* `polyLE X n` is the subspace of `C(X, ℝ)` of the restrictions of the real polynomials of
  degree at most `n`.
* `HaarCondition V d` says that no nonzero element of `V` vanishes at `d` distinct points of `X`.
  It is what the alternation arguments use about polynomials, and it holds for `polyLE X n` with
  `d = n + 1` (`haarCondition_polyLE`), as it does for the trigonometric polynomials of degree at
  most `n` on a circle. The dimension is carried as a parameter rather than read off as
  `Module.finrank`, so that no rank computation is needed at a use site.
* `Equioscillates g m` says that `g` attains `± ‖g‖` with alternating signs at `m` increasing
  points of `X`.
* `le_infDist_of_alternates` is the de la Vallée-Poussin lower bound: an alternation of length
  `n + 2` for the error of *any* competitor bounds the distance to `polyLE X n` from below. Its
  immediate consequence `isBestApprox_of_equioscillates` is the sufficiency half of Chebyshev's
  equioscillation theorem.
* `IsBestApprox.exists_card_eq_of_interpolation` is the half with content in the other direction:
  the error of a best approximation attains its maximum modulus at `d` distinct points, because
  otherwise an element of the subspace interpolating the error at the extreme points gives a
  direction of improvement. Its hypothesis, that the subspace takes prescribed values at fewer
  than `d` points, holds for `polyLE X n` by Lagrange's formula
  (`IsBestApprox.exists_card_eq_of_polyLE`) and for a `d`-dimensional Haar subspace by
  `HaarCondition.exists_mem_forall_eq`, the interpolation property of a Haar system.
* `IsBestApprox.unique_of_polyLE` and `IsBestApprox.unique_of_haarCondition`, the uniqueness of
  the best uniform approximation, follow from it and the Haar condition through the midpoint of
  two best approximations.

## References

[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009. (Theorem 3.3.19.)
[^kress]: Rainer Kress, *Numerical Analysis*, Graduate Texts in Mathematics 181, Springer, 1998.
  (§8.2.)
-/

open scoped Polynomial

/-- The subspace of `C(X, ℝ)` of the restrictions to `X` of the real polynomial functions of
degree at most `n`. -/
noncomputable def polyLE (X : Set ℝ) (n : ℕ) : Submodule ℝ C(X, ℝ) :=
  (Polynomial.degreeLE ℝ n).map (Polynomial.toContinuousMapOnAlgHom X).toLinearMap

/-- An element of `polyLE X n` is exactly a continuous function on `X` given by a polynomial of
degree at most `n`. -/
theorem mem_polyLE_iff {X : Set ℝ} {n : ℕ} {g : C(X, ℝ)} :
    g ∈ polyLE X n ↔ ∃ P : ℝ[X], P.degree ≤ n ∧ ∀ t : X, g t = P.eval (t : ℝ) := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P, Polynomial.mem_degreeLE.mp hP, fun t => by simp⟩
  · rintro ⟨P, hP, hg⟩
    refine ⟨P, Polynomial.mem_degreeLE.mpr hP, ?_⟩
    ext t
    simpa using (hg t).symm

/-- A subspace `V` of `C(X, ℝ)` satisfies the **Haar condition in dimension `d`** when no nonzero
element of `V` vanishes at `d` distinct points of `X`. For a `d`-dimensional space this is the
classical Haar condition; carrying `d` as a parameter keeps every use site free of a rank
computation. -/
def HaarCondition {X : Type*} [TopologicalSpace X] (V : Submodule ℝ C(X, ℝ)) (d : ℕ) : Prop :=
  ∀ g ∈ V, g ≠ 0 → ∀ s : Finset X, (∀ t ∈ s, g t = 0) → s.card < d

/-- The polynomials of degree at most `n` satisfy the Haar condition in dimension `n + 1`:
a nonzero polynomial of degree at most `n` has at most `n` roots. -/
theorem haarCondition_polyLE (X : Set ℝ) (n : ℕ) : HaarCondition (polyLE X n) (n + 1) := by
  intro g hg hg0 s hs
  by_contra hcard
  push Not at hcard
  obtain ⟨P, hP, hgP⟩ := mem_polyLE_iff.mp hg
  have himg : (s.image Subtype.val).card = s.card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  have hP0 : P = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P (s.image Subtype.val)
      (fun t ht => ?_) ?_
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      rw [← hgP u]
      exact hs u hu
    · rw [himg]
      exact lt_of_le_of_lt (Polynomial.natDegree_le_of_degree_le hP) (by omega)
  refine hg0 ?_
  ext t
  simp [hgP t, hP0]

/-- **A Haar system interpolates.** A subspace of dimension `d` satisfying the Haar condition in
dimension `d` takes prescribed values at any `d` distinct points: the evaluation map into
`Fin d → ℝ` is injective by the Haar condition, hence surjective because the dimensions agree. -/
theorem HaarCondition.exists_forall_apply_eq {X : Type*} [TopologicalSpace X]
    {V : Submodule ℝ C(X, ℝ)} {d : ℕ} [FiniteDimensional ℝ V] (hV : HaarCondition V d)
    (hdim : Module.finrank ℝ V = d) {x : Fin d → X} (hx : Function.Injective x)
    (y : Fin d → ℝ) : ∃ g ∈ V, ∀ i, g (x i) = y i := by
  classical
  set ev : V →ₗ[ℝ] Fin d → ℝ :=
    { toFun := fun g i => (g : C(X, ℝ)) (x i)
      map_add' := fun g g' => by ext i; simp
      map_smul' := fun c g => by ext i; simp } with hev
  have hevapp : ∀ (g : V) (i : Fin d), ev g i = (g : C(X, ℝ)) (x i) := fun _ _ => rfl
  have hinj : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro g hg
    by_contra hg0
    have hne : (g : C(X, ℝ)) ≠ 0 := fun h => hg0 (Subtype.ext h)
    have hzero : ∀ t ∈ Finset.univ.image x, (g : C(X, ℝ)) t = 0 := by
      rintro t ht
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
      rw [← hevapp g i, hg]
      rfl
    have hcard : (Finset.univ.image x).card = d := by
      rw [Finset.card_image_of_injective _ hx, Finset.card_univ, Fintype.card_fin]
    exact absurd (hV _ g.2 hne _ hzero) (by omega)
  have hrank : Module.finrank ℝ V = Module.finrank ℝ (Fin d → ℝ) := by
    rw [hdim, Module.finrank_fin_fun]
  obtain ⟨g, hg⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj y
  exact ⟨g, g.2, fun i => by rw [← hevapp g i, hg]⟩

/-- The interpolation property of a Haar system in the form the exchange argument uses: fewer than
`d` points can be prescribed arbitrarily, by padding them out to `d` distinct points. -/
theorem HaarCondition.exists_mem_forall_eq {X : Type*} [TopologicalSpace X] [Infinite X]
    {V : Submodule ℝ C(X, ℝ)} {d : ℕ} [FiniteDimensional ℝ V] (hV : HaarCondition V d)
    (hdim : Module.finrank ℝ V = d) (S : Finset X) (hS : S.card < d) (y : X → ℝ) :
    ∃ q ∈ V, ∀ t ∈ S, q t = y t := by
  classical
  obtain ⟨T, hTsub, hTcard⟩ :=
    (Set.Finite.infinite_compl S.finite_toSet).exists_subset_card_eq (d - S.card)
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    exact fun a haS haT => hTsub haT haS
  have hcard : (S ∪ T).card = d := by
    rw [Finset.card_union_of_disjoint hdisj, hTcard]
    omega
  set e := Finset.equivFinOfCardEq hcard with he
  set x : Fin d → X := fun i => ((e.symm i : (S ∪ T : Finset X)) : X) with hx
  have hxinj : Function.Injective x := fun i j hij => e.symm.injective (Subtype.ext hij)
  obtain ⟨g, hgV, hgval⟩ := hV.exists_forall_apply_eq hdim hxinj fun i => y (x i)
  refine ⟨g, hgV, fun t ht => ?_⟩
  have hval := hgval (e ⟨t, Finset.mem_union_left _ ht⟩)
  simpa [hx] using hval

/-- `Equioscillates g m`: the function `g` attains `± ‖g‖` with alternating signs at `m`
increasing points of `X`, the alternation condition in Chebyshev's characterization of a best
uniform approximation. -/
def Equioscillates {X : Set ℝ} [CompactSpace X] (g : C(X, ℝ)) (m : ℕ) : Prop :=
  ∃ (σ : ℝ) (x : Fin m → X), (σ = 1 ∨ σ = -1) ∧ StrictMono (fun i => (x i : ℝ)) ∧
    ∀ i : Fin m, g (x i) = σ * (-1) ^ (i : ℕ) * ‖g‖

/-- A continuous function changing sign on an interval has a root strictly inside it. -/
private theorem exists_root_of_mul_neg {F : ℝ → ℝ} (hF : Continuous F) {u v : ℝ} (huv : u < v)
    (h : F u * F v < 0) : ∃ z ∈ Set.Ioo u v, F z = 0 := by
  rcases mul_neg_iff.mp h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · obtain ⟨z, hz, hz0⟩ :=
      intermediate_value_Ioo' huv.le hF.continuousOn (Set.mem_Ioo.mpr ⟨hv, hu⟩)
    exact ⟨z, hz, hz0⟩
  · obtain ⟨z, hz, hz0⟩ :=
      intermediate_value_Ioo huv.le hF.continuousOn (Set.mem_Ioo.mpr ⟨hu, hv⟩)
    exact ⟨z, hz, hz0⟩

/-- **De la Vallée-Poussin's lower bound.** If the error `f - q` of some competitor `q` of degree
at most `n` alternates in sign at `n + 2` increasing points of `X` with values of modulus at
least `ε`, then no polynomial of degree at most `n` approximates `f` better than `ε`.

The proof is the Haar condition for `polyLE X n`: were some `p` closer than `ε`, the difference
`p - q` would inherit the alternation, hence have `n + 1` roots by the intermediate value
theorem, hence vanish — contradicting the alternation itself.

Reference: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, Theorem 3.3.19. -/
theorem le_infDist_of_alternates {X : Set ℝ} [CompactSpace X] {n : ℕ} {f q : C(X, ℝ)}
    (hq : q ∈ polyLE X n) {ε σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {x : Fin (n + 2) → X}
    (hmono : StrictMono fun i => (x i : ℝ))
    (hval : ∀ i : Fin (n + 2), ε ≤ σ * (-1) ^ (i : ℕ) * (f (x i) - q (x i))) :
    ε ≤ Metric.infDist f (polyLE X n : Set C(X, ℝ)) := by
  have hsgn : ∀ i : Fin (n + 2), |σ * (-1) ^ (i : ℕ)| = 1 := by
    intro i
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]
    rcases hσ with h | h <;> simp [h]
  refine (Metric.le_infDist ⟨0, (polyLE X n).zero_mem⟩).2 ?_
  rintro p hp
  rw [dist_eq_norm]
  by_contra hcon
  push Not at hcon
  -- the difference of the two competitors inherits the alternation
  have hgpos : ∀ i : Fin (n + 2), 0 < σ * (-1) ^ (i : ℕ) * (p (x i) - q (x i)) := by
    intro i
    have h1 : |f (x i) - p (x i)| ≤ ‖f - p‖ := by
      have := (f - p).norm_coe_le_norm (x i)
      simpa using this
    have h2 : σ * (-1) ^ (i : ℕ) * (f (x i) - p (x i)) ≤ ‖f - p‖ := by
      calc σ * (-1) ^ (i : ℕ) * (f (x i) - p (x i))
          ≤ |σ * (-1) ^ (i : ℕ) * (f (x i) - p (x i))| := le_abs_self _
        _ = |f (x i) - p (x i)| := by rw [abs_mul, hsgn i, one_mul]
        _ ≤ ‖f - p‖ := h1
    have h3 := hval i
    nlinarith [h3, h2, hcon]
  -- read the difference off as a polynomial of degree at most `n`
  obtain ⟨P, hPdeg, hPval⟩ := mem_polyLE_iff.mp hp
  obtain ⟨Q, hQdeg, hQval⟩ := mem_polyLE_iff.mp hq
  have hRdeg : (P - Q).degree ≤ (n : ℕ) := (Polynomial.degree_sub_le _ _).trans (max_le hPdeg hQdeg)
  have hRval : ∀ i : Fin (n + 2), 0 < σ * (-1) ^ (i : ℕ) * (P - Q).eval (x i : ℝ) := by
    intro i
    have := hgpos i
    rwa [hPval, hQval, ← Polynomial.eval_sub] at this
  -- the intermediate value theorem produces `n + 1` roots
  have hroot : ∀ i : Fin (n + 1), ∃ z ∈ Set.Ioo (x i.castSucc : ℝ) (x i.succ : ℝ),
      (P - Q).eval z = 0 := by
    intro i
    refine exists_root_of_mul_neg (P - Q).continuous (hmono (Fin.castSucc_lt_succ (i := i))) ?_
    have h1 := hRval i.castSucc
    have h2 := hRval i.succ
    have hpar : ((-1 : ℝ)) ^ (i.succ : ℕ) = -((-1 : ℝ) ^ (i.castSucc : ℕ)) := by
      have : (i.succ : ℕ) = (i.castSucc : ℕ) + 1 := by simp
      rw [this, pow_succ]
      ring
    rw [hpar] at h2
    nlinarith [h1, h2, sq_nonneg (σ * (-1) ^ (i.castSucc : ℕ))]
  choose z hz hz0 using hroot
  have hzmono : StrictMono z := by
    intro i j hij
    calc z i < (x i.succ : ℝ) := (hz i).2
      _ ≤ (x j.castSucc : ℝ) := hmono.monotone (by
          simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
          omega)
      _ < z j := (hz j).1
  have hcard : (Finset.univ.image z).card = n + 1 := by
    rw [Finset.card_image_of_injective _ hzmono.injective, Finset.card_univ, Fintype.card_fin]
  have hR0 : P - Q = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (Finset.univ.image z)
      (fun t ht => ?_) ?_
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
      exact hz0 i
    · rw [hcard]
      exact lt_of_le_of_lt (Polynomial.natDegree_le_of_degree_le hRdeg) (by omega)
  have := hRval 0
  rw [hR0] at this
  simp at this

/-- The sufficiency half of Chebyshev's equioscillation theorem: a polynomial whose error
equioscillates at `n + 2` points is a best uniform approximation.

Reference: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, Theorem 3.3.19. -/
theorem isBestApprox_of_equioscillates {X : Set ℝ} [CompactSpace X] {n : ℕ} {f p : C(X, ℝ)}
    (hp : p ∈ polyLE X n) (h : Equioscillates (f - p) (n + 2)) :
    IsBestApprox (polyLE X n : Set C(X, ℝ)) f p := by
  obtain ⟨σ, x, hσ, hmono, hvals⟩ := h
  have hle : ‖f - p‖ ≤ Metric.infDist f (polyLE X n : Set C(X, ℝ)) := by
    refine le_infDist_of_alternates hp hσ hmono fun i => ?_
    have hv : f (x i) - p (x i) = σ * (-1) ^ (i : ℕ) * ‖f - p‖ := by
      simpa using hvals i
    rw [hv, ← mul_assoc]
    have hsq : σ * (-1) ^ (i : ℕ) * (σ * (-1) ^ (i : ℕ)) = 1 := by
      have h1 : ((-1 : ℝ) ^ (i : ℕ)) * ((-1 : ℝ) ^ (i : ℕ)) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]
        norm_num
      rcases hσ with h | h <;> subst h <;> linear_combination h1
    rw [hsq, one_mul]
  rw [isBestApprox_iff_norm_sub_eq_infDist hp]
  exact le_antisymm hle (by rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hp)

/-! ### The extreme set of a best approximation, and uniqueness -/

/-- On a compact nonempty space the maximum modulus of a continuous function is attained. -/
private theorem exists_abs_eq_norm {X : Set ℝ} [CompactSpace X] [Nonempty X] (g : C(X, ℝ)) :
    ∃ t : X, |g t| = ‖g‖ := by
  obtain ⟨t, -, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (continuous_abs.comp g.continuous).continuousOn
  refine ⟨t, le_antisymm (by simpa using g.norm_coe_le_norm t) ?_⟩
  rw [ContinuousMap.norm_le _ (abs_nonneg _)]
  intro u
  simpa using hmax (Set.mem_univ u)

/-- **The error of a best uniform approximation from an interpolating subspace attains its
maximum modulus at `d` points.** This is the half of the Chebyshev characterization that has
content: if the error attained its maximum modulus at fewer than `d` points, then an element `q`
of the subspace interpolating the error at those points makes `p + c q` a strictly better
approximation once `c > 0` is small enough.

The hypothesis is what a Haar system of dimension `d` supplies
(`HaarCondition.exists_mem_forall_eq`), and what Lagrange interpolation supplies for the
polynomials of degree at most `n`, with `d = n + 1`.

Reference: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, Theorem 3.3.19. -/
theorem IsBestApprox.exists_card_eq_of_interpolation {X : Set ℝ} [CompactSpace X] [Infinite X]
    {d : ℕ} {V : Submodule ℝ C(X, ℝ)} {f p : C(X, ℝ)}
    (hinterp : ∀ S : Finset X, S.card < d → ∀ y : X → ℝ, ∃ q ∈ V, ∀ t ∈ S, q t = y t)
    (hp : IsBestApprox (V : Set C(X, ℝ)) f p) :
    ∃ S : Finset X, S.card = d ∧ ∀ t ∈ S, |(f - p) t| = ‖f - p‖ := by
  classical
  set g : C(X, ℝ) := f - p with hgdef
  by_cases hbig : ∃ S : Finset X, S.card = d ∧ ∀ t ∈ S, |g t| = ‖g‖
  · exact hbig
  exfalso
  set E : Set X := {t | |g t| = ‖g‖} with hEdef
  have hEne : E.Nonempty := (exists_abs_eq_norm g).imp fun t ht => ht
  have hEfin : E.Finite := by
    by_contra hinf
    obtain ⟨S, hSsub, hScard⟩ := Set.Infinite.exists_subset_card_eq hinf d
    exact hbig ⟨S, hScard, fun t ht => hSsub (Finset.mem_coe.mpr ht)⟩
  have hEcard : hEfin.toFinset.card < d := by
    by_contra hlt
    push Not at hlt
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hlt
    exact hbig ⟨S, hScard, fun t ht => hEfin.mem_toFinset.mp (hSsub ht)⟩
  -- the error is not identically zero
  have hgpos : 0 < ‖g‖ := by
    rcases (norm_nonneg g).lt_or_eq with h | h
    · exact h
    · exfalso
      have huniv : E = Set.univ := by
        ext t
        simp only [hEdef, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        have h1 : |g t| ≤ ‖g‖ := by simpa using g.norm_coe_le_norm t
        have h2 : (0 : ℝ) ≤ |g t| := abs_nonneg _
        linarith
      exact Set.infinite_univ (α := X) (huniv ▸ hEfin)
  set S : Finset X := hEfin.toFinset with hSdef
  have hSmem : ∀ t ∈ S, |g t| = ‖g‖ := fun t ht => hEfin.mem_toFinset.mp ht
  obtain ⟨t₃, ht₃⟩ : S.Nonempty := hEfin.toFinset_nonempty.mpr hEne
  -- interpolate the error at the extreme points
  obtain ⟨q, hqmem, hqval⟩ := hinterp S hEcard fun t => g t
  -- the set where the error and the interpolant have the same sign
  set P : Set X := {t | 0 < g t * q t} with hPdef
  have hPopen : IsOpen P := isOpen_lt continuous_const (g.continuous.mul q.continuous)
  have hSP : ∀ t ∈ S, t ∈ P := by
    intro t ht
    have h2 : |g t| = ‖g‖ := hSmem t ht
    have h3 : g t * q t = ‖g‖ * ‖g‖ := by
      rw [hqval t ht, ← abs_mul_abs_self (g t), h2]
    change 0 < g t * q t
    rw [h3]
    exact mul_pos hgpos hgpos
  have hKlt : ∀ t ∈ (Pᶜ : Set X), |g t| < ‖g‖ := by
    intro t ht
    have htE : |g t| ≠ ‖g‖ := fun h => ht (hSP t (hEfin.mem_toFinset.mpr h))
    exact lt_of_le_of_ne (by simpa using g.norm_coe_le_norm t) htE
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ > 0, ∀ t ∈ (Pᶜ : Set X), |g t| ≤ ‖g‖ - δ := by
    rcases Set.eq_empty_or_nonempty (Pᶜ : Set X) with hK | hK
    · refine ⟨‖g‖, hgpos, fun t ht => ?_⟩
      rw [hK] at ht
      exact absurd ht (Set.notMem_empty t)
    · obtain ⟨t₂, ht₂, hm⟩ := (hPopen.isClosed_compl.isCompact).exists_isMaxOn hK
        (continuous_abs.comp g.continuous).continuousOn
      refine ⟨‖g‖ - |g t₂|, by linarith [hKlt t₂ ht₂], fun t ht => ?_⟩
      have h : |g t| ≤ |g t₂| := hm ht
      linarith
  have hqpos : 0 < ‖q‖ := by
    have h1 : |q t₃| ≤ ‖q‖ := by simpa using q.norm_coe_le_norm t₃
    have h2 : |q t₃| = ‖g‖ := by rw [hqval t₃ ht₃]; exact hSmem t₃ ht₃
    linarith
  -- the improving step
  set c : ℝ := min (δ / (‖q‖ + 1)) (‖g‖ / (‖q‖ + 1)) with hcdef
  have hq1 : (0 : ℝ) < ‖q‖ + 1 := by linarith
  have hcpos : 0 < c := lt_min (by positivity) (by positivity)
  have hcq1 : c * ‖q‖ < δ := by
    have hle : c ≤ δ / (‖q‖ + 1) := min_le_left _ _
    have h1 : c * ‖q‖ ≤ δ / (‖q‖ + 1) * ‖q‖ :=
      mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    have h2 : δ / (‖q‖ + 1) * ‖q‖ < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hq1]
      nlinarith
    linarith
  have hcq2 : c * ‖q‖ < ‖g‖ := by
    have hle : c ≤ ‖g‖ / (‖q‖ + 1) := min_le_right _ _
    have h1 : c * ‖q‖ ≤ ‖g‖ / (‖q‖ + 1) * ‖q‖ :=
      mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    have h2 : ‖g‖ / (‖q‖ + 1) * ‖q‖ < ‖g‖ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hq1]
      nlinarith
    linarith
  have hlt : ‖g - c • q‖ < ‖g‖ := by
    obtain ⟨t, -, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
      (continuous_abs.comp (g - c • q).continuous).continuousOn
    have hattain : ‖g - c • q‖ = |(g - c • q) t| := by
      refine le_antisymm ?_ (by simpa using (g - c • q).norm_coe_le_norm t)
      rw [ContinuousMap.norm_le _ (abs_nonneg _)]
      intro u
      simpa using hmax (Set.mem_univ u)
    have hval : (g - c • q) t = g t - c * q t := by simp
    rw [hattain, hval]
    have hga : |g t| ≤ ‖g‖ := by simpa using g.norm_coe_le_norm t
    have hqa : |q t| ≤ ‖q‖ := by simpa using q.norm_coe_le_norm t
    by_cases htP : t ∈ P
    · have hab : 0 < g t * q t := htP
      have hg1 : g t ≤ ‖g‖ := (abs_le.mp hga).2
      have hg2 : -‖g‖ ≤ g t := (abs_le.mp hga).1
      have hqu : q t ≤ ‖q‖ := (abs_le.mp hqa).2
      have hql : -‖q‖ ≤ q t := (abs_le.mp hqa).1
      have hcqu : c * q t ≤ c * ‖q‖ := mul_le_mul_of_nonneg_left hqu hcpos.le
      have hcql : c * -‖q‖ ≤ c * q t := mul_le_mul_of_nonneg_left hql hcpos.le
      rw [abs_lt]
      rcases mul_pos_iff.mp hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hcqp : 0 < c * q t := mul_pos hcpos h2
        constructor <;> nlinarith
      · have hcqn : c * q t < 0 := mul_neg_of_pos_of_neg hcpos h2
        constructor <;> nlinarith
    · have h1 : |g t| ≤ ‖g‖ - δ := hδ t htP
      calc |g t - c * q t| ≤ |g t| + |c * q t| := by
            simpa [sub_eq_add_neg] using abs_add_le (g t) (-(c * q t))
        _ = |g t| + c * |q t| := by rw [abs_mul, abs_of_pos hcpos]
        _ ≤ ‖g‖ - δ + c * ‖q‖ := by gcongr
        _ < ‖g‖ := by linarith
  -- contradiction with best approximation
  have hmem : p + c • q ∈ (V : Set C(X, ℝ)) := V.add_mem hp.1 (V.smul_mem c hqmem)
  have hbetter := hp.2 (p + c • q) hmem
  have heq : f - (p + c • q) = g - c • q := by
    rw [hgdef]
    abel
  rw [heq] at hbetter
  exact absurd hbetter (not_le.mpr hlt)

/-- **The error of a best uniform approximation attains its maximum modulus at `n + 1` distinct
points.** The polynomial case of `IsBestApprox.exists_card_eq_of_interpolation`, whose
interpolation hypothesis is Lagrange's formula at the extreme points.

Reference: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, Theorem 3.3.19. -/
theorem IsBestApprox.exists_card_eq_of_polyLE {X : Set ℝ} [CompactSpace X] [Infinite X] {n : ℕ}
    {f p : C(X, ℝ)} (hp : IsBestApprox (polyLE X n : Set C(X, ℝ)) f p) :
    ∃ S : Finset X, S.card = n + 1 ∧ ∀ t ∈ S, |(f - p) t| = ‖f - p‖ := by
  classical
  refine hp.exists_card_eq_of_interpolation fun S hS y => ?_
  have hinj : Set.InjOn (fun u : X => (u : ℝ)) ↑S := fun a _ b _ h => Subtype.val_injective h
  set Q : ℝ[X] := Lagrange.interpolate S (fun u : X => (u : ℝ)) (fun u => y u) with hQdef
  have hQdeg : Q.degree ≤ (n : ℕ) := by
    have h1 : Q.degree < (S.card : WithBot ℕ) := Lagrange.degree_interpolate_lt _ hinj
    have h2 : (S.card : WithBot ℕ) ≤ (n : ℕ) := by
      exact_mod_cast Nat.lt_succ_iff.mp hS
    exact le_of_lt (lt_of_lt_of_le h1 h2)
  refine ⟨Q.toContinuousMapOn X, mem_polyLE_iff.mpr ⟨Q, hQdeg, fun t => rfl⟩, fun t ht => ?_⟩
  exact Lagrange.eval_interpolate_at_node _ hinj ht

/-- **Uniqueness of the best uniform approximation from a Haar subspace.** Two best
approximations of the same function by elements of a `d`-dimensional subspace satisfying the Haar
condition in dimension `d` agree.

Their midpoint is a best approximation too, its error attains the common minimal norm at `d`
points, and at each of those the two errors must agree; the Haar condition then forces the two
elements to be equal.

Reference: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, Theorem 3.3.19; Rainer Kress, *Numerical
Analysis*, Graduate Texts in Mathematics 181, Springer, 1998, §8.2. -/
theorem IsBestApprox.unique_of_haarCondition {X : Set ℝ} [CompactSpace X] [Infinite X] {d : ℕ}
    {V : Submodule ℝ C(X, ℝ)} [FiniteDimensional ℝ V] (hV : HaarCondition V d)
    (hdim : Module.finrank ℝ V = d) {f p₁ p₂ : C(X, ℝ)}
    (h₁ : IsBestApprox (V : Set C(X, ℝ)) f p₁) (h₂ : IsBestApprox (V : Set C(X, ℝ)) f p₂) :
    p₁ = p₂ := by
  have hmid : IsBestApprox (V : Set C(X, ℝ)) f ((2 : ℝ)⁻¹ • p₁ + (2 : ℝ)⁻¹ • p₂) :=
    convex_setOf_isBestApprox V.convex f h₁ h₂ (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨S, hScard, hSext⟩ :=
    hmid.exists_card_eq_of_interpolation (hV.exists_mem_forall_eq hdim)
  set ρ : ℝ := ‖f - ((2 : ℝ)⁻¹ • p₁ + (2 : ℝ)⁻¹ • p₂)‖ with hρ
  have hρ₁ : ‖f - p₁‖ = ρ := by
    rw [hρ, h₁.norm_sub_eq_infDist, hmid.norm_sub_eq_infDist]
  have hρ₂ : ‖f - p₂‖ = ρ := by
    rw [hρ, h₂.norm_sub_eq_infDist, hmid.norm_sub_eq_infDist]
  have hagree : ∀ t ∈ S, p₁ t = p₂ t := by
    intro t ht
    have hmax := hSext t ht
    have hb₁ : |f t - p₁ t| ≤ ρ := by
      rw [← hρ₁]
      simpa using (f - p₁).norm_coe_le_norm t
    have hb₂ : |f t - p₂ t| ≤ ρ := by
      rw [← hρ₂]
      simpa using (f - p₂).norm_coe_le_norm t
    have hsplit : (f - ((2 : ℝ)⁻¹ • p₁ + (2 : ℝ)⁻¹ • p₂)) t
        = (2 : ℝ)⁻¹ * (f t - p₁ t) + (2 : ℝ)⁻¹ * (f t - p₂ t) := by
      simp
      ring
    rw [hsplit] at hmax
    rcases abs_le.mp hb₁ with ⟨ha₁, ha₂⟩
    rcases abs_le.mp hb₂ with ⟨hc₁, hc₂⟩
    rcases abs_cases ((2 : ℝ)⁻¹ * (f t - p₁ t) + (2 : ℝ)⁻¹ * (f t - p₂ t)) with
      ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] at hmax <;> linarith
  have hzero : p₁ - p₂ = 0 := by
    by_contra hne
    have hcard := hV (p₁ - p₂) (V.sub_mem h₁.1 h₂.1) hne S (fun t ht => by
      simpa using sub_eq_zero.mpr (hagree t ht))
    omega
  exact sub_eq_zero.mp hzero

/-- **Uniqueness of the best uniform approximation** by polynomials of degree at most `n` on a
compact infinite subset of the line: two best approximations of the same function agree.

Their midpoint is a best approximation too, its error attains the common minimal norm at `n + 1`
points, and at each of those the two errors must agree; the Haar condition then forces the two
polynomials to be equal.

Reference: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, Theorem 3.3.19. -/
theorem IsBestApprox.unique_of_polyLE {X : Set ℝ} [CompactSpace X] [Infinite X] {n : ℕ}
    {f p₁ p₂ : C(X, ℝ)} (h₁ : IsBestApprox (polyLE X n : Set C(X, ℝ)) f p₁)
    (h₂ : IsBestApprox (polyLE X n : Set C(X, ℝ)) f p₂) : p₁ = p₂ := by
  have hconv : Convex ℝ ((polyLE X n : Set C(X, ℝ))) := (polyLE X n).convex
  have hmid : IsBestApprox (polyLE X n : Set C(X, ℝ)) f
      ((2 : ℝ)⁻¹ • p₁ + (2 : ℝ)⁻¹ • p₂) :=
    convex_setOf_isBestApprox hconv f h₁ h₂ (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨S, hScard, hSext⟩ := hmid.exists_card_eq_of_polyLE
  set ρ : ℝ := ‖f - ((2 : ℝ)⁻¹ • p₁ + (2 : ℝ)⁻¹ • p₂)‖ with hρ
  have hρ₁ : ‖f - p₁‖ = ρ := by
    rw [hρ, h₁.norm_sub_eq_infDist, hmid.norm_sub_eq_infDist]
  have hρ₂ : ‖f - p₂‖ = ρ := by
    rw [hρ, h₂.norm_sub_eq_infDist, hmid.norm_sub_eq_infDist]
  have hagree : ∀ t ∈ S, p₁ t = p₂ t := by
    intro t ht
    have hmax := hSext t ht
    have hb₁ : |f t - p₁ t| ≤ ρ := by
      rw [← hρ₁]
      simpa using (f - p₁).norm_coe_le_norm t
    have hb₂ : |f t - p₂ t| ≤ ρ := by
      rw [← hρ₂]
      simpa using (f - p₂).norm_coe_le_norm t
    have hsplit : (f - ((2 : ℝ)⁻¹ • p₁ + (2 : ℝ)⁻¹ • p₂)) t
        = (2 : ℝ)⁻¹ * (f t - p₁ t) + (2 : ℝ)⁻¹ * (f t - p₂ t) := by
      simp
      ring
    rw [hsplit] at hmax
    rcases abs_le.mp hb₁ with ⟨ha₁, ha₂⟩
    rcases abs_le.mp hb₂ with ⟨hc₁, hc₂⟩
    rcases abs_cases ((2 : ℝ)⁻¹ * (f t - p₁ t) + (2 : ℝ)⁻¹ * (f t - p₂ t)) with
      ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] at hmax <;> linarith
  have hsubmem : p₁ - p₂ ∈ polyLE X n := (polyLE X n).sub_mem h₁.1 h₂.1
  have hzero : p₁ - p₂ = 0 := by
    by_contra hne
    have hcard := haarCondition_polyLE X n (p₁ - p₂) hsubmem hne S (fun t ht => by
      simpa using sub_eq_zero.mpr (hagree t ht))
    omega
  exact sub_eq_zero.mp hzero
