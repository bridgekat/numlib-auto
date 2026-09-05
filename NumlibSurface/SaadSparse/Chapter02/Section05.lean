import NumlibSurface.SaadSparse.Common

/-!
# §2.5 The finite volume method

Section 2.5 of Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003: the cell-centred finite volume discretization of a conservation law, and the one
structural claim the section makes about it — the semi-discrete operator (2.54)–(2.55) has
nonnegative diagonal entries, nonpositive off-diagonal entries and zero row sums, hence is a
Z-matrix that is weakly diagonally dominant by rows.

Everything here is plane linear algebra.  The claim rests on `∑ j, s⃗_j = 0` for the outward edge
vectors of a polygon, which Saad's Problem P-2.12 asks to be proved by the divergence theorem;
the elementary proof is used instead, since the outward normal times the edge length is the edge
vector rotated by a quarter turn and the edge vectors of a closed polygon telescope
(`SaadSparse.Ch02.sum_edgeVec_eq_zero`).

The derivation preceding the claim is not formalized: the conservation law (2.48), its weak form,
the cell integration (2.49) — which is the divergence theorem on a cell — and the cell-averaging
approximations (2.50)–(2.51), which the book itself calls crude and for which it states no error
bound.  The section discretizes in space only, so no linear system is ever formed; what it
produces is the operator `SaadSparse.Ch02.equation_2_55` below.

Vectors of the plane are `Fin 2 → ℝ`, so that Saad's `λ⃗ ⬝ s⃗` is Mathlib's `dotProduct`.
-/

open Finset Matrix

namespace SaadSparse.Ch02

/-! ### The outward edge vectors of a polygon -/

section Polygon

variable {m : ℕ} [NeZero m]

/-- Saad §2.5, Figure 2.10: the outward edge vector `s⃗_j = s_j n⃗_j` of the closed polygon with
vertices `p`, that is the edge `p_{j+1} - p_j` rotated by a quarter turn.  Its length is the
length of the edge, and its direction is the outward normal when the vertices run
counterclockwise. -/
def edgeVec (p : Fin m → Fin 2 → ℝ) (j : Fin m) : Fin 2 → ℝ :=
  ![p (j + 1) 1 - p j 1, p j 0 - p (j + 1) 0]

@[simp]
theorem edgeVec_zero (p : Fin m → Fin 2 → ℝ) (j : Fin m) :
    edgeVec p j 0 = p (j + 1) 1 - p j 1 := rfl

@[simp]
theorem edgeVec_one (p : Fin m → Fin 2 → ℝ) (j : Fin m) :
    edgeVec p j 1 = p j 0 - p (j + 1) 0 := rfl

/-- Summing a function of `Fin m` along the cyclic successor changes nothing, because the
successor is a permutation of `Fin m`.  This is what makes the edges of a *closed* polygon
telescope. -/
theorem sum_succ_eq_sum (f : Fin m → ℝ) : ∑ j, f (j + 1) = ∑ j, f j :=
  Fintype.sum_equiv (Equiv.addRight (1 : Fin m)) _ _ fun _ => rfl

/-- **Saad Problem P-2.12**: the outward edge vectors of a closed polygon sum to zero.  The book
asks for a proof by the divergence theorem; the edges `p_{j+1} - p_j` telescope over the cycle
`Fin m` and the quarter turn is linear, so no integration is needed. -/
theorem sum_edgeVec_eq_zero (p : Fin m → Fin 2 → ℝ) : ∑ j, edgeVec p j = 0 := by
  have key : ∀ f : Fin m → ℝ, ∑ j, (f (j + 1) - f j) = 0 := fun f => by
    rw [Finset.sum_sub_distrib, sum_succ_eq_sum, sub_self]
  have key' : ∀ f : Fin m → ℝ, ∑ j, (f j - f (j + 1)) = 0 := fun f => by
    rw [Finset.sum_sub_distrib, sum_succ_eq_sum, sub_self]
  ext i
  rw [Finset.sum_apply, Pi.zero_apply]
  fin_cases i
  · simpa [edgeVec] using key fun j => p j 1
  · simpa [edgeVec] using key' fun j => p j 0

end Polygon

/-! ### Positive and negative parts in Saad's sign convention

Saad's `(z)⁺ = (z + |z|)/2` and `(z)⁻ = (z - |z|)/2` are `max z 0` and `min z 0`.  Note that
Saad's negative part is *nonpositive*, unlike Mathlib's `negPart`, which is `max (-z) 0`. -/

/-- Saad's positive part `(z)⁺ = (z + |z|)/2` is `max z 0`. -/
theorem max_zero_eq_half (z : ℝ) : max z 0 = (z + |z|) / 2 := by
  rcases abs_cases z with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> [rw [max_eq_left]; rw [max_eq_right]] <;>
    linarith

/-- Saad's negative part `(z)⁻ = (z - |z|)/2` is `min z 0`. -/
theorem min_zero_eq_half (z : ℝ) : min z 0 = (z - |z|) / 2 := by
  rcases abs_cases z with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> [rw [min_eq_right]; rw [min_eq_left]] <;>
    linarith

/-- Saad (2.53): `z⁺ + z⁻ = z`, the decomposition of a scalar into its positive and negative
parts. -/
theorem posPart_add_negPart (z : ℝ) : max z 0 + min z 0 = z := by
  rw [max_zero_eq_half, min_zero_eq_half]; ring

/-- Saad (2.53), the upwind edge value: the average flux `(a + b)/2 * z` corrected by the upwind
term `|z|/2 * (b - a)` is `a z⁺ + b z⁻`, which is what produces the coefficients (2.54)–(2.55)
from the flux balance.  At `a = b = 1` it is `SaadSparse.Ch02.posPart_add_negPart`. -/
theorem equation_2_53 (a b z : ℝ) :
    (a + b) / 2 * z - |z| / 2 * (b - a) = a * max z 0 + b * min z 0 := by
  rw [max_zero_eq_half, min_zero_eq_half]; ring

/-! ### The semi-discrete finite volume operator (2.54)–(2.55) -/

section Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
  {lam : Fin 2 → ℝ} {s : (i : ι) → κ i → Fin 2 → ℝ} {nb : (i : ι) → κ i → ι}

/-- Saad (2.54)–(2.55): the semi-discrete finite volume operator for the linear flux `F⃗ = λ⃗ u`.
The cells are indexed by `ι`; cell `i` has edges indexed by `κ i`, with outward edge vector
`s⃗ i j` and neighbour `nb i j` across edge `j`.  The diagonal entry is
`β_i = ∑ j, (λ⃗ ⬝ s⃗ i j)⁺` and the entry at a neighbour collects `α_{ij} = (λ⃗ ⬝ s⃗ i j)⁻` over
the edges leading to it.

The geometry enters only through the hypothesis `∑ j, s⃗ i j = 0` of
`SaadSparse.Ch02.equation_2_55_isDiagDominant`, which
`SaadSparse.Ch02.sum_edgeVec_eq_zero` supplies for polygonal cells. -/
def equation_2_55 (lam : Fin 2 → ℝ) (s : (i : ι) → κ i → Fin 2 → ℝ) (nb : (i : ι) → κ i → ι) :
    Matrix ι ι ℝ :=
  Matrix.of fun i j =>
    (if i = j then ∑ k, max (lam ⬝ᵥ s i k) 0 else 0) +
      ∑ k with nb i k = j, min (lam ⬝ᵥ s i k) 0

omit [Fintype ι] in
/-- The diagonal entry `β_i = ∑ j, (λ⃗ ⬝ s⃗ i j)⁺` of (2.54), when no edge of a cell leads back
to the cell itself. -/
theorem equation_2_55_apply_self (hnb : ∀ i k, nb i k ≠ i) (i : ι) :
    equation_2_55 lam s nb i i = ∑ k, max (lam ⬝ᵥ s i k) 0 := by
  have h : (univ.filter fun k => nb i k = i) = ∅ :=
    filter_eq_empty_iff.mpr fun k _ => hnb i k
  simp [equation_2_55, h]

omit [Fintype ι] in
/-- The off-diagonal entry `α_{ij}` of (2.55): the negative parts of the edges of cell `i` that
lead to cell `j`. -/
theorem equation_2_55_apply_ne {i j : ι} (hij : i ≠ j) :
    equation_2_55 lam s nb i j = ∑ k with nb i k = j, min (lam ⬝ᵥ s i k) 0 := by
  simp [equation_2_55, hij]

/-- The row sum of the operator is `λ⃗ ⬝ (∑ j, s⃗ i j)`: the positive and negative parts of each
edge recombine by `SaadSparse.Ch02.posPart_add_negPart`. -/
theorem sum_equation_2_55 (i : ι) :
    ∑ j, equation_2_55 lam s nb i j = lam ⬝ᵥ ∑ k, s i k := by
  have hdiag : ∑ j, (if i = j then ∑ k, max (lam ⬝ᵥ s i k) 0 else 0) =
      ∑ k, max (lam ⬝ᵥ s i k) 0 := by simp
  have hoff : ∑ j, ∑ k with nb i k = j, min (lam ⬝ᵥ s i k) 0 =
      ∑ k, min (lam ⬝ᵥ s i k) 0 := Finset.sum_fiberwise _ _ _
  calc ∑ j, equation_2_55 lam s nb i j
      = (∑ k, max (lam ⬝ᵥ s i k) 0) + ∑ k, min (lam ⬝ᵥ s i k) 0 := by
        simp only [equation_2_55, Matrix.of_apply, Finset.sum_add_distrib, hdiag, hoff]
    _ = ∑ k, (lam ⬝ᵥ s i k) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => posPart_add_negPart _
    _ = lam ⬝ᵥ ∑ k, s i k := (dotProduct_sum _ _ _).symm

/-- **The structural claim of Saad §2.5**: the finite volume operator (2.54)–(2.55) has
nonnegative diagonal entries, nonpositive off-diagonal entries and zero row sums, and is
therefore a Z-matrix that is weakly diagonally dominant by rows — "the same desirable property
of weak diagonal dominance seen in the one-dimensional case".  The only geometric input is that
the outward edge vectors of each cell sum to zero, which `SaadSparse.Ch02.sum_edgeVec_eq_zero`
supplies. -/
theorem equation_2_55_isDiagDominant (hnb : ∀ i k, nb i k ≠ i) (hs : ∀ i, ∑ k, s i k = 0) :
    (∀ i, 0 ≤ equation_2_55 lam s nb i i) ∧
      (∀ i j, i ≠ j → equation_2_55 lam s nb i j ≤ 0) ∧
      (∀ i, ∑ j, equation_2_55 lam s nb i j = 0) ∧
      ∀ i, ∑ j ∈ univ.erase i, |equation_2_55 lam s nb i j| ≤
        |equation_2_55 lam s nb i i| := by
  have hrow : ∀ i, ∑ j, equation_2_55 lam s nb i j = 0 := fun i => by
    rw [sum_equation_2_55 i, hs i, dotProduct_zero]
  have hdiag : ∀ i, 0 ≤ equation_2_55 lam s nb i i := fun i => by
    rw [equation_2_55_apply_self hnb i]
    exact Finset.sum_nonneg fun k _ => le_max_right _ _
  have hoff : ∀ i j, i ≠ j → equation_2_55 lam s nb i j ≤ 0 := fun i j hij => by
    rw [equation_2_55_apply_ne hij]
    exact Finset.sum_nonpos fun k _ => min_le_right _ _
  refine ⟨hdiag, hoff, hrow, fun i => ?_⟩
  have habs : ∑ j ∈ univ.erase i, |equation_2_55 lam s nb i j| =
      -∑ j ∈ univ.erase i, equation_2_55 lam s nb i j := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j hj =>
      abs_of_nonpos (hoff i j (Ne.symm (Finset.ne_of_mem_erase hj)))
  have hsplit :
      equation_2_55 lam s nb i i + ∑ j ∈ univ.erase i, equation_2_55 lam s nb i j = 0 := by
    have h := hrow i
    rwa [← Finset.add_sum_erase _ _ (mem_univ i)] at h
  rw [habs, abs_of_nonneg (hdiag i)]
  linarith

end Operator

end SaadSparse.Ch02
