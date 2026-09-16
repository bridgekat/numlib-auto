import Numlib.Analysis.Convex.LinearInequalities
import NumlibSurface.Rockafellar.Chapter03.Section14

/-!
# Rockafellar §22: linear inequalities

Surface file for R. Tyrrell Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §22:
finite systems of weak and strict linear inequalities, the theorems of the alternative that decide
their solvability, and Farkas' Lemma.

Four of §22's nine numbered results are formalized over `Rn n = ℝⁿ`: Theorems 22.1–22.3 and
Corollary 22.3.1 (Farkas' Lemma).

The book writes `⟨aᵢ, x⟩` with the coefficient vector first, while the backbone writes `B x (a i)`,
because in general the solution vector and the coefficient vectors live in different spaces. On
`ℝⁿ` the pairing is symmetric, and `pairing_comm` is the only translation any statement here needs.

Rockafellar's `Σ ζ*ⱼIⱼ > 0` (p. 202) is a **set containment**, `⊆ (0, +∞)`: it says that
`ζ*₁ζ₁ + ⋯ + ζ*_NζN > 0` for every choice of `ζⱼ ∈ Iⱼ`. The convention is stated once in the book,
in a parenthesis far ahead of the theorem that uses it; `posIntervalCombo` records it.

## Main definitions

* `IsConsequence` — the book's *consequence* of a system of weak linear inequalities.
* `IsRowsOf` — the matrix form of a system: `A` is the matrix whose rows are the `aᵢ`.
* `IsRealInterval`, `rectangle`, `intervalCombo`, `posIntervalCombo` — the interval vocabulary of
  p. 202, with `posIntervalCombo` carrying the set-containment reading of `Σ ζ*ⱼIⱼ > 0`.
* `intervalVector`, `intervalSubspace`, `leIntervals`, `nonnegEqIntervals` — the translation of a
  linear system in `ℝⁿ` into a subspace-meets-rectangle problem in `ℝᴺ`, `N = n + m`.

## Main results

* `theorem_22_1`, `theorem_22_1_matrix` — Gale's theorem of the alternative, in vector and matrix
  form.
* `theorem_22_2`, `not_consistent_iff` — Motzkin's transposition theorem for a mixed system.
* `theorem_22_3`, `corollary_22_3_1`, `corollary_22_3_1_polar`, `solutions_eq_polarCone` — which
  inequalities are consequences of a consistent system, Farkas' Lemma, and its reading as
  `K°° = K` for a finitely generated cone.
* `interval_reading_le`, `interval_reading_nonneg_eq` — the two interval readings of p. 202: a
  linear system has a solution exactly when the subspace `L` meets the rectangle.

## Not formalized

Five of §22's nine numbered results — Lemmas 22.4 and 22.5, Corollary 22.4.1, and Theorems 22.6
and 22.7 (Tucker's complementarity theorem) — rest on the *elementary vectors* of a subspace, a
development that is combinatorial matroid theory rather than convex analysis and is deliberately
not formalized here; it is this project's one scope deferral. Theorems 22.6 and 22.7 rest further
on *Tucker representations* of a subspace, which the book describes only procedurally — solve the
defining system for the last `N - n` coordinates in terms of the first `n`, for some permutation —
so stating them at all needs a choice of `n` independent coordinate positions and the resulting
change of basis. Corollary 31.4.2 is the one other result of the book resting on them.
-/

open Set Pointwise

namespace Rockafellar

open ConvexAnalysis

variable {m n : ℕ}

/-! ### Theorem 22.1: the alternative for a system of weak inequalities -/

/-- **Theorem 22.1** (Gale's theorem of the alternative). For `aᵢ ∈ ℝⁿ` and `αᵢ ∈ ℝ`, one and only
one of the following holds: (a) `⟨aᵢ, x⟩ ≤ αᵢ` for `i = 1, …, m` has a solution `x ∈ ℝⁿ`; (b) there
are reals `λᵢ ≥ 0` with `∑ λᵢaᵢ = 0` and `∑ λᵢαᵢ < 0`. "One and only one" is the `Iff` with the
negation on the right: forwards is the exclusivity, backwards the existence. -/
theorem theorem_22_1 (a : Fin m → Rn n) (α : Fin m → ℝ) :
    (∃ x : Rn n, ∀ i, pairing n (a i) x ≤ α i) ↔
      ¬ ∃ l : Fin m → ℝ, (∀ i, 0 ≤ l i) ∧ (∑ i, l i • a i = 0) ∧ ∑ i, l i * α i < 0 := by
  rw [← alternative_linear_system (B := pairing n) a α]
  exact exists_congr fun x => forall_pairing_le_comm a α x

/-! ### Theorem 22.2: the alternative for a mixed system -/

/-- **Theorem 22.2** (Motzkin's transposition theorem). Assume `⟨bⱼ, x⟩ ≤ βⱼ` is consistent. Then
one and only one of the following holds: (a) some `x` has `⟨aᵢ, x⟩ < αᵢ` for every `i` and
`⟨bⱼ, x⟩ ≤ βⱼ` for every `j`; (b) there are reals `λᵢ, μⱼ ≥ 0` with some `λᵢ` non-zero,
`∑ λᵢaᵢ + ∑ μⱼbⱼ = 0` and `∑ λᵢαᵢ + ∑ μⱼβⱼ ≤ 0`. The book cuts one index range `1, …, m` at `k`;
here the strict and weak constraints are separate families. -/
theorem theorem_22_2 {p q : ℕ} (a : Fin p → Rn n) (α : Fin p → ℝ) (b : Fin q → Rn n)
    (β : Fin q → ℝ) (hcons : ∃ x : Rn n, ∀ j, pairing n (b j) x ≤ β j) :
    (∃ x : Rn n, (∀ i, pairing n (a i) x < α i) ∧ ∀ j, pairing n (b j) x ≤ β j) ↔
      ¬ ∃ (l : Fin p → ℝ) (μ : Fin q → ℝ), (∀ i, 0 ≤ l i) ∧ (∀ j, 0 ≤ μ j) ∧ (∃ i, l i ≠ 0) ∧
        (∑ i, l i • a i + ∑ j, μ j • b j = 0) ∧ ∑ i, l i * α i + ∑ j, μ j * β j ≤ 0 := by
  obtain ⟨x₀, hx₀⟩ := hcons
  rw [← alternative_linear_system_strict (B := pairing n) a α b β
    ⟨x₀, (forall_pairing_le_comm b β x₀).1 hx₀⟩]
  exact exists_congr fun x =>
    and_congr (forall_pairing_lt_comm a α x) (forall_pairing_le_comm b β x)

/-- **§22 (p. 200).** The hypothesis of Theorem 22.2 is itself decided by Theorem 22.1: the weak
subsystem is inconsistent exactly when it carries non-negative multipliers annihilating the `bⱼ`
with `∑ μⱼβⱼ < 0`. -/
theorem not_consistent_iff {q : ℕ} (b : Fin q → Rn n) (β : Fin q → ℝ) :
    (¬ ∃ x : Rn n, ∀ j, pairing n (b j) x ≤ β j) ↔
      ∃ μ : Fin q → ℝ, (∀ j, 0 ≤ μ j) ∧ (∑ j, μ j • b j = 0) ∧ ∑ j, μ j * β j < 0 := by
  rw [theorem_22_1 b β, not_not]

/-! ### Theorem 22.3: consequences of a system -/

/-- **Consequence of a system** (p. 200): `⟨a₀, x⟩ ≤ α₀` is a *consequence* of the system
`⟨aᵢ, x⟩ ≤ αᵢ`, `i = 1, …, m`, if every solution of the system satisfies it. -/
def IsConsequence (a : Fin m → Rn n) (α : Fin m → ℝ) (a₀ : Rn n) (α₀ : ℝ) : Prop :=
  ∀ x : Rn n, (∀ i, pairing n (a i) x ≤ α i) → pairing n a₀ x ≤ α₀

/-- `IsConsequence` in the backbone's orientation of the pairing. -/
theorem isConsequence_iff {a : Fin m → Rn n} {α : Fin m → ℝ} {a₀ : Rn n} {α₀ : ℝ} :
    IsConsequence a α a₀ α₀ ↔
      ∀ x : Rn n, (∀ i, pairing n x (a i) ≤ α i) → pairing n x a₀ ≤ α₀ :=
  forall_congr' fun x => imp_congr (forall_pairing_le_comm a α x) (by rw [pairing_comm])

/-- **Theorem 22.3**. For a consistent system `⟨aᵢ, x⟩ ≤ αᵢ`, an inequality `⟨a₀, x⟩ ≤ α₀` is a
consequence of it iff `∑ λᵢaᵢ = a₀` and `∑ λᵢαᵢ ≤ α₀` for some reals `λᵢ ≥ 0`. -/
theorem theorem_22_3 (a : Fin m → Rn n) (α : Fin m → ℝ) (a₀ : Rn n) (α₀ : ℝ)
    (hcons : ∃ x : Rn n, ∀ i, pairing n (a i) x ≤ α i) :
    IsConsequence a α a₀ α₀ ↔
      ∃ l : Fin m → ℝ, (∀ i, 0 ≤ l i) ∧ (∑ i, l i • a i = a₀) ∧ ∑ i, l i * α i ≤ α₀ := by
  obtain ⟨x₀, hx₀⟩ := hcons
  rw [isConsequence_iff]
  exact le_consequence_iff a α a₀ α₀ ⟨x₀, (forall_pairing_le_comm a α x₀).1 hx₀⟩

/-- **Corollary 22.3.1** (Farkas' Lemma). `⟨a₀, x⟩ ≤ 0` is a consequence of `⟨aᵢ, x⟩ ≤ 0`,
`i = 1, …, m`, iff `∑ λᵢaᵢ = a₀` for some reals `λᵢ ≥ 0`. -/
theorem corollary_22_3_1 (a : Fin m → Rn n) (a₀ : Rn n) :
    IsConsequence a (fun _ => 0) a₀ 0 ↔
      ∃ l : Fin m → ℝ, (∀ i, 0 ≤ l i) ∧ ∑ i, l i • a i = a₀ := by
  rw [isConsequence_iff]
  exact farkas (B := pairing n) a a₀

/-- **The solution set of a homogeneous system is a polar cone** (p. 200): the solutions of
`⟨aᵢ, x⟩ ≤ 0` are exactly `K°`, for `K` the convex cone generated by `a₁, …, a_m`. -/
theorem solutions_eq_polarCone (a : Fin m → Rn n) :
    {x : Rn n | ∀ i, pairing n (a i) x ≤ 0}
      = polarCone (pairing n) (PointedCone.hull ℝ (Set.range a) : Set (Rn n)) :=
  (polarCone_hull_range_rn a).symm

/-- **Farkas' Lemma says `K°° = K`** (p. 200) for `K` the convex cone generated by finitely many
vectors: `K` is closed because it is finitely generated (Theorem 19.1), so Theorem 14.1 gives
`K°° = cl K = K`. -/
theorem corollary_22_3_1_polar (a : Fin m → Rn n) :
    polarCone (pairing n) (polarCone (pairing n)
        (PointedCone.hull ℝ (Set.range a) : Set (Rn n)))
      = (PointedCone.hull ℝ (Set.range a) : Set (Rn n)) := by
  rw [polarCone_hull_range_rn, polarCone_setOf_forall_le_zero_rn,
    (isClosed_coe_pointedCone_hull_range a).closure_eq]

/-! ### The matrix form -/

/-- **The matrix form** (p. 201): `A` is the `m × n` matrix whose rows are `a₁, …, a_m`, so that
the system of alternative (a) of Theorem 22.1 reads `Ax ≤ a`, componentwise. -/
def IsRowsOf (A : Rn n →ₗ[ℝ] Rn m) (a : Fin m → Rn n) : Prop := ∀ x i, A x i = pairing n (a i) x

/-- **Rockafellar's transpose `A*` is the adjoint**, and on the rows it is `w ↦ ∑ wᵢaᵢ`; so the
vector condition `∑ λᵢaᵢ = 0` of Theorem 22.1(b) reads `A*w = 0`. -/
theorem adjoint_eq_sum_smul {A : Rn n →ₗ[ℝ] Rn m} {a : Fin m → Rn n} (h : IsRowsOf A a)
    (w : Rn m) : LinearMap.adjoint A w = ∑ i, w i • a i := by
  refine ext_inner_left ℝ fun x => ?_
  rw [← pairing_apply, ← isAdjointPair_adjoint A x w, pairing_apply, PiLp.inner_apply, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right, ← pairing_apply, pairing_comm, ← h x i]
  simp

/-- **Theorem 22.1 in matrix form** (p. 201). With `A` the matrix whose rows are the `aᵢ`,
alternative (a) is `Ax ≤ a` and alternative (b) is `w ≥ 0`, `A*w = 0`, `⟨w, a⟩ < 0`: whatever the
coefficients, exactly one of the two systems has a solution. -/
theorem theorem_22_1_matrix {A : Rn n →ₗ[ℝ] Rn m} {a : Fin m → Rn n} (h : IsRowsOf A a)
    (α : Rn m) :
    (∃ x : Rn n, ∀ i, A x i ≤ α i) ↔
      ¬ ∃ w : Rn m, (∀ i, 0 ≤ w i) ∧ LinearMap.adjoint A w = 0 ∧ pairing m w α < 0 := by
  have hsum : ∀ w : Rn m, pairing m w α = ∑ i, w i * α i := by
    intro w
    rw [pairing_apply, PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  have hL : (∃ x : Rn n, ∀ i, A x i ≤ α i) ↔ ∃ x : Rn n, ∀ i, pairing n (a i) x ≤ α i :=
    exists_congr fun x => forall_congr' fun i => by rw [h x i]
  rw [hL, theorem_22_1 a fun i => α i]
  refine not_congr ⟨fun hl => ?_, fun hw => ?_⟩
  · obtain ⟨l, hl0, hla, hlα⟩ := hl
    refine ⟨WithLp.toLp 2 l, hl0, ?_, ?_⟩
    · rw [adjoint_eq_sum_smul h]
      exact hla
    · rw [hsum]
      exact hlα
  · obtain ⟨w, hw0, hwa, hwα⟩ := hw
    refine ⟨fun i => w i, hw0, ?_, ?_⟩
    · rw [← adjoint_eq_sum_smul h w]
      exact hwa
    · rw [← hsum w]
      exact hwα

/-! ### The interval form -/

/-- **Real interval** (p. 202): "by a real interval we mean merely a convex subset of `R`; thus
`Iⱼ` may be open or closed or neither, and it may consist of just a single number". -/
def IsRealInterval (I : Set ℝ) : Prop := Convex ℝ I

/-- The **generalized rectangle** `C = {(ζ₁, …, ζ_N) | ζⱼ ∈ Iⱼ, j = 1, …, N}` of p. 203, the set
the subspace `L` of Theorem 22.6 either meets or is separated from. -/
def rectangle {N : ℕ} (I : Fin N → Set ℝ) : Set (Rn N) := {z : Rn N | ∀ j, z j ∈ I j}

@[simp] theorem mem_rectangle {N : ℕ} {I : Fin N → Set ℝ} {z : Rn N} :
    z ∈ rectangle I ↔ ∀ j, z j ∈ I j := Iff.rfl

/-- A generalized rectangle of real intervals is convex. -/
theorem convex_rectangle {N : ℕ} {I : Fin N → Set ℝ} (h : ∀ j, IsRealInterval (I j)) :
    Convex ℝ (rectangle I) := by
  intro x hx y hy s t hs ht hst j
  simpa using h j (hx j) (hy j) hs ht hst

/-- The set `ζ*₁I₁ + ⋯ + ζ*_N I_N` of p. 202, the left side of Rockafellar's `Σ ζ*ⱼIⱼ > 0`. -/
def intervalCombo {N : ℕ} (z : Rn N) (I : Fin N → Set ℝ) : Set ℝ := ∑ j, z j • I j

/-- **Rockafellar's `Σ ζ*ⱼIⱼ > 0`** (p. 202), which is a *set containment*: `ζ*₁ζ₁ + ⋯ + ζ*_NζN > 0`
for every choice of `ζⱼ ∈ Iⱼ`, that is, `Σ ζ*ⱼIⱼ ⊆ (0, +∞)`. -/
def posIntervalCombo {N : ℕ} (z : Rn N) (I : Fin N → Set ℝ) : Prop :=
  intervalCombo z I ⊆ Set.Ioi 0

theorem posIntervalCombo_iff {N : ℕ} {z : Rn N} {I : Fin N → Set ℝ} :
    posIntervalCombo z I ↔ ∀ c ∈ intervalCombo z I, 0 < c := Iff.rfl

/-- "The set `Σ ζ*ⱼIⱼ` is a real interval, by the way, since a linear combination of convex sets is
convex" (p. 203). -/
theorem isRealInterval_intervalCombo {N : ℕ} (z : Rn N) {I : Fin N → Set ℝ}
    (h : ∀ j, IsRealInterval (I j)) : IsRealInterval (intervalCombo z I) := by
  classical
  refine Finset.sum_induction _ (Convex ℝ) (fun s t hs ht => hs.add ht) ?_ ?_
  · rw [← Set.singleton_zero]
    exact convex_singleton 0
  · exact fun j _ => (h j).smul (z j)

/-! ### The interval reading of a linear system (p. 202)

A system in `ℝⁿ` with `m` constraints becomes a *rectangle* problem in `ℝᴺ`, `N = n + m`: append the
`m` constraint values to the `n` unknowns, and the system says exactly that the resulting vector
lies both in a fixed `n`-dimensional subspace `L` — the graph of `A`, written in `ℝᴺ` — and in the
generalized rectangle cut out by the intervals `I₁, …, I_N`. Which system one started from survives
only in the choice of intervals. -/

/-- The vector `z = (ξ₁, …, ξ_n, (Ax)₁, …, (Ax)_m)` of `ℝᴺ`, `N = n + m`, that a solution `x`
becomes when the constraint values are appended to the unknowns (p. 202). -/
noncomputable def intervalVector (A : Rn n →ₗ[ℝ] Rn m) (x : Rn n) : Rn (n + m) :=
  euclideanProdEquiv n m (x, A x)

@[simp] theorem intervalVector_castAdd (A : Rn n →ₗ[ℝ] Rn m) (x : Rn n) (j : Fin n) :
    intervalVector A x (Fin.castAdd m j) = x j :=
  euclideanProdEquiv_apply_castAdd (x, A x) j

@[simp] theorem intervalVector_natAdd (A : Rn n →ₗ[ℝ] Rn m) (x : Rn n) (i : Fin m) :
    intervalVector A x (Fin.natAdd n i) = A x i :=
  euclideanProdEquiv_apply_natAdd (x, A x) i

/-- **The subspace `L` of p. 202**: the vectors `z ∈ ℝᴺ` with `ζ_{n+i} = ∑ⱼ αᵢⱼζⱼ`, that is the
graph of `A` written in `ℝᴺ`. Theorem 22.6 is stated about it, in place of the matrix. -/
noncomputable def intervalSubspace (A : Rn n →ₗ[ℝ] Rn m) : Submodule ℝ (Rn (n + m)) :=
  LinearMap.range ((euclideanProdEquiv n m).toLinearEquiv.toLinearMap.comp
    ((LinearMap.id : Rn n →ₗ[ℝ] Rn n).prod A))

@[simp] theorem mem_intervalSubspace {A : Rn n →ₗ[ℝ] Rn m} {z : Rn (n + m)} :
    z ∈ intervalSubspace A ↔ ∃ x, intervalVector A x = z := Iff.rfl

/-- A vector lies in the rectangle exactly when its unknowns and its constraint values do. -/
theorem intervalVector_mem_rectangle {A : Rn n →ₗ[ℝ] Rn m} {x : Rn n}
    {I : Fin (n + m) → Set ℝ} :
    intervalVector A x ∈ rectangle I ↔
      (∀ j, x j ∈ I (Fin.castAdd m j)) ∧ ∀ i, A x i ∈ I (Fin.natAdd n i) := by
  rw [mem_rectangle]
  refine ⟨fun h => ⟨fun j => ?_, fun i => ?_⟩, fun h => Fin.addCases (fun j => ?_) fun i => ?_⟩
  · simpa using h (Fin.castAdd m j)
  · simpa using h (Fin.natAdd n i)
  · simpa using h.1 j
  · simpa using h.2 i

/-- **The intervals of the system `Ax ≤ a`** (p. 202): `Iⱼ = (-∞, +∞)` for `j = 1, …, n` and
`I_{n+i} = (-∞, αᵢ]` for `i = 1, …, m`. -/
def leIntervals (n : ℕ) {m : ℕ} (α : Rn m) : Fin (n + m) → Set ℝ :=
  Fin.addCases (fun _ : Fin n => Set.univ) fun i => Set.Iic (α i)

@[simp] theorem leIntervals_castAdd {n m : ℕ} (α : Rn m) (j : Fin n) :
    leIntervals n α (Fin.castAdd m j) = Set.univ := Fin.addCases_left j

@[simp] theorem leIntervals_natAdd {n m : ℕ} (α : Rn m) (i : Fin m) :
    leIntervals n α (Fin.natAdd n i) = Set.Iic (α i) := Fin.addCases_right i

/-- **The intervals of the system `x ≥ 0`, `Ax = a`** (p. 202): `Iⱼ = [0, +∞)` for `j = 1, …, n` and
`I_{n+i} = {αᵢ}` for `i = 1, …, m`. -/
def nonnegEqIntervals (n : ℕ) {m : ℕ} (α : Rn m) : Fin (n + m) → Set ℝ :=
  Fin.addCases (fun _ : Fin n => Set.Ici 0) fun i => {α i}

@[simp] theorem nonnegEqIntervals_castAdd {n m : ℕ} (α : Rn m) (j : Fin n) :
    nonnegEqIntervals n α (Fin.castAdd m j) = Set.Ici 0 := Fin.addCases_left j

@[simp] theorem nonnegEqIntervals_natAdd {n m : ℕ} (α : Rn m) (i : Fin m) :
    nonnegEqIntervals n α (Fin.natAdd n i) = {α i} := Fin.addCases_right i

/-- **p. 202, the first interval reading**: `Ax ≤ a` has a solution in `ℝⁿ` exactly when `L` meets
the generalized rectangle cut out by `Iⱼ = (-∞, +∞)` for `j ≤ n` and `I_{n+i} = (-∞, αᵢ]`. This is
the correspondence the second half of §22 is stated over. -/
theorem interval_reading_le (A : Rn n →ₗ[ℝ] Rn m) (α : Rn m) :
    (∃ x : Rn n, ∀ i, A x i ≤ α i) ↔
      ((intervalSubspace A : Set (Rn (n + m))) ∩ rectangle (leIntervals n α)).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨intervalVector A x, ⟨x, rfl⟩, ?_⟩
    exact intervalVector_mem_rectangle.2 ⟨fun j => by simp, fun i => by simpa using hx i⟩
  · rintro ⟨z, ⟨x, rfl⟩, hz⟩
    exact ⟨x, fun i => by simpa using (intervalVector_mem_rectangle.1 hz).2 i⟩

/-- **Rockafellar, p. 202, the second interval reading**: the system `x ≥ 0`, `Ax = a` in `ℝⁿ` has a
solution exactly when the subspace `L` meets the generalized rectangle cut out by `Iⱼ = [0, +∞)`
for `j ≤ n` and `I_{n+i} = {αᵢ}`. -/
theorem interval_reading_nonneg_eq (A : Rn n →ₗ[ℝ] Rn m) (α : Rn m) :
    (∃ x : Rn n, (∀ j, 0 ≤ x j) ∧ A x = α) ↔
      ((intervalSubspace A : Set (Rn (n + m))) ∩ rectangle (nonnegEqIntervals n α)).Nonempty := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨intervalVector A x, ⟨x, rfl⟩, ?_⟩
    exact intervalVector_mem_rectangle.2 ⟨fun j => by simpa using hx j, fun i => by simp⟩
  · rintro ⟨z, ⟨x, rfl⟩, hz⟩
    obtain ⟨h1, h2⟩ := intervalVector_mem_rectangle.1 hz
    refine ⟨x, fun j => by simpa using h1 j, ?_⟩
    ext i
    simpa using h2 i

/-- The intervals of both readings are real intervals, so both rectangles are convex — which is
what makes the conjectured alternative of Theorem 22.6 a separation theorem. -/
theorem isRealInterval_leIntervals {n m : ℕ} (α : Rn m) (j : Fin (n + m)) :
    IsRealInterval (leIntervals n α j) := by
  refine Fin.addCases (fun j => ?_) (fun i => ?_) j
  · rw [leIntervals_castAdd]
    exact convex_univ
  · rw [leIntervals_natAdd]
    exact convex_Iic (α i)

theorem isRealInterval_nonnegEqIntervals {n m : ℕ} (α : Rn m) (j : Fin (n + m)) :
    IsRealInterval (nonnegEqIntervals n α j) := by
  refine Fin.addCases (fun j => ?_) (fun i => ?_) j
  · rw [nonnegEqIntervals_castAdd]
    exact convex_Ici (0 : ℝ)
  · rw [nonnegEqIntervals_natAdd]
    exact convex_singleton (α i)


end Rockafellar
