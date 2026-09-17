import NumlibSurface.Brezis.Chapter07.Section03

/-!
# Brezis §7.4: the self-adjoint case

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §7.4: symmetric and self-adjoint unbounded operators on
a real Hilbert space `H`, Remark 7, Proposition 7.6 (a symmetric maximal monotone operator is
self-adjoint), Remark 8 (maximal monotonicity of `A` and of `A*`), and Theorem 7.7 (for a
self-adjoint maximal monotone `A`, every `u₀ ∈ H` gives a solution, smooth for `t > 0`, with
`|du/dt (t)| ≤ |u₀| / t`).

The book identifies `H* = H` and takes `A*` as an unbounded operator in `H`: this is Mathlib's
Hilbert-space adjoint `LinearPMap.adjoint`, written `A†`
(`Mathlib/Analysis/InnerProductSpace/LinearPMap`), so *symmetric* is Mathlib's
`A.IsFormalAdjoint A` and *self-adjoint* is Mathlib's `IsSelfAdjoint A`, i.e. `A† = A`. The
surface defines both in the book's words — `IsSymmetricOperator`, `IsSelfAdjointOperator`, named
so as not to shadow the root `IsSelfAdjoint` inside the namespace — and proves the equivalences
`isSymmetricOperator_iff`, `isSelfAdjointOperator_iff`. Proposition 7.6 and Remark 8 delegate to
`Numlib/Analysis/InnerProductSpace/MaximalMonotone`, Theorem 7.7 to
`Numlib/Analysis/ODE/HilleYosida`.

## Main results

* `remark_7_7` — a self-adjoint operator is symmetric, and a densely defined `A` is symmetric iff
  `A ⊂ A*` (`D(A) ⊂ D(A*)` and `A* = A` on `D(A)`).
* `proposition_7_6` — a maximal monotone symmetric operator is self-adjoint.
* `remark_7_8` — for a closed, densely defined `A` with `D(A*)` dense: `A` is maximal monotone
  ⟺ `A*` is maximal monotone ⟺ `A` is closed, `D(A)` is dense, and `A`, `A*` are monotone
  (`remark_7_8_adjoint`, `remark_7_8_closed` are the two equivalences; the second needs no
  hypothesis).
* `theorem_7_7` — for a self-adjoint maximal monotone `A` and every `u₀ ∈ H`, there is a unique
  `u ∈ C([0, +∞); H) ∩ C¹((0, +∞); H) ∩ C((0, +∞); D(A))` with `du/dt + A u = 0` on `(0, +∞)`,
  `u(0) = u₀`; moreover `|u(t)| ≤ |u₀|`, `|du/dt (t)| = |A u(t)| ≤ |u₀| / t` for `t > 0`, and
  `u ∈ C^k((0, +∞); D(A^ℓ))` for all integers `k, ℓ` (26).

Footnote 5 is discussion. The counterexample sentences of Remark 7 (a symmetric `A` with
`D(A) ≠ D(A*)`) and Remark 8 (`A*` need not be monotone) are not formalized. Remark 8's first
equivalence needs `D(A*)` dense for `A** = A` (recorded in `notes/book-errata.md`).
-/

open Filter Topology Set
open scoped InnerProductSpace LinearPMap

noncomputable section

namespace Brezis.Chapter07

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {A : H →ₗ.[ℝ] H}

/-! ### The definitions -/

/-- **Definition (§7.4), symmetric.** `A` is *symmetric* if `(A u, v) = (u, A v)` for all
`u, v ∈ D(A)`. -/
def IsSymmetricOperator (A : H →ₗ.[ℝ] H) : Prop :=
  ∀ u v : A.domain, ⟪A u, (v : H)⟫_ℝ = ⟪(u : H), A v⟫_ℝ

/-- The book's symmetry is Mathlib's `A.IsFormalAdjoint A`. -/
theorem isSymmetricOperator_iff (A : H →ₗ.[ℝ] H) : IsSymmetricOperator A ↔ A.IsFormalAdjoint A :=
  Iff.rfl

variable [CompleteSpace H]

/-- **Definition (§7.4), self-adjoint.** `A` is *self-adjoint* if `D(A*) = D(A)` and `A* = A`,
where `A*` is the adjoint `A†` of `A` viewed as an unbounded operator in `H` (identifying
`H* = H`). -/
def IsSelfAdjointOperator (A : H →ₗ.[ℝ] H) : Prop :=
  A†.domain = A.domain ∧ ∀ (u : A.domain) (v : A†.domain), (u : H) = v → A† v = A u

/-- The book's self-adjointness is Mathlib's `IsSelfAdjoint A`, i.e. `A† = A`. -/
theorem isSelfAdjointOperator_iff (A : H →ₗ.[ℝ] H) : IsSelfAdjointOperator A ↔ IsSelfAdjoint A := by
  rw [LinearPMap.isSelfAdjoint_def]
  constructor
  · rintro ⟨hd, h⟩
    exact LinearPMap.dExt hd fun x y hxy => h y x hxy.symm
  · intro heq
    obtain ⟨hd, h⟩ := LinearPMap.dExt_iff.1 heq
    exact ⟨hd, fun u v huv => h huv.symm⟩

/-- **Remark 7.** Any self-adjoint operator is symmetric; and a densely defined `A` is symmetric
iff `A ⊂ A*`, i.e. `D(A) ⊂ D(A*)` and `A* = A` on `D(A)`. (That `A` may be symmetric with
`D(A) ≠ D(A*)` is a counterexample claim and is not formalized; for maximal monotone `A` the two
notions coincide, Proposition 7.6.) -/
theorem remark_7_7 (A : H →ₗ.[ℝ] H) (hd : Dense (A.domain : Set H)) :
    (IsSelfAdjointOperator A → IsSymmetricOperator A) ∧
      (IsSymmetricOperator A ↔ A.domain ≤ A†.domain ∧
        ∀ (u : A.domain) (v : A†.domain), (u : H) = v → A† v = A u) := by
  refine ⟨fun h => ((isSelfAdjointOperator_iff A).1 h).isFormalAdjoint_self, ?_⟩
  rw [isSymmetricOperator_iff, LinearPMap.IsFormalAdjoint.le_adjoint_iff hd]
  exact ⟨fun h => ⟨h.1, fun u v huv => (h.2 huv).symm⟩,
    fun h => ⟨h.1, fun u v huv => (h.2 u v huv).symm⟩⟩

/-- **Proposition 7.6.** A maximal monotone symmetric operator is self-adjoint. -/
theorem proposition_7_6 (hA : IsMaximalMonotone A) (hs : IsSymmetricOperator A) :
    IsSelfAdjointOperator A :=
  (isSelfAdjointOperator_iff A).2 (hA.isMaximalMonotone.isSelfAdjoint_of_isFormalAdjoint hs)

/-- **Remark 8, the first equivalence.** For a closed, densely defined `A` whose adjoint is
densely defined (so that `A** = A`), `A` is maximal monotone iff `A*` is. -/
theorem remark_7_8_adjoint (hcl : A.IsClosed) (hd : Dense (A.domain : Set H))
    (hd' : Dense (A†.domain : Set H)) : IsMaximalMonotone A ↔ IsMaximalMonotone A† := by
  rw [isMaximalMonotone_iff, isMaximalMonotone_iff]
  exact LinearPMap.isMaximalMonotone_iff_adjoint hcl hd hd'

/-- **Remark 8, the second equivalence.** `A` is maximal monotone iff `A` is closed, `D(A)` is
dense, and `A` and `A*` are monotone (no hypothesis on `A` is needed). -/
theorem remark_7_8_closed (A : H →ₗ.[ℝ] H) :
    IsMaximalMonotone A ↔
      A.IsClosed ∧ Dense (A.domain : Set H) ∧ IsMonotone A ∧ IsMonotone A† := by
  rw [isMaximalMonotone_iff, isMonotone_iff, isMonotone_iff]
  exact LinearPMap.isMaximalMonotone_iff_isClosed_dense_isMonotone

/-- **Remark 8.** For a closed, densely defined `A` with `D(A*)` dense, the following are
equivalent: `A` is maximal monotone; `A*` is maximal monotone; `A` is closed, `D(A)` is dense,
and `A`, `A*` are monotone. (That `A*` need not be monotone when `A` is merely a symmetric
monotone operator is a counterexample claim and is not formalized; the general Banach-space
version is the book's Problem 16.) -/
theorem remark_7_8 (hcl : A.IsClosed) (hd : Dense (A.domain : Set H))
    (hd' : Dense (A†.domain : Set H)) :
    [IsMaximalMonotone A, IsMaximalMonotone A†,
      A.IsClosed ∧ Dense (A.domain : Set H) ∧ IsMonotone A ∧ IsMonotone A†].TFAE := by
  tfae_have 1 ↔ 2 := remark_7_8_adjoint hcl hd hd'
  tfae_have 1 ↔ 3 := remark_7_8_closed A
  tfae_finish

/-! ### Theorem 7.7 -/

/-- **Theorem 7.7.** Let `A` be a self-adjoint maximal monotone operator. Then for every
`u₀ ∈ H` there is a unique `u ∈ C([0, +∞); H) ∩ C¹((0, +∞); H) ∩ C((0, +∞); D(A))` with
`du/dt + A u = 0` on `(0, +∞)` and `u(0) = u₀` (uniqueness among solutions on `(0, +∞)` that are
continuous on `[0, +∞)`). Moreover `|u(t)| ≤ |u₀|` for `t ≥ 0`, `|du/dt (t)| = |A u(t)| ≤ |u₀| / t`
for `t > 0`, and (26) `u ∈ C^k((0, +∞); D(A^ℓ))` for all integers `k, ℓ`. The solution is
`t ↦ S_A(t) u₀`; the book's Step 1 is the backbone's Lyapunov-function estimate
`norm_exp_neg_smul_apply_le_div`, Step 2 is `semigroup_apply_mem_domain_of_isFormalAdjoint`, and
(26) is `contDiffOnPowDomain_semigroup_Ioi` (`Numlib/Analysis/ODE/HilleYosida`). -/
theorem theorem_7_7 (hA : IsMaximalMonotone A) (hs : IsSelfAdjointOperator A) (u₀ : H) :
    ∃ u : ℝ → H, ∃ hu : A.IsSolutionOn u₀ (Ioi 0) u,
      ContinuousOn u (Ici 0) ∧ ContDiffOn ℝ 1 u (Ioi 0) ∧ A.ContDiffOnPowDomain 0 1 u (Ioi 0) ∧
      (∀ v, A.IsSolutionOn u₀ (Ioi 0) v → ContinuousOn v (Ici 0) → EqOn v u (Ici 0)) ∧
      (∀ t, 0 ≤ t → ‖u t‖ ≤ ‖u₀‖) ∧
      (∀ t (ht : 0 < t), ‖deriv u t‖ = ‖A ⟨u t, hu.mem_domain t ht⟩‖ ∧
        ‖A ⟨u t, hu.mem_domain t ht⟩‖ ≤ ‖u₀‖ / t) ∧
      ∀ k l : ℕ, A.ContDiffOnPowDomain k l u (Ioi 0) := by
  obtain ⟨u, hu, hc, hc1, hle, hdiv, hpow⟩ := LinearPMap.exists_isSolutionOn_Ioi_of_isSelfAdjoint
    hA.isMaximalMonotone ((isSelfAdjointOperator_iff A).1 hs) u₀
  refine ⟨u, hu, hc, hc1, by simpa using hpow 0 1,
    fun v hv hvc => hA.isMaximalMonotone.isMonotone.eqOn_of_isSolutionOn_Ioi hv hu hvc hc, hle,
    fun t ht => ⟨?_, hdiv t ht⟩, hpow⟩
  rw [((hu.hasDerivWithinAt t ht).hasDerivAt (Ioi_mem_nhds ht)).deriv, norm_neg]

end Brezis.Chapter07

end
