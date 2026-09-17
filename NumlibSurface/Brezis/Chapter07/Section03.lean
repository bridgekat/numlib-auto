import NumlibSurface.Brezis.Chapter07.Section02

/-!
# Brezis §7.3: regularity

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §7.3: the spaces `D(A^k)`, defined by induction as
`D(A^k) = {v ∈ D(A^{k−1}) ; A v ∈ D(A^{k−1})}`, their Hilbert structure, and Theorem 7.5
(`u ∈ C^{k−j}([0, +∞); D(A^j))` for `u₀ ∈ D(A^k)`), for a maximal monotone `A` on a real Hilbert
space `H`.

## Main definitions and results

* `domainPow A k` — the book's recursive set `D(A^k)`, as a `Submodule ℝ H` (`domainPow_zero`,
  `domainPow_one`, `mem_domainPow_succ_iff` are the recursion); `mem_domainPow_iff` identifies it
  with the first coordinates of the backbone's Hilbert space `A.PowDomain k`
  (`Numlib/Analysis/InnerProductSpace/MaximalMonotone`), the tuples `(u, A u, …, A^k u)` in
  `PiLp 2 (Fin (k + 1) → H)`, which carries the book's inner product on the nose.
* `domainPow_hilbert` — "it is easily seen that `D(A^k)` is a Hilbert space for the scalar
  product `(u, v)_{D(A^k)} = ∑_{j ≤ k} (A^j u, A^j v)`", with the norm
  `|u|_{D(A^k)} = (∑_{j ≤ k} |A^j u|²)^{1/2}`: completeness of `A.PowDomain k` and its inner
  product and norm.
* `theorem_7_5` — for `u₀ ∈ D(A^k)`, the solution `u` of problem (6) (Theorem 7.4) lies in
  `C^{k−j}([0, +∞); D(A^j))` for every `j ≤ k`, where "`u ∈ C^n([0, +∞); D(A^j))`" is the
  backbone's `A.ContDiffOnPowDomain n j u (Ici 0)`: `u` lifts to a `C^n` map into `A.PowDomain j`
  (`Numlib/Analysis/ODE/HilleYosida`). The book's proof — Theorem 7.4 for the part `A₁` of `A`
  in the Hilbert space `H₁ = D(A)`, then induction with `v = du/dt` — is the backbone's ladder
  `IsMaximalMonotone.contDiffOn_semigroup_powPart` over the parts `A.powPart j`, packaged as
  `IsMaximalMonotone.contDiffOnPowDomain_semigroup`; the surface transports it to `u` by the
  uniqueness of Theorem 7.4. The book states the theorem for `k ≥ 2`; it holds for every `k`.
-/

open Filter Topology Set LinearPMap.PowDomain
open scoped InnerProductSpace

noncomputable section

namespace Brezis.Chapter07

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### The spaces `D(A^k)` -/

/-- **Definition (§7.3), the spaces `D(A^k)`**, by induction: `D(A^0) = H`, and
`D(A^{k+1}) = {v ∈ D(A^k) ; v ∈ D(A) and A v ∈ D(A^k)}` — in particular `D(A^1) = D(A)` and,
for `k ≥ 2`, the book's `D(A^k) = {v ∈ D(A^{k−1}) ; A v ∈ D(A^{k−1})}`. As a submodule of `H`:
the second condition is the image under the inclusion `D(A) ⊆ H` of the preimage of `D(A^k)`
under `A`. -/
def domainPow (A : H →ₗ.[ℝ] H) : ℕ → Submodule ℝ H
  | 0 => ⊤
  | k + 1 => domainPow A k ⊓ (Submodule.comap A.toFun (domainPow A k)).map A.domain.subtype

variable {A : H →ₗ.[ℝ] H}

/-- `D(A^0) = H`. -/
@[simp]
theorem domainPow_zero : domainPow A 0 = ⊤ :=
  rfl

/-- The recursion: `v ∈ D(A^{k+1})` iff `v ∈ D(A^k)`, `v ∈ D(A)` and `A v ∈ D(A^k)`. -/
theorem mem_domainPow_succ_iff {k : ℕ} {v : H} :
    v ∈ domainPow A (k + 1) ↔
      v ∈ domainPow A k ∧ ∃ h : v ∈ A.domain, A ⟨v, h⟩ ∈ domainPow A k := by
  simp only [domainPow, Submodule.mem_inf, Submodule.mem_map, Submodule.mem_comap]
  refine and_congr_right fun _ => ⟨fun ⟨y, hy, hyv⟩ => ?_, fun ⟨h, hv⟩ => ⟨⟨v, h⟩, hv, rfl⟩⟩
  obtain ⟨y, hy'⟩ := y
  change y = v at hyv
  subst hyv
  exact ⟨hy', hy⟩

/-- `D(A^1) = D(A)`. -/
@[simp]
theorem domainPow_one : domainPow A 1 = A.domain := by
  ext v
  rw [mem_domainPow_succ_iff, domainPow_zero]
  simp

/-- **`D(A^k)` is the set of first coordinates of the backbone's `D(A^k)`**: `v ∈ D(A^k)` iff
`v` is the `0`-th coordinate of some tuple `(v, A v, …, A^k v)` of `A.PowDomain k`. -/
theorem mem_domainPow_iff {k : ℕ} {v : H} :
    v ∈ domainPow A k ↔ ∃ x : A.PowDomain k, applyL A k 0 x = v := by
  induction k generalizing v with
  | zero =>
    refine ⟨fun _ => ⟨LinearPMap.PowDomain.mk A (fun _ => v) fun i => i.elim0, rfl⟩,
      fun _ => Submodule.mem_top⟩
  | succ k ih =>
    rw [mem_domainPow_succ_iff]
    constructor
    · rintro ⟨-, h, hAv⟩
      obtain ⟨y, hy⟩ := ih.1 hAv
      -- the tuple `(v, A v, …, A^{k+1} v)` is `v` followed by the tuple of `A v`
      refine ⟨LinearPMap.PowDomain.mk A (Fin.cons v fun i => applyL A k i y) fun i => ?_, ?_⟩
      · induction i using Fin.cases with
        | zero =>
          simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]
          exact ⟨h, hy.symm⟩
        | succ j =>
          rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
          exact ⟨applyL_mem_domain y j, apply_applyL y j⟩
      · simp
    · rintro ⟨x, rfl⟩
      exact ⟨ih.2 ⟨castL A k x, by simp⟩, applyL_mem_domain x 0,
        ih.2 ⟨shiftL A k x, applyL_zero_shiftL x⟩⟩

/-- **"It is easily seen that `D(A^k)` is a Hilbert space** for the scalar product
`(u, v)_{D(A^k)} = ∑_{j=0}^k (A^j u, A^j v)`; the corresponding norm is
`|u|_{D(A^k)} = (∑_{j=0}^k |A^j u|²)^{1/2}`." For a maximal monotone (indeed any closed) `A`,
the backbone's `A.PowDomain k` — the tuples `(u, A u, …, A^k u)`, whose first coordinates form
`D(A^k)` by `mem_domainPow_iff` — is complete, and its inner product and norm are the displayed
sums, `A^j u` being the coordinate `applyL A k j`. -/
theorem domainPow_hilbert [CompleteSpace H] (hA : IsMaximalMonotone A) (k : ℕ) :
    CompleteSpace (A.PowDomain k) ∧
      (∀ x y : A.PowDomain k, ⟪x, y⟫_ℝ = ∑ j, ⟪applyL A k j x, applyL A k j y⟫_ℝ) ∧
      ∀ x : A.PowDomain k, ‖x‖ = Real.sqrt (∑ j, ‖applyL A k j x‖ ^ 2) :=
  ⟨(proposition_7_1_b hA).completeSpace_powDomain k, fun x y => inner_def x y, fun x => by
    rw [← norm_sq_eq, Real.sqrt_sq (norm_nonneg _)]⟩

/-! ### Theorem 7.5 -/

/-- **Theorem 7.5.** Let `A` be maximal monotone and `u₀ ∈ D(A^k)` (the book takes `k ≥ 2`; the
statement holds for every `k`). Then the solution `u` of problem (6) obtained in Theorem 7.4
satisfies `u ∈ C^{k−j}([0, +∞); D(A^j))` for every `j = 0, 1, …, k`. -/
theorem theorem_7_5 [CompleteSpace H] (hA : IsMaximalMonotone A) {k : ℕ} {u₀ : H}
    (hu₀ : u₀ ∈ domainPow A k) {u : ℝ → H} (hu : IsSolution A u₀ u) :
    ∀ j ≤ k, A.ContDiffOnPowDomain (k - j : ℕ) j u (Ici 0) := by
  intro j hj
  obtain ⟨x, hx⟩ := mem_domainPow_iff.1 hu₀
  have hmem : u₀ ∈ A.domain := hu.1.apply_zero ▸ hu.1.mem_domain 0 self_mem_Ici
  have hu' : A.IsSolutionOn ((⟨u₀, hmem⟩ : A.domain) : H) (Ici 0) u := hu.1
  refine contDiffOnPowDomain_congr (hA.isMaximalMonotone.contDiffOnPowDomain_semigroup x hj)
    fun t ht => ?_
  rw [hx, (hu'.eq_semigroup hA.isMaximalMonotone ht)]

end Brezis.Chapter07

end
