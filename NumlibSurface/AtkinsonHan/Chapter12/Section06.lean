import NumlibSurface.AtkinsonHan.Chapter12.Section04

/-!
# Atkinson–Han §12.6: iteration methods for the discretized equations

Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009.

The linear systems produced by the methods of this chapter are large and dense, so they are solved
by residual correction rather than by elimination.  §12.6.2 is the two-grid iteration for the
Nyström method: the residual of the *fine* equation `(λ - K_n) u_n = f` is corrected with the
inverse of the *coarse* operator `λ - K_m`, which is the only inverse ever formed.  As in §12.1 the
book's scalar `λ` is written `μ`, `λ` being Lean's lambda binder.

## Main results

* `twoGridStep`, `equation_12_6_20` — (12.6.20)–(12.6.22), the residual, the coarse correction and
  the update, as one step of the residual correction method (12.6.5)–(12.6.6) whose approximate
  inverse `C_n` is `(λ - K_m)⁻¹`.
* `twoGridOperator`, `equation_12_6_27` — (12.6.27)–(12.6.28), the error identity
  `u_n - u_n^{(κ+1)} = M_{m,n} (u_n - u_n^{(κ)})` with
  `M_{m,n} = (1/λ) (λ - K_m)⁻¹ (K_n - K_m) K_n`, and the geometric bound it gives.
* `theorem_12_6_1` — for a collectively compact, pointwise convergent family with `λ - K`
  invertible, every large enough coarse index `m` makes `λ - K_m` invertible and `‖M_{m,n}‖ < 1`
  for *every* fine index `n ≥ m`, so the two-grid iterates converge to `u_n` from every starting
  point.

## Not formalized here

§12.6.3, the translation of the operator iteration into the linear system `A_n u_n = f_n`, and
§12.6.4, the operation count.  Both are implementation, with no theorem content.

## Conventions

The book states Theorem 12.6.1 for the Nyström operators of §12.4 on `C(D)`.  Its proof uses only
that the family is collectively compact and pointwise convergent — the assumptions A1–A3 of
`IsCollectivelyCompactFamily` — so that is the form stated here, and the Nyström case is the
instance.  The two indices both have to be large for a reason that the book's `n, m → ∞` hides:
`(K_n - K_m) K_n` splits into `(K_n - K) K_n`, which needs `n` large, and `(K - K_m) K_n`, which
has to be small *uniformly in `n`* and so is not covered by the diagonal estimate
`lemma_12_4_7_d`.
-/

open Filter Topology

namespace AtkinsonHan.Ch12

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-! ### The two-grid iteration -/

/-- **(12.6.20)–(12.6.22)**, one step of the two-grid iteration for the fine equation
`(λ - K_n) u = f`: form the residual `r = f - (λ - K_n) u`, correct it with the *coarse* inverse,
`δ = (λ - K_m)⁻¹ (K_n r)`, and update `u ↦ u + (r + δ)/λ`.

The coarse equivalence is carried as `e : X ≃L[𝕜] X` with `↑e = λ - K_m`, so that `e.symm` is a
genuine inverse; it is the approximate inverse `C_n` of the residual correction method
(12.6.5)–(12.6.6), and the only inverse the method ever forms.  This is the backbone
`SecondKind.twoGridStep`. -/
noncomputable abbrev twoGridStep (μ : 𝕜) (e : X ≃L[𝕜] X) (Kn : X →L[𝕜] X) (f u : X) : X :=
  SecondKind.twoGridStep μ e Kn f u

/-- The three displays **(12.6.20)–(12.6.22)** written out: the residual `r_n^{(κ)}`, and the
update built from it and from the coarse correction. -/
theorem equation_12_6_20 (μ : 𝕜) (e : X ≃L[𝕜] X) (Kn : X →L[𝕜] X) (f u : X) :
    SecondKind.residual μ Kn f u = f - (μ • 1 - Kn : X →L[𝕜] X) u ∧
      twoGridStep μ e Kn f u = u + μ⁻¹ • (SecondKind.residual μ Kn f u
        + e.symm (Kn (SecondKind.residual μ Kn f u))) :=
  ⟨rfl, rfl⟩

/-- **(12.6.28)**, the iteration operator `M_{m,n} = (1/λ) (λ - K_m)⁻¹ (K_n - K_m) K_n` of the
two-grid method, where `e` is the coarse equivalence `↑e = λ - K_m`.  The factor `K_n - K_m`
appears composed with `K_n`, which is the shape that collective compactness makes small even
though `‖K_n - K_m‖` does not tend to zero.  This is the backbone
`SecondKind.twoGridOperator`. -/
noncomputable abbrev twoGridOperator (μ : 𝕜) (e : X ≃L[𝕜] X) (Km Kn : X →L[𝕜] X) : X →L[𝕜] X :=
  SecondKind.twoGridOperator μ e Km Kn

/-- **(12.6.27)** and its consequence: if `u_n` solves the fine equation `(λ - K_n) u_n = f`, then
one two-grid step multiplies the error by `M_{m,n}`,

`u_n - u_n^{(κ+1)} = M_{m,n} (u_n - u_n^{(κ)})`,

and hence `‖u_n - u_n^{(κ)}‖ ≤ ‖M_{m,n}‖^κ ‖u_n - u_n^{(0)}‖`.  The identity is algebra: no
compactness, no completeness and no bound on `M_{m,n}` is used. -/
theorem equation_12_6_27 {μ : 𝕜} (hμ : μ ≠ 0) {e : X ≃L[𝕜] X} {Km Kn : X →L[𝕜] X}
    (he : (e : X →L[𝕜] X) = μ • 1 - Km) {f ustar : X}
    (hstar : (μ • 1 - Kn : X →L[𝕜] X) ustar = f) (u : X) :
    ustar - twoGridStep μ e Kn f u = twoGridOperator μ e Km Kn (ustar - u) ∧
      ∀ k : ℕ, ‖ustar - (twoGridStep μ e Kn f)^[k] u‖ ≤
        ‖twoGridOperator μ e Km Kn‖ ^ k * ‖ustar - u‖ :=
  ⟨SecondKind.twoGrid_error_eq hμ he hstar u,
    SecondKind.norm_sub_twoGridStep_iterate_le hμ he hstar u⟩

/-! ### Convergence -/

variable {K : ℕ → X →L[𝕜] X} {L : X →L[𝕜] X}

/-- **Theorem 12.6.1**: let `{K_p}` be a collectively compact family converging pointwise to `K`,
with `λ ≠ 0` and `λ - K` invertible.  Then for every sufficiently large coarse index `m` the
coarse operator `λ - K_m` is invertible and, for *every* fine index `n ≥ m`,

`‖M_{m,n}‖ < 1`,

so the two-grid iterates converge to the solution `u_n` of `(λ - K_n) u_n = f` from every starting
point, geometrically by `equation_12_6_27`.

The book states this for the Nyström operators on `C(D)`; the proof uses only the assumptions
A1–A3, which is `IsCollectivelyCompactFamily`.  Both indices have to be large: `(K_n - K_m) K_n`
splits into `(K_n - K) K_n`, which `lemma_12_4_7_d` makes small for large `n`, and `(K - K_m) K_n`,
which must be small uniformly in `n` and is the backbone
`SecondKind.eventually_forall_opNorm_sub_comp_lt`. -/
theorem theorem_12_6_1 [CompleteSpace X] {μ : 𝕜} (hμ : μ ≠ 0)
    (h : IsCollectivelyCompactFamily K L) {e : X ≃L[𝕜] X} (he : (e : X →L[𝕜] X) = μ • 1 - L) :
    ∀ᶠ m in atTop, ∃ em : X ≃L[𝕜] X, (em : X →L[𝕜] X) = μ • 1 - K m ∧
      ∀ n ≥ m, ‖twoGridOperator μ em (K m) (K n)‖ < 1 ∧
        ∀ f un : X, (μ • 1 - K n : X →L[𝕜] X) un = f → ∀ u₀ : X,
          Tendsto (fun k => (twoGridStep μ em (K n) f)^[k] u₀) atTop (𝓝 un) := by
  filter_upwards [SecondKind.eventually_norm_twoGridOperator_lt_one hμ h.isCollectivelyCompact
    h.tendsto he] with m hm
  obtain ⟨em, hem, hlt⟩ := hm
  exact ⟨em, hem, fun n hn =>
    ⟨hlt n hn, fun f un hun u₀ => SecondKind.tendsto_twoGridIterate hμ hem (hlt n hn) hun u₀⟩⟩

end AtkinsonHan.Ch12
