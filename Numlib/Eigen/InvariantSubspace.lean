import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.ZPow
import Numlib.Analysis.InnerProductSpace.Projection.Gap
import Numlib.Analysis.Normed.Operator.QuadraticEquation
import Numlib.Eigen.PowerMethod
import Numlib.LinearAlgebra.Matrix.Sylvester

/-!
# Invariant subspaces: uniqueness, perturbation, and subspace iteration

Invariant subspaces of a matrix or operator: their uniqueness for a set of eigenvalues, their
perturbation (Stewart's theorem), the transport of graph subspaces by powers, and the convergence of
subspace (orthogonal) iteration to the dominant one with explicit constants.

## Main results

* **Uniqueness.** An `A`-invariant subspace on which `A` has only eigenvalues from a set `Λ`, of the
  dimension of `⨆_{μ ∈ Λ} maxGenEigenspace A μ` (the total algebraic multiplicity of `Λ`), *is* that
  subspace (`Module.End.invtSubmodule_eq_iSup_maxGenEigenspace`). That is the precise sense of
  [golub2013matrix]'s "the unique invariant subspace associated with the eigenvalues λ₁, …, λ_r"
  (§7.3.2, the dominant invariant subspace `D_r(A)`, and §7.6.2, the first `p` Schur vectors when
  `λ(T₁₁) ∩ λ(T₂₂) = ∅`); the matrix form is `Matrix.span_cols_eq_iSup_maxGenEigenspace_of_conj`.
* **Powers from a Schur form** ([golub2013matrix] Lemma 7.3.2): with `Qᴴ A Q = D + N`,
  `‖A^k‖₂ ≤ (1+μ)^{n-1} (max |t_ii| + ‖N‖_F/(1+μ))^k` (`Matrix.l2_opNorm_pow_le_of_schur`) and the
  inverse-power bound (`Matrix.l2_opNorm_inv_pow_le_of_schur`); the diagonal scaling
  `Δ = diag(1, 1+μ, …, (1+μ)^{n-1})` shrinks the strictly upper part by `1+μ`
  (`Matrix.frobenius_norm_diagonal_mul_mul_inv_le`).
* **Stewart's perturbation theorem** ([golub2013matrix] Theorem 7.2.4, after G. W. Stewart, SIAM
  Rev. 15 (1973), Theorem 4.11), `Matrix.exists_invariant_graph_of_sep`. In Schur coordinates
  `T = fromBlocks T₁₁ T₁₂ 0 T₂₂` and a perturbation `E` with blocks `Eᵢⱼ`, the column space of
  `fromRows 1 P` is `(T + E)`-invariant exactly when `P` solves the Riccati equation
  `P A₁₁ - A₂₂ P + P A₁₂ P = E₂₁` (`Aᵢⱼ` the blocks of `T + E`). Its linear part is
  `-sylvesterMap A₂₂ A₁₁`, bounded below by `sep(A₂₂, A₁₁) = sep(A₁₁, A₂₂)` (`Matrix.sep_comm`),
  and `sep(A₁₁, A₂₂) ≥ sep(T₁₁, T₂₂) - ‖E₁₁‖_F - ‖E₂₂‖_F` (`Matrix.sep_sub_le_sep_add`); Stewart's
  quadratic-equation lemma (`ContinuousLinearEquiv.exists_apply_add_eq_of_quadratic`) solves it with
  `‖P‖_F ≤ 2γ/δ` when `4γη < δ²`. With the book's hypothesis
  `‖E‖_F (1 + 5‖T₁₂‖_F/sep) ≤ sep/5`: `δ ≥ 3 sep/5` and `γη ≤ sep²/25`, so `4γη < δ²` and
  `‖P‖_F ≤ (10/3) ‖E₂₁‖_F/sep ≤ 4 ‖E₂₁‖_F/sep` — the book's constants, with room.
* **Graph subspaces** ([golub2013matrix] Corollary 7.2.5 and (7.2.6)): the gap between
  `ran [I; 0]` and `ran [I; P]` is at most `‖P‖₂` (`Matrix.gap_range_fromRows_le`); coordinate-free,
  a subspace at gap `< 1` from `K` of the same dimension is the graph of some `X : K → Kᗮ`
  (`Submodule.exists_eq_graph_of_gap_lt_one`) with `‖X‖ = d/√(1 - d²)`
  (`Submodule.norm_eq_gap_graph_div`, inverting `Submodule.gap_graph` of
  `Numlib/Analysis/InnerProductSpace/Projection/Gap`). The gap is unitarily invariant
  (`Submodule.gap_map_linearIsometryEquiv`).
* **Transport of graphs by powers** (`Krylov.subspaceIterate_graph`): for complementary invariant
  `K`, `W` with `A` bijective on `K`, `A^k` carries the graph of `X : K → W` to the graph of
  `A₂^k X A₁^{-k}`. Pure algebra; it is the coordinate-free core of the appendix proof of
  [golub2013matrix] Theorem 7.3.1 and of Theorem 8.2.2.
* **Subspace iteration for a symmetric operator** ([golub2013matrix] Theorem 8.2.2):
  `gap D (A^k S) ≤ (r/ρ)^k d₀/√(1 - d₀²)` (`LinearMap.IsSymmetric.gap_subspaceIterate_le`, through
  `LinearMap.IsSymmetric.gap_subspaceIterate_le_of_invariant`), the `tan Θ` form of the book's
  argument with no CS decomposition.

## The corrected Theorem 7.3.1

[golub2013matrix] Theorem 7.3.1 bounds the distance of the orthogonal iterates to `D_r(A)` under the
hypothesis `d₀ = dist(D_r(A), ran Q₀) < 1`. That hypothesis is the wrong one — the proof uses
`dist(D_r(Aᴴ), ran Q₀) < 1`, and the text after the theorem says so in words — and the printed
theorem is false: for `A = [[2, 1], [0, 1]]`, `r = 1` and `Q₀ = (1, -1)/√2` (an eigenvector for
`λ₂ = 1`), `d₀ = 1/√2 < 1` but `d_k = 1/√2` for all `k`. The corrected statement
(`Matrix.gap_subspaceIterate_le_of_schur`, with the factor `d₀/√(1 - d̃₀²)`,
`d̃₀ = dist(D_r(Aᴴ), ran Q₀)`) is proved without graphs or a CS decomposition: its
coordinate-free core `Krylov.gap_subspaceIterate_le_of_isCompl` bounds `gap D (A^k S)` for
complementary invariant `D`, `W` by the norm of the oblique projection onto `D` along `W`, the
compression of `A^k` to `Dᗮ` and the inverse of `A^k` on `D`; in Schur coordinates these are
`1 + ‖X‖₂` (`X` the Sylvester solution, `W = ran [X; I]`), `‖T₂₂^k‖₂` and `‖T₁₁^{-k}‖₂`, bounded by
Lemma 7.3.2 and `‖X‖_F ≤ ‖T₁₂‖_F/sep`.

Mathlib has invariant submodules (`Module.End.invtSubmodule`) and generalized eigenspaces, nothing
on their perturbation; `Numlib/Eigen/PowerMethod` has the qualitative convergence of subspace
iteration (`Krylov.exists_gap_subspaceIterate_le`), which assumes diagonalizability and gives no
constant.
-/

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- An invariant subspace on which every eigenvalue lies in `Λ` is contained in the sum of the
generalized eigenspaces of `Λ`: over an algebraically closed field, `S` is the sum of the
generalized eigenspaces of `A|_S` (`Module.End.iSup_maxGenEigenspace_eq_top`), each inside the
corresponding one of `A`, and those of eigenvalues outside `Λ` vanish. -/
theorem invtSubmodule_le_iSup_maxGenEigenspace [IsAlgClosed K] [FiniteDimensional K V]
    {A : Module.End K V} {Λ : Set K} {S : Submodule K V} (hS : S ∈ A.invtSubmodule)
    (hΛ : ∀ μ ∉ Λ, ∀ x ∈ S, A x = μ • x → x = 0) :
    S ≤ ⨆ μ ∈ Λ, A.maxGenEigenspace μ := by
  have hS' : ∀ x ∈ S, A x ∈ S := (A.mem_invtSubmodule_iff_forall_mem_of_mem).1 hS
  have hall : ⨆ μ, A.genEigenspace μ ⊤ = ⊤ := iSup_maxGenEigenspace_eq_top A
  calc S = S ⊓ ⨆ μ, A.genEigenspace μ ⊤ := by rw [hall, inf_top_eq]
    _ = ⨆ μ, S ⊓ A.genEigenspace μ ⊤ := Submodule.inf_iSup_genEigenspace hS' ⊤
    _ ≤ ⨆ μ ∈ Λ, A.maxGenEigenspace μ := iSup_le fun μ => ?_
  by_cases hμ : μ ∈ Λ
  · exact inf_le_right.trans (le_iSup₂_of_le μ hμ le_rfl)
  rw [Submodule.inf_genEigenspace A S hS']
  have h0 : Module.End.genEigenspace (A.restrict hS') μ ⊤ = ⊥ := by
    by_contra h
    have h1 : Module.End.HasUnifEigenvalue (A.restrict hS') μ ⊤ := h
    rw [hasUnifEigenvalue_iff_hasUnifEigenvalue_one (by simp)] at h1
    obtain ⟨x, hx⟩ := HasEigenvalue.exists_hasEigenvector h1
    have hAx : A x = μ • (x : V) := by
      simpa using congrArg Subtype.val hx.apply_eq_smul
    exact hx.2 (Subtype.ext (hΛ μ hμ x x.2 hAx))
  rw [h0, Submodule.map_bot]
  exact bot_le

/-- **Uniqueness of the invariant subspace of a spectral set** ([golub2013matrix] §7.3.2, §7.6.2):
over an algebraically closed field, an `A`-invariant subspace `S` on which every eigenvalue of `A`
lies in `Λ` (`A x = μ x`, `x ∈ S`, `μ ∉ Λ` force `x = 0`) and whose dimension is that of
`⨆ μ ∈ Λ, maxGenEigenspace A μ` (the sum of the algebraic multiplicities) *is* that subspace. -/
theorem invtSubmodule_eq_iSup_maxGenEigenspace [IsAlgClosed K] [FiniteDimensional K V]
    {A : Module.End K V} {Λ : Set K} {S : Submodule K V} (hS : S ∈ A.invtSubmodule)
    (hΛ : ∀ μ ∉ Λ, ∀ x ∈ S, A x = μ • x → x = 0)
    (hdim : Module.finrank K S = Module.finrank K ↥(⨆ μ ∈ Λ, A.maxGenEigenspace μ)) :
    S = ⨆ μ ∈ Λ, A.maxGenEigenspace μ :=
  Submodule.eq_of_le_of_finrank_eq (invtSubmodule_le_iSup_maxGenEigenspace hS hΛ) hdim

end Module.End

namespace Matrix

section Block

variable {K : Type*} [Field K] {n p q : Type*} [Fintype n] [DecidableEq n] [Fintype p]
  [DecidableEq p] [Fintype q] [DecidableEq q]

omit [DecidableEq n] [DecidableEq p] [DecidableEq q] in
/-- A matrix whose reindexing is block upper triangular acts blockwise on coordinates. -/
theorem mulVec_comp_symm_of_reindex_eq_fromBlocks {T : Matrix n n K} (e : n ≃ p ⊕ q)
    {T₁₁ : Matrix p p K} {T₁₂ : Matrix p q K} {T₂₂ : Matrix q q K}
    (hT : T.reindex e e = fromBlocks T₁₁ T₁₂ 0 T₂₂) (v : n → K) :
    (T *ᵥ v) ∘ e.symm = Sum.elim (T₁₁ *ᵥ (v ∘ e.symm ∘ Sum.inl) + T₁₂ *ᵥ (v ∘ e.symm ∘ Sum.inr))
      (T₂₂ *ᵥ (v ∘ e.symm ∘ Sum.inr)) := by
  have h : T.reindex e e *ᵥ (v ∘ e.symm) = (T *ᵥ v) ∘ e.symm := by
    rw [reindex_apply, submatrix_mulVec_equiv]
    congr 2
    ext i
    simp
  rw [← h, hT, fromBlocks_mulVec, zero_mulVec, zero_add]
  rfl

/-- **The first `p` Schur vectors span the invariant subspace of `λ(T₁₁)`** ([golub2013matrix]
§7.6.2, "the first `p` columns of `Q` span the unique invariant subspace associated with
`λ(T₁₁)`"; and the dominant invariant subspace `D_r(A)` of §7.3.2): if `Q` is invertible and
`(Q⁻¹ A Q).reindex e e = fromBlocks T₁₁ T₁₂ 0 T₂₂` with `λ(T₁₁) ∩ λ(T₂₂) = ∅`, then the span of the
columns `Q.col (e.symm (inl i))` is `⨆ μ ∈ λ(T₁₁), maxGenEigenspace A μ`. The span is invariant
with eigenvalues in `λ(T₁₁)` (`Module.End.invtSubmodule_le_iSup_maxGenEigenspace`); conversely the
trailing coordinates `π x = (Q⁻¹ x)(e.symm (inr ·))` intertwine `A` with `T₂₂`, so on a generalized
eigenvector for `μ ∉ λ(T₂₂)` they vanish, and `ker π` is the span. -/
theorem span_cols_eq_iSup_maxGenEigenspace_of_conj [IsAlgClosed K] {A Q : Matrix n n K}
    (hQ : IsUnit Q) (e : n ≃ p ⊕ q) {T₁₁ : Matrix p p K} {T₁₂ : Matrix p q K}
    {T₂₂ : Matrix q q K} (hT : (Q⁻¹ * A * Q).reindex e e = fromBlocks T₁₁ T₁₂ 0 T₂₂)
    (hdisj : Disjoint (spectrum K T₁₁) (spectrum K T₂₂)) :
    Submodule.span K (Set.range fun i : p => Q.col (e.symm (Sum.inl i))) =
      ⨆ μ ∈ spectrum K T₁₁, Module.End.maxGenEigenspace (toLin' A) μ := by
  set T := Q⁻¹ * A * Q with hTdef
  have hQd : IsUnit Q.det := (isUnit_iff_isUnit_det Q).1 hQ
  have hQQ : Q * Q⁻¹ = 1 := mul_nonsing_inv Q hQd
  have hQQ' : Q⁻¹ * Q = 1 := nonsing_inv_mul Q hQd
  have hAQ : A * Q = Q * T := by
    rw [hTdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
  have hQA : Q⁻¹ * A = T * Q⁻¹ := by
    rw [hTdef, Matrix.mul_assoc, Matrix.mul_assoc, hQQ, Matrix.mul_one]
  have hblk := mulVec_comp_symm_of_reindex_eq_fromBlocks e hT
  -- the embedding of the leading block and the trailing coordinates
  set w : (p → K) → n → K := fun c => Sum.elim c 0 ∘ e with hw
  have hwsymm : ∀ c, w c ∘ e.symm = Sum.elim c 0 := fun c => by
    ext s; simp [hw]
  have hTw : ∀ c, T *ᵥ w c = w (T₁₁ *ᵥ c) := fun c => by
    ext j
    have h := congrFun (hblk (w c)) (e j)
    have h1 : w c ∘ e.symm ∘ Sum.inl = c := by ext i; simp [hw]
    have h2 : w c ∘ e.symm ∘ Sum.inr = 0 := by ext i; simp [hw]
    rw [h1, h2] at h
    simp only [Function.comp_apply, Equiv.symm_apply_apply, mulVec_zero, add_zero] at h
    rw [h]
    simp [hw]
  -- the span is the range of `c ↦ Q w c`
  have hcol : ∀ i, Q.col (e.symm (Sum.inl i)) = Q *ᵥ w (Pi.single i 1) := fun i => by
    ext j
    simp only [col_apply, mulVec, dotProduct, hw, Function.comp_apply]
    rw [Finset.sum_eq_single (e.symm (Sum.inl i))]
    · simp
    · intro b _ hb
      rcases hbe : e b with k | k
      · have hki : k ≠ i := fun hk => hb (by rw [← hk, ← hbe, Equiv.symm_apply_apply])
        simp [hki]
      · simp
    · simp
  set L : (p → K) →ₗ[K] n → K :=
    { toFun := fun c => Q *ᵥ w c
      map_add' := fun c d => by
        rw [← mulVec_add]; congr 1; ext j
        rcases h : e j with i | i <;> simp [hw, h]
      map_smul' := fun a c => by
        rw [RingHom.id_apply, ← mulVec_smul]; congr 1; ext j
        rcases h : e j with i | i <;> simp [hw, h] } with hL
  have hspan : Submodule.span K (Set.range fun i : p => Q.col (e.symm (Sum.inl i)))
      = LinearMap.range L := by
    rw [LinearMap.range_eq_map, ← (Pi.basisFun K p).span_eq, Submodule.map_span,
      ← Set.range_comp]
    congr 1
    ext i
    simp [hL, hcol]
  rw [hspan]
  apply le_antisymm
  · -- the span is invariant, with eigenvalues in `λ(T₁₁)`
    have hinv : LinearMap.range L ∈ Module.End.invtSubmodule (toLin' A) := by
      rintro _ ⟨c, rfl⟩
      refine ⟨T₁₁ *ᵥ c, ?_⟩
      simp only [hL, LinearMap.coe_mk, AddHom.coe_mk, toLin'_apply]
      rw [mulVec_mulVec, hAQ, ← mulVec_mulVec, hTw]
    refine Module.End.invtSubmodule_le_iSup_maxGenEigenspace hinv fun μ hμ x hx hAx => ?_
    obtain ⟨c, rfl⟩ := hx
    simp only [hL, LinearMap.coe_mk, AddHom.coe_mk, toLin'_apply] at hAx ⊢
    rw [mulVec_mulVec, hAQ, ← mulVec_mulVec, hTw, ← mulVec_smul] at hAx
    have hinj : ∀ u v : n → K, Q *ᵥ u = Q *ᵥ v → u = v := fun u v h => by
      have := congrArg (Q⁻¹ *ᵥ ·) h
      simpa only [mulVec_mulVec, hQQ', one_mulVec] using this
    have h1 := congrArg (· ∘ e.symm) (hinj _ _ hAx)
    simp only [hwsymm] at h1
    have hsm : (μ • w c) ∘ e.symm = Sum.elim (μ • c) 0 := by
      ext s; rcases s with i | i <;> simp [hw]
    rw [hsm] at h1
    have hc : T₁₁ *ᵥ c = μ • c := by
      funext i; exact congrFun h1 (Sum.inl i)
    by_cases hc0 : c = 0
    · subst hc0
      have : w 0 = 0 := by ext j; rcases h : e j with i | i <;> simp [hw, h]
      rw [this, mulVec_zero]
    exact absurd ((mem_spectrum_iff_exists_mulVec_eq_smul T₁₁ μ).2 ⟨c, hc0, hc⟩) hμ
  · -- a generalized eigenvector of `λ(T₁₁)` has vanishing trailing coordinates
    refine iSup₂_le fun μ hμ x hx => ?_
    have hμ2 : μ ∉ spectrum K T₂₂ := Set.disjoint_left.1 hdisj hμ
    set π : (n → K) → q → K := fun y => (Q⁻¹ *ᵥ y) ∘ e.symm ∘ Sum.inr with hπ
    have hπA : ∀ y, π ((A - μ • 1) *ᵥ y) = (T₂₂ - μ • 1) *ᵥ π y := fun y => by
      have h := congrFun (hblk (Q⁻¹ *ᵥ y))
      ext i
      have h2 := h (Sum.inr i)
      simp only [Function.comp_apply, Sum.elim_inr] at h2
      simp only [hπ, sub_mulVec, mulVec_sub, smul_mulVec, one_mulVec, mulVec_smul,
        mulVec_mulVec, hQA, Function.comp_apply, Pi.sub_apply, Pi.smul_apply]
      rw [← mulVec_mulVec, h2]
    have hπpow : ∀ k y, π (((A - μ • 1) ^ k) *ᵥ y) = ((T₂₂ - μ • 1) ^ k) *ᵥ π y := by
      intro k
      induction k with
      | zero => intro y; simp
      | succ k ih =>
        intro y
        rw [pow_succ', ← mulVec_mulVec, hπA, ih, mulVec_mulVec, ← pow_succ']
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hx
    have hk' : ((A - μ • 1) ^ k) *ᵥ x = 0 := by
      rw [← toLin'_apply, toLin'_pow, map_sub, map_smul, toLin'_one, ← hk]
      rfl
    have hunit : IsUnit ((T₂₂ - μ • 1) ^ k) := by
      refine IsUnit.pow k ?_
      have := (spectrum.mem_iff (R := K)).not.1 hμ2
      rw [not_not, Algebra.algebraMap_eq_smul_one] at this
      rw [← neg_sub, IsUnit.neg_iff]
      exact this
    have hπx : π x = 0 := by
      have h := hπpow k x
      rw [hk'] at h
      have h0 : π 0 = 0 := by ext; simp [hπ]
      rw [h0] at h
      obtain ⟨u, hu⟩ := hunit
      have h' := congrArg ((↑u⁻¹ : Matrix q q K) *ᵥ ·) h
      simp only [mulVec_mulVec, ← hu, Units.inv_mul, one_mulVec, mulVec_zero] at h'
      exact h'.symm
    refine ⟨(Q⁻¹ *ᵥ x) ∘ e.symm ∘ Sum.inl, ?_⟩
    simp only [hL, LinearMap.coe_mk, AddHom.coe_mk]
    have hwx : w ((Q⁻¹ *ᵥ x) ∘ e.symm ∘ Sum.inl) = Q⁻¹ *ᵥ x := by
      ext j
      simp only [hw, Function.comp_apply]
      rcases hj : e j with i | i
      · have h3 : e.symm (Sum.inl i) = j := by rw [← hj, Equiv.symm_apply_apply]
        simp [h3]
      · have := congrFun hπx i
        simp only [hπ, Function.comp_apply, Pi.zero_apply] at this
        rw [Sum.elim_inr, Pi.zero_apply, ← this, ← hj, Equiv.symm_apply_apply]
    rw [hwx, mulVec_mulVec, hQQ, one_mulVec]

end Block

end Matrix

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

section Aux

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- A diagonal matrix with entries of modulus at least `c` stretches every vector by `c`. -/
private theorem le_norm_diagonal_apply {d : m → 𝕜} {c : ℝ} (hc : 0 ≤ c) (hd : ∀ i, c ≤ ‖d i‖)
    (x : PiLp 2 fun _ : m => 𝕜) : c * ‖x‖ ≤ ‖lpCLM 2 (diagonal d) x‖ := by
  refine (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 ?_
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [lpCLM_apply, PiLp.toLp_apply, mulVec_diagonal, norm_mul, mul_pow]
  gcongr
  exact hd i

/-- An operator bounded below by `c > 0` is invertible, with inverse of norm at most `1 / c`. -/
private theorem lpOpNorm_inv_le_of_le_norm {Y : Matrix m m 𝕜} {c : ℝ} (hc : 0 < c)
    (hY : ∀ x, c * ‖x‖ ≤ ‖lpCLM 2 Y x‖) : IsUnit Y ∧ lpOpNorm 2 Y⁻¹ ≤ 1 / c := by
  have hinj : Function.Injective Y.mulVec := by
    intro u v huv
    have h := hY (WithLp.toLp 2 (u - v))
    rw [lpCLM_apply, WithLp.ofLp_toLp, mulVec_sub, huv, sub_self] at h
    have h0 : ‖WithLp.toLp 2 (u - v)‖ = 0 := by
      have := norm_nonneg (WithLp.toLp 2 (u - v))
      simp only [WithLp.toLp_zero, norm_zero] at h
      nlinarith
    rw [norm_eq_zero] at h0
    exact sub_eq_zero.1 (by simpa using congrArg (WithLp.ofLp) h0)
  have hU : IsUnit Y := (mulVec_injective_iff_isUnit).1 hinj
  refine ⟨hU, ?_⟩
  have hYY : Y * Y⁻¹ = 1 := mul_nonsing_inv Y ((isUnit_iff_isUnit_det Y).1 hU)
  rw [lpOpNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  have hx : lpCLM 2 Y (lpCLM 2 Y⁻¹ x) = x := by
    rw [← mul_apply_eq_comp, ← lpCLM_mul, hYY, lpCLM_one]; rfl
  have h := hY (lpCLM 2 Y⁻¹ x)
  rw [hx] at h
  rw [one_div_mul_eq_div, le_div_iff₀ hc, mul_comm]
  exact h

open scoped Matrix.Norms.L2Operator in
/-- Unitary conjugation preserves the `2`-norm. -/
private theorem lpOpNorm_two_unitary_conj {Q : Matrix m m 𝕜} (hQ : Q ∈ unitaryGroup m 𝕜)
    (X : Matrix m m 𝕜) : lpOpNorm 2 (Q * X * star Q) = lpOpNorm 2 X := by
  rw [lpOpNorm_two, lpOpNorm_two]
  exact l2_opNorm_unitary_mul_mul_unitary hQ X (Unitary.star_mem hQ)

end Aux

open scoped Matrix.Norms.Frobenius

/-- The scaling step of [golub2013matrix] Lemma 7.3.2: for a strictly upper triangular
`N : Matrix (Fin n) (Fin n) 𝕜`, `μ ≥ 0` and `Δ = diag((1+μ)^i)`,
`‖Δ N Δ⁻¹‖_F ≤ ‖N‖_F / (1 + μ)`: entry `(i, j)`, `i < j`, is scaled by `(1+μ)^{i-j} ≤ (1+μ)⁻¹`.
(`Δ⁻¹` is written out as the diagonal of the reciprocals.) -/
theorem frobenius_norm_diagonal_mul_mul_inv_le {N : Matrix (Fin n) (Fin n) 𝕜}
    (hN : ∀ i j, j ≤ i → N i j = 0) {μ : ℝ} (hμ : 0 ≤ μ) :
    ‖diagonal (fun i : Fin n => (((1 + μ) ^ (i : ℕ) : ℝ) : 𝕜)) * N *
        diagonal (fun i : Fin n => (((1 + μ) ^ (i : ℕ) : ℝ) : 𝕜)⁻¹)‖ ≤ ‖N‖ / (1 + μ) := by
  have h1 : (0 : ℝ) < 1 + μ := by linarith
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [div_pow, le_div_iff₀ (by positivity), frobenius_norm_sq_eq_sum_sq,
    frobenius_norm_sq_eq_sum_sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [mul_diagonal, diagonal_mul]
  by_cases hij : j ≤ i
  · rw [hN i j hij]; simp
  push Not at hij
  have hpow : (1 + μ) ^ (i : ℕ) * (1 + μ) ≤ (1 + μ) ^ (j : ℕ) := by
    rw [← pow_succ]
    exact pow_le_pow_right₀ (by linarith) (Nat.succ_le_of_lt hij)
  have hpos : ∀ k : ℕ, (0 : ℝ) < (1 + μ) ^ k := fun k => pow_pos h1 k
  simp only [norm_mul, norm_inv, RCLike.norm_ofReal, abs_of_pos (hpos _), mul_pow]
  have hr : ((1 + μ) ^ (i : ℕ)) ^ 2 * ((1 + μ) ^ (j : ℕ))⁻¹ ^ 2 * (1 + μ) ^ 2 ≤ 1 := by
    have hq : (1 + μ) ^ (i : ℕ) * (1 + μ) / (1 + μ) ^ (j : ℕ) ≤ 1 := by
      rw [div_le_one (hpos _)]; exact hpow
    calc ((1 + μ) ^ (i : ℕ)) ^ 2 * ((1 + μ) ^ (j : ℕ))⁻¹ ^ 2 * (1 + μ) ^ 2
        = ((1 + μ) ^ (i : ℕ) * (1 + μ) / (1 + μ) ^ (j : ℕ)) ^ 2 := by ring
      _ ≤ 1 := pow_le_one₀ (by positivity) hq
  nlinarith [sq_nonneg ‖N i j‖, hr]

/-- The common setting of [golub2013matrix] Lemma 7.3.2: the scaling `Δ = diag((1+μ)^i)` turns
the Schur form `T = D + N` into `Y = Δ T Δ⁻¹ = D + Δ N Δ⁻¹`. -/
private theorem schur_scaling {T : Matrix (Fin n) (Fin n) 𝕜} (hTu : T.IsUpperTriangular)
    {μ : ℝ} (hμ : 0 ≤ μ) :
    let d : Fin n → 𝕜 := fun i => (((1 + μ) ^ (i : ℕ) : ℝ) : 𝕜)
    diagonal d * diagonal (fun i => (d i)⁻¹) = 1 ∧
      diagonal (fun i => (d i)⁻¹) * diagonal d = 1 ∧
      lpOpNorm 2 (diagonal d) ≤ (1 + μ) ^ (n - 1) ∧
      lpOpNorm 2 (diagonal (fun i => (d i)⁻¹)) ≤ 1 ∧
      diagonal d * T * diagonal (fun i => (d i)⁻¹) =
        diagPart T + diagonal d * strictUpper T * diagonal (fun i => (d i)⁻¹) ∧
      lpOpNorm 2 (diagonal d * strictUpper T * diagonal (fun i => (d i)⁻¹)) ≤
        ‖strictUpper T‖ / (1 + μ) := by
  intro d
  have h1 : (1 : ℝ) ≤ 1 + μ := by linarith
  have hd0 : ∀ i, d i ≠ 0 := fun i => RCLike.ofReal_ne_zero.2 (pow_pos (by linarith) _).ne'
  have hnd : ∀ i, ‖d i‖ = (1 + μ) ^ (i : ℕ) := fun i => by
    simp only [d, RCLike.norm_ofReal,
      abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + μ) _)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hd0 i)
  · rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact inv_mul_cancel₀ (hd0 i)
  · refine lpOpNorm_diagonal_le 2 (by positivity) fun i => ?_
    rw [hnd]
    exact pow_le_pow_right₀ h1 (by omega)
  · refine lpOpNorm_diagonal_le 2 zero_le_one fun i => ?_
    rw [norm_inv, hnd]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ h1)
  · have hT : T = diagPart T + strictUpper T := by
      have h := diagPart_add_strictLower_add_strictUpper T
      have hl : strictLower T = 0 := by
        ext i j
        rw [strictLower_apply]
        split_ifs with h
        · exact hTu h
        · rfl
      rw [hl, add_zero] at h
      exact h.symm
    conv_lhs => rw [hT]
    rw [Matrix.mul_add, Matrix.add_mul, diagPart, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 2
    funext i
    field_simp [hd0 i]
  · refine (l2_opNorm_le_frobenius_norm _).trans ?_
    refine frobenius_norm_diagonal_mul_mul_inv_le (fun i j hji => ?_) hμ
    simp [strictUpper_apply, not_lt.2 hji]

/-- **Powers from a Schur form** ([golub2013matrix] Lemma 7.3.2, (7.3.15)): if `Q` is unitary,
`Qᴴ A Q = T` is upper triangular with strictly upper part `N` and `μ ≥ 0`, then
`‖A^k‖₂ ≤ (1 + μ)^{n-1} (max_i |t_ii| + ‖N‖_F / (1 + μ))^k` for every `k`.
`A^k = Q Δ⁻¹ (D + Δ N Δ⁻¹)^k Δ Qᴴ` with `Δ = diag((1+μ)^i)`, `‖Δ‖₂ ≤ (1+μ)^{n-1}`,
`‖Δ⁻¹‖₂ ≤ 1`, `‖D‖₂ = max |t_ii|` and `‖Δ N Δ⁻¹‖₂ ≤ ‖Δ N Δ⁻¹‖_F ≤ ‖N‖_F/(1+μ)`
(`Matrix.frobenius_norm_diagonal_mul_mul_inv_le`). -/
theorem l2_opNorm_pow_le_of_schur {A Q T : Matrix (Fin n) (Fin n) 𝕜}
    (hQ : Q ∈ unitaryGroup (Fin n) 𝕜) (hT : star Q * A * Q = T) (hTu : T.IsUpperTriangular)
    {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) :
    lpOpNorm 2 (A ^ k) ≤
      (1 + μ) ^ (n - 1) * ((⨆ i, ‖T i i‖) + ‖strictUpper T‖ / (1 + μ)) ^ k := by
  have h1 : (1 : ℝ) ≤ 1 + μ := by linarith
  have hsup0 : 0 ≤ ⨆ i, ‖T i i‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  rcases k with _ | k
  · rw [pow_zero, pow_zero, mul_one]
    refine le_trans ?_ (one_le_pow₀ h1)
    rw [lpOpNorm, lpCLM_one]; exact ContinuousLinearMap.norm_id_le
  obtain ⟨hΔ, hΔ', hΔn, hΔin, hY, hM⟩ := schur_scaling hTu hμ
  set d : Fin n → 𝕜 := fun i => (((1 + μ) ^ (i : ℕ) : ℝ) : 𝕜)
  set Δ := diagonal d
  set Δi := diagonal fun i => (d i)⁻¹
  set Y := Δ * T * Δi with hYdef
  have hQQ : Q * star Q = 1 := mem_unitaryGroup_iff.1 hQ
  have hQQ' : star Q * Q = 1 := mem_unitaryGroup_iff'.1 hQ
  have hA : A = Q * T * star Q := by
    rw [← hT]; simp only [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
    rw [Matrix.mul_assoc, hQQ, Matrix.mul_one]
  have hTY : T = Δi * Y * Δ := by
    simp only [hYdef, ← Matrix.mul_assoc, hΔ', Matrix.one_mul]
    rw [Matrix.mul_assoc, hΔ', Matrix.mul_one]
  have hAk : A ^ (k + 1) = Q * (Δi * Y ^ (k + 1) * Δ) * star Q := by
    rw [hA, conj_pow_of_mul_eq_one hQQ', hTY, conj_pow_of_mul_eq_one hΔ]
  rw [hAk, lpOpNorm_two_unitary_conj hQ]
  have hYn : lpOpNorm 2 Y ≤ (⨆ i, ‖T i i‖) + ‖strictUpper T‖ / (1 + μ) := by
    rw [hY]
    refine (lpOpNorm_add_le 2 _ _).trans (add_le_add ?_ hM)
    refine lpOpNorm_diagonal_le 2 hsup0 fun i => ?_
    exact le_ciSup (Finite.bddAbove_range fun i => ‖T i i‖) i
  calc lpOpNorm 2 (Δi * Y ^ (k + 1) * Δ)
      ≤ lpOpNorm 2 Δi * lpOpNorm 2 (Y ^ (k + 1)) * lpOpNorm 2 Δ :=
        (lpOpNorm_mul_le 2 _ _).trans (mul_le_mul_of_nonneg_right (lpOpNorm_mul_le 2 _ _)
          (lpOpNorm_nonneg _ _))
    _ ≤ 1 * ((⨆ i, ‖T i i‖) + ‖strictUpper T‖ / (1 + μ)) ^ (k + 1) * (1 + μ) ^ (n - 1) := by
        have hYk := (lpOpNorm_pow_le 2 Y (k + 1)).trans
          (pow_le_pow_left₀ (lpOpNorm_nonneg _ _) hYn (k + 1))
        have hX0 : 0 ≤ (⨆ i, ‖T i i‖) + ‖strictUpper T‖ / (1 + μ) := by positivity
        exact mul_le_mul (mul_le_mul hΔin hYk (lpOpNorm_nonneg _ _) zero_le_one) hΔn
          (lpOpNorm_nonneg _ _) (mul_nonneg zero_le_one (pow_nonneg hX0 _))
    _ = _ := by ring

/-- **Powers of the inverse from a Schur form** ([golub2013matrix] Lemma 7.3.2, (7.3.16)): in the
setting of `Matrix.l2_opNorm_pow_le_of_schur`, if `(1 + μ) m > ‖N‖_F` for `m = min_i |t_ii|`,
then `‖A⁻¹^k‖₂ ≤ (1 + μ)^{n-1} (1 / (m - ‖N‖_F/(1+μ)))^k`. The hypothesis already makes `A`
nonsingular: `Y = D + Δ N Δ⁻¹` satisfies `‖Y x‖ ≥ (m - ‖Δ N Δ⁻¹‖₂) ‖x‖` (the Neumann-series bound
`‖(1 + X)⁻¹‖ ≤ 1/(1 - ‖X‖)` of the book, in lower-bound form). The book's last display writes
`|μ|` for `|λ_min|`. -/
theorem l2_opNorm_inv_pow_le_of_schur {A Q T : Matrix (Fin n) (Fin n) 𝕜}
    (hQ : Q ∈ unitaryGroup (Fin n) 𝕜) (hT : star Q * A * Q = T) (hTu : T.IsUpperTriangular)
    {μ : ℝ} (hμ : 0 ≤ μ) (hm : ‖strictUpper T‖ < (1 + μ) * ⨅ i, ‖T i i‖) (k : ℕ) :
    lpOpNorm 2 (A⁻¹ ^ k) ≤
      (1 + μ) ^ (n - 1) * (1 / ((⨅ i, ‖T i i‖) - ‖strictUpper T‖ / (1 + μ))) ^ k := by
  have h1 : (1 : ℝ) ≤ 1 + μ := by linarith
  set m := ⨅ i, ‖T i i‖ with hmdef
  have hm0 : 0 ≤ m := Real.iInf_nonneg fun _ => norm_nonneg _
  have hc : 0 < m - ‖strictUpper T‖ / (1 + μ) := by
    rw [sub_pos, div_lt_iff₀ (by linarith)]; linarith
  rcases k with _ | k
  · rw [pow_zero, pow_zero, mul_one]
    refine le_trans ?_ (one_le_pow₀ h1)
    rw [lpOpNorm, lpCLM_one]; exact ContinuousLinearMap.norm_id_le
  obtain ⟨hΔ, hΔ', hΔn, hΔin, hY, hM⟩ := schur_scaling hTu hμ
  set d : Fin n → 𝕜 := fun i => (((1 + μ) ^ (i : ℕ) : ℝ) : 𝕜)
  set Δ := diagonal d
  set Δi := diagonal fun i => (d i)⁻¹
  set Y := Δ * T * Δi with hYdef
  set M := Δ * strictUpper T * Δi
  have hQQ : Q * star Q = 1 := mem_unitaryGroup_iff.1 hQ
  have hQQ' : star Q * Q = 1 := mem_unitaryGroup_iff'.1 hQ
  have hA : A = Q * T * star Q := by
    rw [← hT]; simp only [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
    rw [Matrix.mul_assoc, hQQ, Matrix.mul_one]
  have hTY : T = Δi * Y * Δ := by
    simp only [hYdef, ← Matrix.mul_assoc, hΔ', Matrix.one_mul]
    rw [Matrix.mul_assoc, hΔ', Matrix.mul_one]
  -- `Y` is bounded below
  have hlow : ∀ x, (m - lpOpNorm 2 M) * ‖x‖ ≤ ‖lpCLM 2 Y x‖ := by
    intro x
    have hD := le_norm_diagonal_apply (d := T.diag) hm0
      (fun i => ciInf_le (Finite.bddBelow_range fun i => ‖T i i‖) i) x
    have hMx : ‖lpCLM 2 M x‖ ≤ lpOpNorm 2 M * ‖x‖ := (lpCLM 2 M).le_opNorm x
    have hsplit : lpCLM 2 Y x = lpCLM 2 (diagonal T.diag) x + lpCLM 2 M x := by
      rw [hY, lpCLM_add]; rfl
    rw [hsplit]
    have h2 : ‖lpCLM 2 (diagonal T.diag) x‖ ≤
        ‖lpCLM 2 (diagonal T.diag) x + lpCLM 2 M x‖ + ‖lpCLM 2 M x‖ := by
      simpa using norm_sub_le (lpCLM 2 (diagonal T.diag) x + lpCLM 2 M x) (lpCLM 2 M x)
    rw [sub_mul]
    linarith
  have hcM : m - ‖strictUpper T‖ / (1 + μ) ≤ m - lpOpNorm 2 M := by linarith
  obtain ⟨hYu, hYinv⟩ := lpOpNorm_inv_le_of_le_norm (hc.trans_le hcM) hlow
  have hYinv' : lpOpNorm 2 Y⁻¹ ≤ 1 / (m - ‖strictUpper T‖ / (1 + μ)) :=
    hYinv.trans (one_div_le_one_div_of_le hc hcM)
  -- `A⁻¹ = Q Δ⁻¹ Y⁻¹ Δ Qᴴ`
  have hΔinv : Δ⁻¹ = Δi := inv_eq_right_inv hΔ
  have hΔiinv : Δi⁻¹ = Δ := inv_eq_right_inv hΔ'
  have hQinv : Q⁻¹ = star Q := inv_eq_right_inv hQQ
  have hsQinv : (star Q)⁻¹ = Q := inv_eq_right_inv hQQ'
  have hAinv : A⁻¹ = Q * (Δi * Y⁻¹ * Δ) * star Q := by
    rw [hA, hTY, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.mul_inv_rev, hsQinv, hQinv, hΔinv, hΔiinv]
    simp only [Matrix.mul_assoc]
  rw [hAinv, conj_pow_of_mul_eq_one hQQ', lpOpNorm_two_unitary_conj hQ,
    conj_pow_of_mul_eq_one hΔ]
  calc lpOpNorm 2 (Δi * Y⁻¹ ^ (k + 1) * Δ)
      ≤ lpOpNorm 2 Δi * lpOpNorm 2 (Y⁻¹ ^ (k + 1)) * lpOpNorm 2 Δ :=
        (lpOpNorm_mul_le 2 _ _).trans (mul_le_mul_of_nonneg_right (lpOpNorm_mul_le 2 _ _)
          (lpOpNorm_nonneg _ _))
    _ ≤ 1 * (1 / (m - ‖strictUpper T‖ / (1 + μ))) ^ (k + 1) * (1 + μ) ^ (n - 1) := by
        have hYk := (lpOpNorm_pow_le 2 Y⁻¹ (k + 1)).trans
          (pow_le_pow_left₀ (lpOpNorm_nonneg _ _) hYinv' (k + 1))
        exact mul_le_mul (mul_le_mul hΔin hYk (lpOpNorm_nonneg _ _) zero_le_one) hΔn
          (lpOpNorm_nonneg _ _) (mul_nonneg zero_le_one (pow_nonneg (one_div_pos.2 hc).le _))
    _ = _ := by ring

end Matrix

namespace Matrix

open scoped Matrix.Norms.Frobenius

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-- **Stewart's perturbation theorem for invariant subspaces** ([golub2013matrix] Theorem 7.2.4,
after G. W. Stewart, SIAM Rev. 15 (1973), Theorem 4.11), in Schur coordinates: for
`T = fromBlocks T₁₁ T₁₂ 0 T₂₂`, a perturbation `E` with `s = sep T₁₁ T₂₂ > 0` and
`‖E‖_F (1 + 5 ‖T₁₂‖_F / s) ≤ s / 5`, there is `P` with `‖P‖_F ≤ 4 ‖E₂₁‖_F / s` such that the
column space of `[I; P]` is `(T + E)`-invariant:
`(T + E) [I; P] = [I; P] (T₁₁ + E₁₁ + (T₁₂ + E₁₂) P)`.
The second block row is the Riccati equation `P A₁₁ - A₂₂ P + P A₁₂ P = E₂₁` (`Aᵢⱼ` the blocks of
`T + E`), solved by Stewart's quadratic-equation lemma
(`ContinuousLinearEquiv.exists_apply_add_eq_of_quadratic`) with `L = -sylvesterMap A₂₂ A₁₁`,
`‖L⁻¹‖ ≤ 1 / sep A₁₁ A₂₂` (`Matrix.sep_comm`), `sep A₁₁ A₂₂ ≥ s - 2‖E‖_F`
(`Matrix.sep_sub_le_sep_add`), `γ = ‖E₂₁‖_F` and `η = ‖A₁₂‖_F`: then `δ ≥ 3s/5` and
`4γη ≤ 4s²/25 < δ²`, and the solution has `‖P‖_F ≤ 2γ/δ ≤ (10/3) γ/s`. -/
theorem exists_invariant_graph_of_sep {T₁₁ : Matrix m m 𝕜} {T₁₂ : Matrix m n 𝕜}
    {T₂₂ : Matrix n n 𝕜} {E : Matrix (m ⊕ n) (m ⊕ n) 𝕜} (hs : 0 < sep T₁₁ T₂₂)
    (hE : ‖E‖ * (1 + 5 * ‖T₁₂‖ / sep T₁₁ T₂₂) ≤ sep T₁₁ T₂₂ / 5) :
    ∃ P : Matrix n m 𝕜, ‖P‖ ≤ 4 * ‖E.toBlocks₂₁‖ / sep T₁₁ T₂₂ ∧
      (fromBlocks T₁₁ T₁₂ 0 T₂₂ + E) * fromRows 1 P =
        fromRows 1 P * (T₁₁ + E.toBlocks₁₁ + (T₁₂ + E.toBlocks₁₂) * P) := by
  set s := sep T₁₁ T₂₂ with hsdef
  set ε := ‖E‖ with hεdef
  set t := ‖T₁₂‖ with htdef
  set A₁₁ := T₁₁ + E.toBlocks₁₁ with hA11
  set A₁₂ := T₁₂ + E.toBlocks₁₂ with hA12
  set A₂₂ := T₂₂ + E.toBlocks₂₂ with hA22
  set g := E.toBlocks₂₁
  have hε0 : 0 ≤ ε := norm_nonneg _
  have ht0 : 0 ≤ t := norm_nonneg _
  have hb11 : ‖E.toBlocks₁₁‖ ≤ ε :=
    frobenius_norm_submatrix_le E Sum.inl_injective Sum.inl_injective
  have hb12 : ‖E.toBlocks₁₂‖ ≤ ε :=
    frobenius_norm_submatrix_le E Sum.inl_injective Sum.inr_injective
  have hb21 : ‖g‖ ≤ ε :=
    frobenius_norm_submatrix_le E Sum.inr_injective Sum.inl_injective
  have hb22 : ‖E.toBlocks₂₂‖ ≤ ε :=
    frobenius_norm_submatrix_le E Sum.inr_injective Sum.inr_injective
  -- the arithmetic of the hypothesis
  have hE' : 5 * ε * s + 25 * ε * t ≤ s ^ 2 := by
    have h := hE
    rw [mul_add, mul_one, mul_div_assoc', le_div_iff₀ (by norm_num : (0 : ℝ) < 5)] at h
    have h2 : ε * (5 * t) / s * 5 = 25 * ε * t / s := by ring
    rw [add_mul, h2] at h
    have h3 : 25 * ε * t / s * s = 25 * ε * t := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right h hs.le]
  have hεs : ε ≤ s / 5 := by nlinarith [mul_nonneg hε0 ht0]
  -- the separation of the perturbed blocks
  set δ := sep A₁₁ A₂₂ with hδdef
  have hδ : 3 * s / 5 ≤ δ := by
    have := sep_sub_le_sep_add T₁₁ E.toBlocks₁₁ T₂₂ E.toBlocks₂₂
    linarith
  have hδ0 : 0 < δ := by linarith
  have hsep' : sep A₂₂ A₁₁ = δ := sep_comm _ _
  have hlow : ∀ X : Matrix n m 𝕜, δ * ‖X‖ ≤ ‖X * A₁₁ - A₂₂ * X‖ := fun X => by
    have h := sep_mul_norm_le (A := A₂₂) (B := A₁₁) X
    rwa [hsep', norm_sub_rev] at h
  -- the linear part `L X = X A₁₁ - A₂₂ X`
  set L₀ : Matrix n m 𝕜 →ₗ[𝕜] Matrix n m 𝕜 := -sylvesterMap A₂₂ A₁₁ with hL₀
  have hL₀apply : ∀ X, L₀ X = X * A₁₁ - A₂₂ * X := fun X => by
    rw [hL₀, LinearMap.neg_apply, sylvesterMap_apply, neg_sub]
  have hinj : Function.Injective L₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    have h := hlow X
    rw [← hL₀apply, hX, norm_zero] at h
    exact norm_eq_zero.1 (le_antisymm (nonpos_of_mul_nonpos_right h hδ0) (norm_nonneg _))
  -- the quadratic part `φ X = X A₁₂ X`
  set η := ‖A₁₂‖ with hηdef
  have hη : η ≤ t + ε := (norm_add_le _ _).trans (by linarith)
  have hφ : ∀ X Y : Matrix n m 𝕜, ‖X * A₁₂ * X - Y * A₁₂ * Y‖ ≤ η * (‖X‖ + ‖Y‖) * ‖X - Y‖ := by
    intro X Y
    have heq : X * A₁₂ * X - Y * A₁₂ * Y = (X - Y) * A₁₂ * X + Y * A₁₂ * (X - Y) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub]; abel
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(X - Y) * A₁₂ * X‖ ≤ ‖X - Y‖ * η * ‖X‖ :=
      (frobenius_norm_mul _ _).trans (by gcongr; exact frobenius_norm_mul _ _)
    have h2 : ‖Y * A₁₂ * (X - Y)‖ ≤ ‖Y‖ * η * ‖X - Y‖ :=
      (frobenius_norm_mul _ _).trans (by gcongr; exact frobenius_norm_mul _ _)
    nlinarith
  have hkey : 4 * ‖g‖ * η < δ ^ 2 := by
    have h1 : ‖g‖ * η ≤ ε * (t + ε) :=
      mul_le_mul hb21 hη (norm_nonneg _) hε0
    have h2 : ε * (t + ε) ≤ s ^ 2 / 25 := by nlinarith
    have h3 : (3 * s / 5) ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (by positivity) hδ 2
    nlinarith
  obtain ⟨P, hP, hPn⟩ := L₀.exists_apply_add_eq_of_quadratic_of_le_norm hδ0
    (fun X => (hL₀apply X).symm ▸ hlow X) le_rfl (φ := fun X => X * A₁₂ * X) (by simp) hφ hkey
  refine ⟨P, ?_, ?_⟩
  · calc ‖P‖ ≤ 2 * ‖g‖ / δ := hPn
      _ ≤ 2 * ‖g‖ / (3 * s / 5) := by gcongr
      _ ≤ 4 * ‖g‖ / s := by
          rw [div_le_div_iff₀ (by positivity) hs]; nlinarith [norm_nonneg g]
  · have hP' : P * A₁₁ - A₂₂ * P + P * A₁₂ * P = g := by
      rw [← hL₀apply]; exact hP
    conv_lhs => rw [← fromBlocks_toBlocks E, fromBlocks_add, fromBlocks_mul_fromRows]
    rw [fromRows_mul]
    congr 1
    · simp only [hA11, hA12, Matrix.mul_one, Matrix.one_mul, Matrix.mul_add, Matrix.add_mul]
    · simp only [zero_add, Matrix.mul_one]
      have hg : E.toBlocks₂₁ = P * A₁₁ - A₂₂ * P + P * A₁₂ * P := hP'.symm
      rw [hg, ← hA22, Matrix.mul_assoc P A₁₂ P]
      simp only [hA11, Matrix.mul_add]
      abel

end Matrix

namespace Submodule

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **The gap is invariant under isometries**: `gap (e K) (e L) = gap K L` for a linear isometry
equivalence `e`, since `P_{eK} = e P_K e⁻¹` (`Submodule.starProjection_map_apply`). With unitary
matrices this is the unitary invariance of [golub2013matrix]'s `dist` (§2.5.3). -/
theorem gap_map_linearIsometryEquiv (e : E ≃ₗᵢ[𝕜] F) (K L : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] :
    (K.map (e.toLinearEquiv : E →ₗ[𝕜] F)).gap (L.map (e.toLinearEquiv : E →ₗ[𝕜] F)) =
      K.gap L := by
  have h : (K.map (e.toLinearEquiv : E →ₗ[𝕜] F)).starProjection -
      (L.map (e.toLinearEquiv : E →ₗ[𝕜] F)).starProjection =
      (e.toLinearIsometry.toContinuousLinearMap).comp
        ((K.starProjection - L.starProjection).comp
          (e.symm.toLinearIsometry.toContinuousLinearMap)) := by
    ext x
    simp [starProjection_map_apply]
  rw [gap, gap, h, LinearIsometry.norm_toContinuousLinearMap_comp]
  exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ e.symm

/-- **A subspace close to `K` is a graph over `K`**: if `gap K S < 1` and `S` has the dimension of
`K` (finite), then `S = K.graph X` for some `X : K →L[𝕜] Kᗮ`. The restricted projection
`P_K|_S` is injective (`Submodule.eq_zero_of_starProjection_eq_zero_of_gap_lt_one`), hence
bijective, and `X = P_{Kᗮ}|_S ∘ (P_K|_S)⁻¹`. -/
theorem exists_eq_graph_of_gap_lt_one [FiniteDimensional 𝕜 E] (K S : Submodule 𝕜 E)
    (hdim : Module.finrank 𝕜 S = Module.finrank 𝕜 K) (h : K.gap S < 1) :
    ∃ X : K →L[𝕜] Kᗮ, S = K.graph X := by
  set φ := K.orthogonalProjectionRestrict S with hφ
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : K.starProjection (x : E) = 0 := by
      rw [← coe_orthogonalProjectionRestrict_apply, ← hφ, hx, ZeroMemClass.coe_zero]
    exact Subtype.ext (K.eq_zero_of_starProjection_eq_zero_of_gap_lt_one S h x.2 h0)
  have hbij : Function.Bijective φ :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩
  set ψ := LinearEquiv.ofBijective φ hbij with hψ
  set X : K →ₗ[𝕜] Kᗮ := Kᗮ.orthogonalProjectionRestrict S ∘ₗ (ψ.symm : K →ₗ[𝕜] S) with hX
  refine ⟨LinearMap.toContinuousLinearMap X, ?_⟩
  have hdec : ∀ s : S, (φ s : E) + ((Kᗮ.orthogonalProjectionRestrict S s : Kᗮ) : E) = s :=
    fun s => by
      rw [coe_orthogonalProjectionRestrict_apply, coe_orthogonalProjectionRestrict_apply,
        starProjection_orthogonal]
      simp
  ext y
  constructor
  · intro hy
    refine ⟨φ ⟨y, hy⟩, ?_⟩
    have hs : ψ.symm (φ ⟨y, hy⟩) = ⟨y, hy⟩ := ψ.symm_apply_apply ⟨y, hy⟩
    simp only [LinearMap.add_apply, Submodule.subtype_apply, LinearMap.comp_apply,
      ContinuousLinearMap.coe_coe, LinearMap.coe_toContinuousLinearMap', hX, LinearEquiv.coe_coe]
    rw [hs, hdec]
  · rintro ⟨u, rfl⟩
    have hu : φ (ψ.symm u) = u := ψ.apply_symm_apply u
    simp only [LinearMap.add_apply, Submodule.subtype_apply, LinearMap.comp_apply,
      ContinuousLinearMap.coe_coe, LinearMap.coe_toContinuousLinearMap', hX, LinearEquiv.coe_coe]
    have := hdec (ψ.symm u)
    rw [hu] at this
    rw [this]
    exact (ψ.symm u).2

/-- The norm of `X` is read off the gap of its graph: `‖X‖ = d / √(1 - d²)` for
`d = gap K (graph X) < 1` (inverting `Submodule.gap_graph`). -/
theorem norm_eq_gap_graph_div (K : Submodule 𝕜 E) [FiniteDimensional 𝕜 K] (X : K →L[𝕜] Kᗮ) :
    ‖X‖ = K.gap (K.graph X) / Real.sqrt (1 - K.gap (K.graph X) ^ 2) := by
  rw [gap_graph]
  set t := ‖X‖
  have hs : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hs2 : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  have h1 : 1 - (t / Real.sqrt (1 + t ^ 2)) ^ 2 = (1 / Real.sqrt (1 + t ^ 2)) ^ 2 := by
    rw [div_pow, div_pow, hs2]; field_simp; ring
  rw [h1, Real.sqrt_sq (by positivity)]
  field_simp

end Submodule

namespace Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Transport of a graph subspace by powers** (the coordinate-free core of [golub2013matrix]
Theorem 7.3.1's appendix proof and of Theorem 8.2.2): let `K`, `W` be `A`-invariant, `A` bijective
on `K` (`A₁ = A|_K`), `A₂ = A|_W`, and `X : K →ₗ[𝕜] W`. The graph `{u + X u | u ∈ K}` is carried by
`A^k` onto the graph of `A₂^k X A₁^{-k}`: `A^k (u + X u) = A₁^k u + A₂^k X u`, and `u ↦ A₁^k u` is a
bijection of `K`. Pure algebra: no complement, inner product or dimension is used. -/
theorem subspaceIterate_graph {A : Module.End 𝕜 E} {K W : Submodule 𝕜 E}
    (hK : ∀ x ∈ K, A x ∈ K) (hW : ∀ x ∈ W, A x ∈ W) (hA₁ : Function.Bijective (A.restrict hK))
    (X : K →ₗ[𝕜] W) (k : ℕ) :
    subspaceIterate A (LinearMap.range (K.subtype + W.subtype ∘ₗ X)) k =
      LinearMap.range (K.subtype + W.subtype ∘ₗ (((A.restrict hW) ^ k) ∘ₗ X ∘ₗ
        (((LinearEquiv.ofBijective _ hA₁).symm : K →ₗ[𝕜] K) ^ k))) := by
  set A₁ := LinearEquiv.ofBijective _ hA₁ with hA₁def
  set B : Module.End 𝕜 K := (A₁ : K →ₗ[𝕜] K) with hB
  set C : Module.End 𝕜 K := (A₁.symm : K →ₗ[𝕜] K) with hC
  have hBC : B * C = 1 := by
    ext u; simp [hB, hC]
  have hCB : C * B = 1 := by
    ext u; simp [hB, hC]
  have hcomm : Commute B C := hBC.trans hCB.symm
  have hBCk : B ^ k * C ^ k = 1 := by rw [← hcomm.mul_pow, hBC, one_pow]
  have hCBk : C ^ k * B ^ k = 1 := by rw [← hcomm.symm.mul_pow, hCB, one_pow]
  have hpowK : ∀ u : K, (A ^ k) (u : E) = ((B ^ k) u : E) := fun u => by
    have hB' : B = A.restrict hK := by ext; simp [hB, hA₁def]
    rw [hB', Module.End.pow_restrict k hK]
    rfl
  have hpowW : ∀ w : W, (A ^ k) (w : E) = (((A.restrict hW) ^ k) w : E) := fun w => by
    rw [Module.End.pow_restrict k hW]
    rfl
  ext y
  rw [mem_subspaceIterate]
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    refine ⟨(B ^ k) u, ?_⟩
    have hu : (C ^ k) ((B ^ k) u) = u := by rw [← Module.End.mul_apply, hCBk]; rfl
    simp only [LinearMap.add_apply, Submodule.subtype_apply, LinearMap.comp_apply, map_add,
      hpowK, hpowW, hu]
  · rintro ⟨u, rfl⟩
    refine ⟨_, ⟨(C ^ k) u, rfl⟩, ?_⟩
    have hu : (B ^ k) ((C ^ k) u) = u := by rw [← Module.End.mul_apply, hBCk]; rfl
    simp only [LinearMap.add_apply, Submodule.subtype_apply, LinearMap.comp_apply, map_add,
      hpowK, hpowW, hu]

end Krylov

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E}

/-- **Subspace iteration toward an invariant subspace of a symmetric operator, explicit
constant**: let `D` be `A`-invariant with `‖A u‖ ≥ ρ ‖u‖` on `D` (`ρ > 0`) and `‖A w‖ ≤ r ‖w‖` on
`Dᗮ` (`r ≥ 0`), and `S` of the dimension of `D` with `d₀ = gap D S < 1`. Then
`gap D (A^k S) ≤ (r / ρ)^k d₀ / √(1 - d₀²)`. `Dᗮ` is invariant (symmetry), `S` is the graph of
some `X : D → Dᗮ` with `‖X‖ = d₀ / √(1 - d₀²)` (`Submodule.exists_eq_graph_of_gap_lt_one`,
`Submodule.norm_eq_gap_graph_div`), `A^k S` is the graph of `A₂^k X A₁^{-k}`
(`Krylov.subspaceIterate_graph`), and `gap ≤ ‖X_k‖` (`Submodule.gap_graph`). -/
theorem gap_subspaceIterate_le_of_invariant (hA : A.IsSymmetric) {D S : Submodule 𝕜 E}
    (hD : ∀ x ∈ D, A x ∈ D) {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 ≤ r)
    (hlow : ∀ u ∈ D, ρ * ‖u‖ ≤ ‖A u‖) (hup : ∀ w ∈ Dᗮ, ‖A w‖ ≤ r * ‖w‖)
    (hdim : Module.finrank 𝕜 S = Module.finrank 𝕜 D) (h0 : D.gap S < 1) (k : ℕ) :
    D.gap (Krylov.subspaceIterate A S k) ≤
      (r / ρ) ^ k * (D.gap S / Real.sqrt (1 - D.gap S ^ 2)) := by
  have hDo : ∀ x ∈ Dᗮ, A x ∈ Dᗮ := fun x hx => by
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro u hu
    rw [← hA u x]
    exact hx _ (hD u hu)
  obtain ⟨X, hX⟩ := D.exists_eq_graph_of_gap_lt_one S hdim h0
  have hnX : ‖X‖ = D.gap S / Real.sqrt (1 - D.gap S ^ 2) := by
    rw [D.gap_congr S hX]; exact D.norm_eq_gap_graph_div X
  rw [← hnX]
  -- `A` is bijective on `D`
  have hinj : Function.Injective (A.restrict hD) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h := hlow u u.2
    have hAu : A u = 0 := by
      simpa using congrArg Subtype.val hu
    rw [hAu, norm_zero] at h
    exact Subtype.ext (norm_eq_zero.1 (le_antisymm
      (nonpos_of_mul_nonpos_right h hρ |>.trans_eq rfl) (norm_nonneg _)))
  have hbij : Function.Bijective (A.restrict hD) :=
    ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  set A₁ := LinearEquiv.ofBijective _ hbij with hA₁
  -- the power bounds
  have hlowk : ∀ j (u : E), u ∈ D → ρ ^ j * ‖u‖ ≤ ‖(A ^ j) u‖ := by
    intro j
    induction j with
    | zero => intro u _; simp
    | succ j ih =>
      intro u hu
      rw [show A ^ (j + 1) = A * A ^ j from pow_succ' A j, Module.End.mul_apply]
      have hmem : (A ^ j) u ∈ D := Module.End.pow_apply_mem_of_forall_mem j hD u hu
      calc ρ ^ (j + 1) * ‖u‖ = ρ * (ρ ^ j * ‖u‖) := by ring
        _ ≤ ρ * ‖(A ^ j) u‖ := by gcongr; exact ih u hu
        _ ≤ ‖A ((A ^ j) u)‖ := hlow _ hmem
  have hupk : ∀ j (w : E), w ∈ Dᗮ → ‖(A ^ j) w‖ ≤ r ^ j * ‖w‖ := by
    intro j
    induction j with
    | zero => intro w _; simp
    | succ j ih =>
      intro w hw
      rw [show A ^ (j + 1) = A * A ^ j from pow_succ' A j, Module.End.mul_apply]
      have hmem : (A ^ j) w ∈ Dᗮ := Module.End.pow_apply_mem_of_forall_mem j hDo w hw
      calc ‖A ((A ^ j) w)‖ ≤ r * ‖(A ^ j) w‖ := hup _ hmem
        _ ≤ r * (r ^ j * ‖w‖) := by gcongr; exact ih w hw
        _ = r ^ (j + 1) * ‖w‖ := by ring
  -- the iterated graph
  set Xk : D →ₗ[𝕜] Dᗮ := ((A.restrict hDo) ^ k) ∘ₗ (X : D →ₗ[𝕜] Dᗮ) ∘ₗ
    ((A₁.symm : D →ₗ[𝕜] D) ^ k) with hXk
  have hiter : Krylov.subspaceIterate A S k = D.graph (LinearMap.toContinuousLinearMap Xk) := by
    rw [hX]
    exact Krylov.subspaceIterate_graph hD hDo hbij (X : D →ₗ[𝕜] Dᗮ) k
  rw [D.gap_congr _ hiter, Submodule.gap_graph]
  set Y := LinearMap.toContinuousLinearMap Xk
  have hY : ‖Y‖ ≤ (r / ρ) ^ k * ‖X‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
    -- `v = A₁^{-k} u`
    set v := ((A₁.symm : D →ₗ[𝕜] D) ^ k) u with hv
    have hAv : ((A ^ k) (v : E)) = u := by
      have h1 : ((A.restrict hD) ^ k) v = u := by
        have hBC : (A.restrict hD : Module.End 𝕜 D) * (A₁.symm : D →ₗ[𝕜] D) = 1 := by
          ext x; simp [hA₁]
        have hCB : (A₁.symm : D →ₗ[𝕜] D) * (A.restrict hD : Module.End 𝕜 D) = 1 := by
          ext x; simp [hA₁]
        have hcomm : Commute (A.restrict hD : Module.End 𝕜 D) (A₁.symm : D →ₗ[𝕜] D) :=
          hBC.trans hCB.symm
        rw [hv, ← Module.End.mul_apply, ← hcomm.mul_pow, hBC, one_pow]
        rfl
      rw [← h1, Module.End.pow_restrict k hD]
      rfl
    have hvn : ρ ^ k * ‖(v : E)‖ ≤ ‖(u : E)‖ := by
      rw [← hAv]; exact hlowk k v v.2
    have hYu : (Y u : E) = (A ^ k) ((X v : Dᗮ) : E) := by
      simp only [Y, hXk, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
        ContinuousLinearMap.coe_coe]
      rw [Module.End.pow_restrict k hDo]
      rfl
    rw [← Submodule.norm_coe, hYu, ← Submodule.norm_coe u]
    have hρk : 0 < ρ ^ k := pow_pos hρ k
    calc ‖(A ^ k) ((X v : Dᗮ) : E)‖ ≤ r ^ k * ‖((X v : Dᗮ) : E)‖ := hupk k _ (X v).2
      _ ≤ r ^ k * (‖X‖ * ‖(v : E)‖) := by
          gcongr; rw [Submodule.norm_coe, Submodule.norm_coe]; exact X.le_opNorm v
      _ ≤ r ^ k * (‖X‖ * (‖(u : E)‖ / ρ ^ k)) := by
          gcongr; rw [le_div_iff₀ hρk, mul_comm]; exact hvn
      _ = (r / ρ) ^ k * ‖X‖ * ‖(u : E)‖ := by rw [div_pow]; field_simp
  have hs : 1 ≤ Real.sqrt (1 + ‖Y‖ ^ 2) := by
    rw [Real.one_le_sqrt]; nlinarith [sq_nonneg ‖Y‖]
  calc ‖Y‖ / Real.sqrt (1 + ‖Y‖ ^ 2) ≤ ‖Y‖ := div_le_self (norm_nonneg _) hs
    _ ≤ (r / ρ) ^ k * ‖X‖ := hY

/-- **Subspace iteration with the explicit constant** ([golub2013matrix] Theorem 8.2.2, (8.2.12)):
let `A` be symmetric with an orthonormal eigenbasis `v` (`A (v i) = l i • v i`, `l` real), `J` a
set of indices with `|l j| ≥ ρ > 0` for `j ∈ J` and `|l i| ≤ r` for `i ∉ J`,
`D = span (v '' J)` the dominant invariant subspace, and `S` with `dim S = dim D` and
`d₀ = gap D S < 1`. Then `gap D (A^k S) ≤ (r / ρ)^k d₀ / √(1 - d₀²)`: the `tan Θ` form of the
book's argument, with no CS decomposition, through
`LinearMap.IsSymmetric.gap_subspaceIterate_le_of_invariant` (the eigenbasis gives
`‖A u‖ ≥ ρ ‖u‖` on `D` and `‖A w‖ ≤ r ‖w‖` on `Dᗮ = span (v '' Jᶜ)`). Compare
`Krylov.exists_gap_subspaceIterate_span_image_le` (any diagonalizable `A`, unspecified
constant). -/
theorem gap_subspaceIterate_le (hA : A.IsSymmetric) {ι : Type*} [Fintype ι]
    (v : OrthonormalBasis ι 𝕜 E) {l : ι → ℝ} (hv : ∀ i, A (v i) = (l i : 𝕜) • v i)
    (J : Set ι) {ρ r : ℝ} (hρ : 0 < ρ) (hJ : ∀ j ∈ J, ρ ≤ |l j|) (hJc : ∀ i ∉ J, |l i| ≤ r)
    {S : Submodule 𝕜 E} (hdim : Module.finrank 𝕜 S = Module.finrank 𝕜 (Submodule.span 𝕜 (v '' J)))
    (h0 : (Submodule.span 𝕜 (v '' J)).gap S < 1) (k : ℕ) :
    (Submodule.span 𝕜 (v '' J)).gap (Krylov.subspaceIterate A S k) ≤
      (r / ρ) ^ k * ((Submodule.span 𝕜 (v '' J)).gap S /
        Real.sqrt (1 - (Submodule.span 𝕜 (v '' J)).gap S ^ 2)) := by
  classical
  set D := Submodule.span 𝕜 (v '' J) with hDdef
  have h1 := Krylov.inner_pow_apply_of_eigenbasis v hv 1
  simp only [pow_one] at h1
  -- coordinates vanish off `J` on `D`, on `J` on `Dᗮ`
  have hDc : ∀ u ∈ D, ∀ i ∉ J, (inner 𝕜 (v i) u : 𝕜) = 0 := by
    intro u hu i hi
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨j, hj, rfl⟩
      have hij : i ≠ j := fun h => hi (by rw [h]; exact hj)
      rw [orthonormal_iff_ite.mp v.orthonormal i j]
      simp [hij]
    · simp
    · intro x y _ _ hx hy; rw [inner_add_right, hx, hy, add_zero]
    · intro c x _ hx; rw [inner_smul_right, hx, mul_zero]
  have hDo : ∀ w ∈ Dᗮ, ∀ j ∈ J, (inner 𝕜 (v j) w : 𝕜) = 0 := fun w hw j hj =>
    (Submodule.mem_orthogonal D w).1 hw _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  have hnormA : ∀ u, ‖A u‖ ^ 2 = ∑ i, |l i| ^ 2 * ‖(inner 𝕜 (v i) u : 𝕜)‖ ^ 2 := fun u => by
    rw [← v.sum_sq_norm_inner_right (A u)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1, norm_mul, RCLike.norm_ofReal, mul_pow]
  have hnorm : ∀ u, ‖u‖ ^ 2 = ∑ i, ‖(inner 𝕜 (v i) u : 𝕜)‖ ^ 2 := fun u =>
    (v.sum_sq_norm_inner_right u).symm
  have hD : ∀ x ∈ D, A x ∈ D := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨j, hj, rfl⟩
      rw [hv]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · simp
    · intro x y _ _ hx hy; rw [map_add]; exact D.add_mem hx hy
    · intro c x _ hx; rw [map_smul]; exact D.smul_mem c hx
  have hlow : ∀ u ∈ D, ρ * ‖u‖ ≤ ‖A u‖ := by
    intro u hu
    refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
    rw [mul_pow, hnorm, hnormA, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : i ∈ J
    · gcongr
      exact (hJ i hi)
    · rw [hDc u hu i hi, norm_zero]; simp
  have hup : ∀ w ∈ Dᗮ, ‖A w‖ ≤ max r 0 * ‖w‖ := by
    intro w hw
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    rw [mul_pow, hnormA, hnorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : i ∈ J
    · rw [hDo w hw i hi, norm_zero]; simp
    · gcongr
      exact (hJc i hi).trans (le_max_left _ _)
  have hcore := gap_subspaceIterate_le_of_invariant hA hD hρ (le_max_right r 0) hlow hup hdim h0 k
  rcases le_or_gt 0 r with hr | hr
  · rwa [max_eq_left hr] at hcore
  -- `r < 0`: every index is in `J`, `D = ⊤ = S`, and both sides vanish
  have hall : ∀ i, i ∈ J := fun i => by
    by_contra hi; exact absurd ((abs_nonneg _).trans (hJc i hi)) (not_le.2 hr)
  have hDtop : D = ⊤ := by
    rw [hDdef, show v '' J = Set.range v by ext x; simp [hall],
      ← OrthonormalBasis.coe_toBasis, v.toBasis.span_eq]
  have hS : S = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hdim, hDtop, finrank_top])
  have hd : D.gap S = 0 := by rw [D.gap_congr S hS, hDtop, Submodule.gap_self]
  rw [hd] at hcore ⊢
  simpa using hcore

end LinearMap.IsSymmetric

namespace Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- **Subspace iteration toward an invariant subspace with an invariant complement** (the
coordinate-free core of [golub2013matrix] Theorem 7.3.1, corrected): let `D` and `W` be
complementary `A`-invariant subspaces (not necessarily orthogonal), `S` of the dimension of `D` with
`d̃₀ = gap Wᗮ S < 1`, and let `c`, `β`, `γ` bound the oblique projection onto `D` along `W`
(`‖Π x‖ ≤ c ‖x‖`), the compression of `A^k` to `Dᗮ` (`‖P_{Dᗮ} A^k w‖ ≤ β ‖w‖` on `Dᗮ`) and the
inverse of `A^k` on `D` (`‖u‖ ≤ γ ‖A^k u‖` on `D`). Then
`gap D (A^k S) ≤ c β γ · gap D S / √(1 - d̃₀²)`.

Write `s₀ ∈ S` as `u₀ + ω₀` along `D ⊕ W`. Then `P_{Wᗮ} s₀ = P_{Wᗮ} u₀`, so
`√(1 - d̃₀²) ‖s₀‖ ≤ ‖u₀‖`; for `s = A^k s₀` the component along `D` is `A^k u₀`, so
`‖u₀‖ ≤ γ c ‖s‖`; and `P_{Dᗮ} s = P_{Dᗮ} A^k P_{Dᗮ} s₀` (`D` is invariant), so
`‖P_{Dᗮ} s‖ ≤ β ‖P_{Dᗮ} s₀‖ ≤ β · gap D S · ‖s₀‖`. The gap of equal-dimensional subspaces is the
one-sided `‖P_{Dᗮ} P_{A^k S}‖` (`Submodule.gap_eq_norm_orthogonal_mul_of_finrank_eq`). No graph
representation and no CS decomposition are needed. -/
theorem gap_subspaceIterate_le_of_isCompl {A : E →ₗ[𝕜] E} {D W S : Submodule 𝕜 E}
    (hD : ∀ x ∈ D, A x ∈ D) (hW : ∀ x ∈ W, A x ∈ W) (hDW : IsCompl D W)
    (hdim : Module.finrank 𝕜 S = Module.finrank 𝕜 D) (h0 : Wᗮ.gap S < 1) (k : ℕ)
    {c β γ : ℝ} (hc0 : 0 ≤ c) (hβ0 : 0 ≤ β) (hγ0 : 0 ≤ γ)
    (hc : ∀ x, ‖Submodule.projection (p := D) (q := W) hDW x‖ ≤ c * ‖x‖)
    (hβ : ∀ w ∈ Dᗮ, ‖Dᗮ.starProjection ((A ^ k) w)‖ ≤ β * ‖w‖)
    (hγ : ∀ u ∈ D, ‖u‖ ≤ γ * ‖(A ^ k) u‖) :
    D.gap (subspaceIterate A S k) ≤
      c * β * γ * (D.gap S / Real.sqrt (1 - Wᗮ.gap S ^ 2)) := by
  set d := D.gap S with hd
  set d' := Wᗮ.gap S with hd'
  have hd0 : 0 ≤ d := D.gap_nonneg S
  have hd'0 : 0 ≤ d' := Wᗮ.gap_nonneg S
  have hsq : 0 < Real.sqrt (1 - d' ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  set B := c * β * γ * (d / Real.sqrt (1 - d' ^ 2)) with hB
  have hB0 : 0 ≤ B := by positivity
  -- the two one-sided gaps of `S`
  have hS1 : ∀ s ∈ S, ‖Dᗮ.starProjection s‖ ≤ d * ‖s‖ := fun s hs => by
    have h := (Dᗮ.starProjection * S.starProjection).le_opNorm s
    rw [mul_apply_eq_comp, Submodule.starProjection_eq_self_iff.2 hs] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [hd, Submodule.gap_comm]
    exact S.norm_orthogonal_mul_le_gap D
  have hS2 : ∀ s ∈ S, Real.sqrt (1 - d' ^ 2) * ‖s‖ ≤ ‖Wᗮ.starProjection s‖ := fun s hs => by
    have h := (Wᗮᗮ.starProjection * S.starProjection).le_opNorm s
    rw [mul_apply_eq_comp, Submodule.starProjection_eq_self_iff.2 hs] at h
    have h1 : ‖Wᗮᗮ.starProjection s‖ ≤ d' * ‖s‖ := by
      refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      rw [hd', Submodule.gap_comm]
      exact S.norm_orthogonal_mul_le_gap Wᗮ
    have h2 := Submodule.norm_sq_eq_add_norm_sq_starProjection s Wᗮ
    have h3 : (1 - d' ^ 2) * ‖s‖ ^ 2 ≤ ‖Wᗮ.starProjection s‖ ^ 2 := by
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) h1 2, norm_nonneg s]
    rw [← Real.sqrt_sq (norm_nonneg (Wᗮ.starProjection s)), ← Real.sqrt_sq (norm_nonneg s),
      ← Real.sqrt_mul (by nlinarith)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  -- the key estimate for `s = A^k s₀`
  have hkey : ∀ s₀ ∈ S, ‖Dᗮ.starProjection ((A ^ k) s₀)‖ ≤ B * ‖(A ^ k) s₀‖ ∧
      ‖s₀‖ ≤ γ * c * ‖(A ^ k) s₀‖ / Real.sqrt (1 - d' ^ 2) := by
    intro s₀ hs₀
    set u₀ := Submodule.projection (p := D) (q := W) hDW s₀ with hu₀
    set ω₀ := Submodule.projection (p := W) (q := D) hDW.symm s₀ with hω₀
    have hu₀D : u₀ ∈ D := Submodule.projection_apply_mem (p := D) (q := W) hDW s₀
    have hω₀W : ω₀ ∈ W := Submodule.projection_apply_mem (p := W) (q := D) hDW.symm s₀
    have hsum : u₀ + ω₀ = s₀ :=
      Submodule.projection_add_projection_eq_self (p := D) (q := W) hDW s₀
    have hAu : (A ^ k) u₀ ∈ D := Module.End.pow_apply_mem_of_forall_mem k hD u₀ hu₀D
    have hAω : (A ^ k) ω₀ ∈ W := Module.End.pow_apply_mem_of_forall_mem k hW ω₀ hω₀W
    -- the component of `A^k s₀` along `D` is `A^k u₀`
    have hPi : Submodule.projection (p := D) (q := W) hDW ((A ^ k) s₀) = (A ^ k) u₀ := by
      rw [← hsum, map_add, map_add,
        Submodule.projection_apply_of_mem_left (p := D) (q := W) hDW hAu,
        (Submodule.projection_apply_eq_zero_iff (p := D) (q := W) hDW).2 hAω, add_zero]
    -- `‖u₀‖ ≤ γ c ‖A^k s₀‖`
    have hu : ‖u₀‖ ≤ γ * c * ‖(A ^ k) s₀‖ := by
      calc ‖u₀‖ ≤ γ * ‖(A ^ k) u₀‖ := hγ u₀ hu₀D
        _ ≤ γ * (c * ‖(A ^ k) s₀‖) := by
            rw [← hPi]; exact mul_le_mul_of_nonneg_left (hc _) hγ0
        _ = γ * c * ‖(A ^ k) s₀‖ := by ring
    -- `√(1 - d̃₀²) ‖s₀‖ ≤ ‖u₀‖`
    have hWu : Wᗮ.starProjection s₀ = Wᗮ.starProjection u₀ := by
      have hω : Wᗮ.starProjection ω₀ = 0 :=
        (Submodule.starProjection_apply_eq_zero_iff Wᗮ).2
          (W.le_orthogonal_orthogonal hω₀W)
      rw [← hsum, map_add, hω, add_zero]
    have hsu : Real.sqrt (1 - d' ^ 2) * ‖s₀‖ ≤ ‖u₀‖ :=
      (hS2 s₀ hs₀).trans (by rw [hWu]; exact Wᗮ.norm_starProjection_apply_le u₀)
    have hsu' : ‖s₀‖ ≤ γ * c * ‖(A ^ k) s₀‖ / Real.sqrt (1 - d' ^ 2) := by
      rw [le_div_iff₀ hsq, mul_comm]
      exact hsu.trans hu
    refine ⟨?_, hsu'⟩
    -- `P_{Dᗮ} A^k s₀ = P_{Dᗮ} A^k P_{Dᗮ} s₀`
    have hsplitD : s₀ = D.starProjection s₀ + Dᗮ.starProjection s₀ := by
      rw [Submodule.starProjection_orthogonal_val]
      abel
    have hAD : (A ^ k) (D.starProjection s₀) ∈ D :=
      Module.End.pow_apply_mem_of_forall_mem k hD _ (D.starProjection_apply_mem s₀)
    have hPD : Dᗮ.starProjection ((A ^ k) s₀) =
        Dᗮ.starProjection ((A ^ k) (Dᗮ.starProjection s₀)) := by
      conv_lhs => rw [hsplitD]
      rw [map_add, map_add, (Submodule.starProjection_apply_eq_zero_iff Dᗮ).2
        (D.le_orthogonal_orthogonal hAD), zero_add]
    calc ‖Dᗮ.starProjection ((A ^ k) s₀)‖
        ≤ β * ‖Dᗮ.starProjection s₀‖ := by
          rw [hPD]; exact hβ _ (Dᗮ.starProjection_apply_mem s₀)
      _ ≤ β * (d * ‖s₀‖) := mul_le_mul_of_nonneg_left (hS1 s₀ hs₀) hβ0
      _ ≤ β * (d * (γ * c * ‖(A ^ k) s₀‖ / Real.sqrt (1 - d' ^ 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsu' hd0) hβ0
      _ = B * ‖(A ^ k) s₀‖ := by rw [hB]; ring
  -- `A^k` is injective on `S`, so `A^k S` has the dimension of `D`
  have hinj : Function.Injective ((A ^ k) ∘ₗ S.subtype) := by
    intro x y hxy
    have h1 := (hkey (x - y : S) (x - y : S).2).2
    rw [Submodule.coe_sub, map_sub] at h1
    have h2 : (A ^ k) (x : E) - (A ^ k) (y : E) = 0 := sub_eq_zero.2 hxy
    rw [h2, norm_zero, mul_zero, zero_div] at h1
    exact sub_eq_zero.1 (Subtype.ext (by
      simpa using norm_le_zero_iff.1 h1))
  have hdimk : Module.finrank 𝕜 (subspaceIterate A S k) = Module.finrank 𝕜 D := by
    have h1 : subspaceIterate A S k = LinearMap.range ((A ^ k) ∘ₗ S.subtype) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
      rfl
    rw [h1, LinearMap.finrank_range_of_inj hinj, hdim]
  rw [Submodule.gap_comm, Submodule.gap_eq_norm_orthogonal_mul_of_finrank_eq _ D hdimk]
  refine ContinuousLinearMap.opNorm_le_bound _ hB0 fun x => ?_
  rw [mul_apply_eq_comp]
  obtain ⟨s₀, hs₀, hs⟩ :=
    mem_subspaceIterate.1 ((subspaceIterate A S k).starProjection_apply_mem x)
  have h := (hkey s₀ hs₀).1
  rw [hs] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    ((subspaceIterate A S k).norm_starProjection_apply_le x) hB0)

end Krylov

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

omit [DecidableEq n] in
/-- **The distance to a graph subspace** ([golub2013matrix] Corollary 7.2.5 and (7.2.6)): in
`EuclideanSpace 𝕜 (m ⊕ n)`, `dist(ran [I; 0], ran [I; P]) ≤ ‖P‖₂` (and `‖P‖₂ ≤ ‖P‖_F`,
`Matrix.l2_opNorm_le_frobenius_norm`). The two subspaces have equal dimension, so the gap is the
one-sided `‖P_{K⊥} P_G‖`; a vector of `G` is `(x, P x)`, whose component orthogonal to
`K = ran [I; 0]` is `(0, P x)`, of norm at most `‖P‖₂ ‖x‖ ≤ ‖P‖₂ ‖(x, P x)‖`. The exact value is
`‖P‖₂ / √(1 + ‖P‖₂²)` (`Submodule.gap_graph`). -/
theorem gap_range_fromRows_le (P : Matrix n m 𝕜) :
    (LinearMap.range (toEuclideanLin (fromRows (1 : Matrix m m 𝕜) (0 : Matrix n m 𝕜)))).gap
        (LinearMap.range (toEuclideanLin (fromRows (1 : Matrix m m 𝕜) P))) ≤ lpOpNorm 2 P := by
  set K := LinearMap.range (toEuclideanLin (fromRows (1 : Matrix m m 𝕜) (0 : Matrix n m 𝕜)))
  set G := LinearMap.range (toEuclideanLin (fromRows (1 : Matrix m m 𝕜) P))
  have happ : ∀ (Q : Matrix n m 𝕜) (x : EuclideanSpace 𝕜 m),
      toEuclideanLin (fromRows 1 Q) x =
        WithLp.toLp 2 (Sum.elim (WithLp.ofLp x) (Q *ᵥ WithLp.ofLp x)) :=
    fun Q x => by rw [toEuclideanLin_apply, fromRows_mulVec, one_mulVec]
  have hinj : ∀ Q : Matrix n m 𝕜, Function.Injective (toEuclideanLin (fromRows 1 Q)) :=
    fun Q x y hxy => by
      rw [happ, happ] at hxy
      have := congrArg (fun v => (WithLp.ofLp v) ∘ Sum.inl) hxy
      exact WithLp.ofLp_injective 2 (by simpa using this)
  have hdim : Module.finrank 𝕜 G = Module.finrank 𝕜 K := by
    rw [LinearMap.finrank_range_of_inj (hinj P), LinearMap.finrank_range_of_inj (hinj 0)]
  rw [Submodule.gap_comm, Submodule.gap_eq_norm_orthogonal_mul_of_finrank_eq G K hdim]
  refine ContinuousLinearMap.opNorm_le_bound _ (lpOpNorm_nonneg _ _) fun z => ?_
  obtain ⟨x, hx⟩ := G.starProjection_apply_mem z
  rw [mul_apply_eq_comp]
  -- the decomposition `(x, P x) = (x, 0) + (0, P x)`
  set y : EuclideanSpace 𝕜 (m ⊕ n) := WithLp.toLp 2 (Sum.elim 0 (P *ᵥ WithLp.ofLp x))
  have hsplit : (G.starProjection z : EuclideanSpace 𝕜 (m ⊕ n)) =
      toEuclideanLin (fromRows 1 (0 : Matrix n m 𝕜)) x + y := by
    rw [← hx, happ, happ]
    ext (i | i) <;> simp [y]
  have hyK : y ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨u, rfl⟩
    rw [happ, EuclideanSpace.inner_eq_star_dotProduct]
    simp [y, dotProduct, Fintype.sum_sum_type]
  have hK : toEuclideanLin (fromRows 1 (0 : Matrix n m 𝕜)) x ∈ K := ⟨x, rfl⟩
  have hproj : Kᗮ.starProjection (G.starProjection z) = y := by
    rw [hsplit, map_add, (Submodule.starProjection_apply_eq_zero_iff Kᗮ).2
      (K.le_orthogonal_orthogonal hK), zero_add, Submodule.starProjection_eq_self_iff.2 hyK]
  rw [hproj]
  -- norms
  have hy : ‖y‖ = ‖WithLp.toLp 2 (P *ᵥ WithLp.ofLp x)‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp [y, Fintype.sum_sum_type]
  have hxg : ‖x‖ ≤ ‖G.starProjection z‖ := by
    rw [← hx, happ, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hPx : ‖WithLp.toLp 2 (P *ᵥ WithLp.ofLp x)‖ ≤ lpOpNorm 2 P * ‖x‖ :=
    (lpCLM 2 P).le_opNorm x
  calc ‖y‖ ≤ lpOpNorm 2 P * ‖x‖ := hy ▸ hPx
    _ ≤ lpOpNorm 2 P * ‖G.starProjection z‖ := mul_le_mul_of_nonneg_left hxg (lpOpNorm_nonneg _ _)
    _ ≤ lpOpNorm 2 P * ‖z‖ :=
        mul_le_mul_of_nonneg_left (G.norm_starProjection_apply_le z) (lpOpNorm_nonneg _ _)

end Matrix

/-! ### Orthogonal iteration from a Schur form: [golub2013matrix] Theorem 7.3.1, corrected -/

namespace Matrix

section OrthogonalIteration

open scoped Matrix.Norms.Frobenius

variable {r s : ℕ}

/-- A vector of `EuclideanSpace` on `p ⊕ q` from its two blocks. -/
private noncomputable abbrev blk {p q : Type*} (u : EuclideanSpace ℂ p) (w : EuclideanSpace ℂ q) :
    EuclideanSpace ℂ (p ⊕ q) :=
  WithLp.toLp 2 (Sum.elim (WithLp.ofLp u) (WithLp.ofLp w))

/-- The first block of a vector on `p ⊕ q`. -/
private noncomputable abbrev fstB {p q : Type*} (x : EuclideanSpace ℂ (p ⊕ q)) :
    EuclideanSpace ℂ p :=
  WithLp.toLp 2 (WithLp.ofLp x ∘ Sum.inl)

/-- The second block of a vector on `p ⊕ q`. -/
private noncomputable abbrev sndB {p q : Type*} (x : EuclideanSpace ℂ (p ⊕ q)) :
    EuclideanSpace ℂ q :=
  WithLp.toLp 2 (WithLp.ofLp x ∘ Sum.inr)

private theorem blk_fstB_sndB {p q : Type*} (x : EuclideanSpace ℂ (p ⊕ q)) :
    blk (fstB x) (sndB x) = x := by
  ext (i | i) <;> rfl

private theorem norm_blk_sq {p q : Type*} [Fintype p] [Fintype q] (u : EuclideanSpace ℂ p)
    (w : EuclideanSpace ℂ q) : ‖blk u w‖ ^ 2 = ‖u‖ ^ 2 + ‖w‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

private theorem norm_fstB_le {p q : Type*} [Fintype p] [Fintype q]
    (x : EuclideanSpace ℂ (p ⊕ q)) : ‖fstB x‖ ≤ ‖x‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  conv_rhs => rw [← blk_fstB_sndB x, norm_blk_sq]
  nlinarith [sq_nonneg ‖sndB x‖]

private theorem norm_sndB_le {p q : Type*} [Fintype p] [Fintype q]
    (x : EuclideanSpace ℂ (p ⊕ q)) : ‖sndB x‖ ≤ ‖x‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  conv_rhs => rw [← blk_fstB_sndB x, norm_blk_sq]
  nlinarith [sq_nonneg ‖fstB x‖]

private theorem inner_blk {p q : Type*} [Fintype p] [Fintype q] (u u' : EuclideanSpace ℂ p)
    (w w' : EuclideanSpace ℂ q) :
    inner ℂ (blk u w) (blk u' w') = inner ℂ u u' + inner ℂ w w' := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  rfl

private theorem blk_add {p q : Type*} (u u' : EuclideanSpace ℂ p) (w w' : EuclideanSpace ℂ q) :
    blk (u + u') (w + w') = blk u w + blk u' w' := by
  ext (i | i) <;> rfl

private theorem norm_blk_zero_right {p q : Type*} [Fintype p] [Fintype q]
    (u : EuclideanSpace ℂ p) : ‖blk u (0 : EuclideanSpace ℂ q)‖ = ‖u‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (blk u _)), norm_blk_sq, norm_zero, zero_pow two_ne_zero,
    add_zero, Real.sqrt_sq (norm_nonneg _)]

private theorem norm_blk_zero_left {p q : Type*} [Fintype p] [Fintype q]
    (w : EuclideanSpace ℂ q) : ‖blk (0 : EuclideanSpace ℂ p) w‖ = ‖w‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (blk _ w)), norm_blk_sq, norm_zero, zero_pow two_ne_zero,
    zero_add, Real.sqrt_sq (norm_nonneg _)]

private theorem toEuclideanLin_fromRows_apply {p q k : Type*} [Fintype k] [DecidableEq k]
    (A₁ : Matrix p k ℂ) (A₂ : Matrix q k ℂ) (y : EuclideanSpace ℂ k) :
    toEuclideanLin (fromRows A₁ A₂) y = blk (toEuclideanLin A₁ y) (toEuclideanLin A₂ y) := by
  ext (i | i) <;> rfl

private theorem toEuclideanLin_fromBlocks_apply {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q] (M₁₁ : Matrix p p ℂ) (M₁₂ : Matrix p q ℂ) (M₂₁ : Matrix q p ℂ)
    (M₂₂ : Matrix q q ℂ) (u : EuclideanSpace ℂ p) (w : EuclideanSpace ℂ q) :
    toEuclideanLin (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) (blk u w) =
      blk (toEuclideanLin M₁₁ u + toEuclideanLin M₁₂ w)
        (toEuclideanLin M₂₁ u + toEuclideanLin M₂₂ w) := by
  ext (i | i) <;> simp [toEuclideanLin_apply, fromBlocks_mulVec]

/-- The powers of a block upper triangular matrix are block upper triangular, with the powers
of the diagonal blocks on the diagonal. -/
private theorem exists_fromBlocks_pow {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p]
    [DecidableEq q] (M₁₁ : Matrix p p ℂ) (M₁₂ : Matrix p q ℂ) (M₂₂ : Matrix q q ℂ) (k : ℕ) :
    ∃ Y, fromBlocks M₁₁ M₁₂ 0 M₂₂ ^ k = fromBlocks (M₁₁ ^ k) Y 0 (M₂₂ ^ k) := by
  induction k with
  | zero => exact ⟨0, by rw [pow_zero, pow_zero, pow_zero, fromBlocks_one]⟩
  | succ k ih =>
    obtain ⟨Y, hY⟩ := ih
    refine ⟨M₁₁ ^ k * M₁₂ + Y * M₂₂, ?_⟩
    rw [pow_succ, hY, fromBlocks_multiply, pow_succ, pow_succ]
    simp

private theorem norm_toEuclideanLin_le_lpOpNorm {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq q] (M : Matrix p q ℂ) (y : EuclideanSpace ℂ q) :
    ‖toEuclideanLin M y‖ ≤ lpOpNorm 2 M * ‖y‖ :=
  (lpCLM 2 M).le_opNorm y

/-- A triangular matrix has only its diagonal entries as eigenvalues. -/
private theorem exists_eq_of_mem_spectrum_of_isUpperTriangular {k : ℕ}
    {T : Matrix (Fin k) (Fin k) ℂ} (hT : T.IsUpperTriangular) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ T) : ∃ i, T i i = μ := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, not_not] at hμ
  have htri : (μ • (1 : Matrix (Fin k) (Fin k) ℂ) - T).IsUpperTriangular := fun i j hij => by
    have hji : j < i := hij
    rw [sub_apply, smul_apply, one_apply_ne (ne_of_lt hji).symm, hT hji, smul_zero, sub_zero]
  rw [det_of_isUpperTriangular htri, Finset.prod_eq_zero_iff] at hμ
  obtain ⟨i, -, hi⟩ := hμ
  refine ⟨i, ?_⟩
  simp only [sub_apply, smul_apply, one_apply_eq, smul_eq_mul, mul_one] at hi
  exact (sub_eq_zero.1 hi).symm

/-- The block form of the corrected Theorem 7.3.1: in `EuclideanSpace ℂ (Fin r ⊕ Fin s)`, for
`M = [T₁₁ T₁₂; 0 T₂₂]` with `T₁₁` invertible and `X` solving `T₁₁ X - X T₂₂ = -T₁₂`, the ranges
`D = ran [I; 0]`, `W = ran [X; I]` are complementary invariant subspaces, `Wᗮ = D' = ran [I; -Xᴴ]`,
and `Krylov.gap_subspaceIterate_le_of_isCompl` applies with `c = 1 + ‖X‖₂`, `β = ‖T₂₂^k‖₂`,
`γ = ‖T₁₁^{-k}‖₂`. -/
private theorem gap_subspaceIterate_le_of_blocks {T₁₁ : Matrix (Fin r) (Fin r) ℂ}
    {T₁₂ : Matrix (Fin r) (Fin s) ℂ} {T₂₂ : Matrix (Fin s) (Fin s) ℂ} (hT₁₁ : IsUnit T₁₁)
    {X : Matrix (Fin r) (Fin s) ℂ} (hX : T₁₁ * X - X * T₂₂ = -T₁₂)
    {S : Submodule ℂ (EuclideanSpace ℂ (Fin r ⊕ Fin s))} (hdim : Module.finrank ℂ S = r)
    (h0 : (LinearMap.range (toEuclideanLin
      (fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (-Xᴴ)))).gap S < 1) (k : ℕ) :
    (LinearMap.range (toEuclideanLin
      (fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (0 : Matrix (Fin s) (Fin r) ℂ)))).gap
        (Krylov.subspaceIterate (toEuclideanLin (fromBlocks T₁₁ T₁₂ 0 T₂₂)) S k) ≤
      (1 + lpOpNorm 2 X) * lpOpNorm 2 (T₂₂ ^ k) * lpOpNorm 2 (T₁₁⁻¹ ^ k) *
        ((LinearMap.range (toEuclideanLin
          (fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (0 : Matrix (Fin s) (Fin r) ℂ)))).gap S /
          Real.sqrt (1 - (LinearMap.range (toEuclideanLin
            (fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (-Xᴴ)))).gap S ^ 2)) := by
  set B := toEuclideanLin (fromBlocks T₁₁ T₁₂ 0 T₂₂) with hB
  set D := LinearMap.range (toEuclideanLin
    (fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (0 : Matrix (Fin s) (Fin r) ℂ))) with hD
  set W := LinearMap.range (toEuclideanLin
    (fromRows X (1 : Matrix (Fin s) (Fin s) ℂ))) with hW
  set D' := LinearMap.range (toEuclideanLin
    (fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (-Xᴴ))) with hD'
  have hXT : T₁₁ * X + T₁₂ = X * T₂₂ := by
    rw [← sub_eq_zero, show T₁₁ * X + T₁₂ - X * T₂₂ = (T₁₁ * X - X * T₂₂) + T₁₂ by abel, hX,
      neg_add_cancel]
  -- membership in `D` and `W`
  have hmemD : ∀ x, x ∈ D ↔ sndB x = 0 := fun x => by
    constructor
    · rintro ⟨y, rfl⟩
      rw [toEuclideanLin_fromRows_apply, map_zero]
      rfl
    · intro hx
      refine ⟨fstB x, ?_⟩
      rw [toEuclideanLin_fromRows_apply, toEuclideanLin_one, LinearMap.id_apply,
        map_zero, LinearMap.zero_apply, ← hx, blk_fstB_sndB]
  have hblkD : ∀ y, blk y (0 : EuclideanSpace ℂ (Fin s)) ∈ D := fun y =>
    (hmemD _).2 rfl
  have hblkW : ∀ z, blk (toEuclideanLin X z) z ∈ W := fun z =>
    ⟨z, by rw [toEuclideanLin_fromRows_apply, toEuclideanLin_one, LinearMap.id_apply]⟩
  -- invariance
  have hBblk : ∀ u w, B (blk u w) = blk (toEuclideanLin T₁₁ u + toEuclideanLin T₁₂ w)
      (toEuclideanLin T₂₂ w) := fun u w => by
    rw [hB, toEuclideanLin_fromBlocks_apply, map_zero, LinearMap.zero_apply, zero_add]
  have hDinv : ∀ x ∈ D, B x ∈ D := fun x hx => by
    rw [hmemD] at hx ⊢
    rw [← blk_fstB_sndB x, hx, hBblk, map_zero, map_zero]
    rfl
  have hWinv : ∀ x ∈ W, B x ∈ W := by
    rintro _ ⟨z, rfl⟩
    refine ⟨toEuclideanLin T₂₂ z, ?_⟩
    rw [toEuclideanLin_fromRows_apply, toEuclideanLin_fromRows_apply, toEuclideanLin_one,
      LinearMap.id_apply, LinearMap.id_apply, hBblk, ← toEuclideanLin_mul_apply,
      ← toEuclideanLin_mul_apply, ← LinearMap.add_apply, ← map_add, hXT]
  -- the decomposition along `D ⊕ W`
  have hdec : ∀ x, x = blk (fstB x - toEuclideanLin X (sndB x)) 0 +
      blk (toEuclideanLin X (sndB x)) (sndB x) := fun x => by
    rw [← blk_add, sub_add_cancel, zero_add, blk_fstB_sndB]
  have hDW : IsCompl D W := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxD hxW
      obtain ⟨z, rfl⟩ := hxW
      rw [hmemD, toEuclideanLin_fromRows_apply, toEuclideanLin_one, LinearMap.id_apply] at hxD
      have hz : z = 0 := hxD
      rw [hz, map_zero]
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      rw [hdec x]
      exact Submodule.add_mem_sup (hblkD _) (hblkW _)
  -- `Wᗮ = D'`
  have hfinW : Module.finrank ℂ W = s := by
    rw [hW, LinearMap.finrank_range_of_inj, finrank_euclideanSpace_fin]
    intro z z' h
    have := congrArg sndB h
    rwa [toEuclideanLin_fromRows_apply, toEuclideanLin_fromRows_apply, toEuclideanLin_one,
      LinearMap.id_apply, LinearMap.id_apply] at this
  have hfinD : Module.finrank ℂ D = r := by
    rw [hD, LinearMap.finrank_range_of_inj, finrank_euclideanSpace_fin]
    intro z z' h
    have := congrArg fstB h
    rwa [toEuclideanLin_fromRows_apply, toEuclideanLin_fromRows_apply, toEuclideanLin_one,
      LinearMap.id_apply, LinearMap.id_apply] at this
  have hfinD' : Module.finrank ℂ D' = r := by
    rw [hD', LinearMap.finrank_range_of_inj, finrank_euclideanSpace_fin]
    intro z z' h
    have := congrArg fstB h
    rwa [toEuclideanLin_fromRows_apply, toEuclideanLin_fromRows_apply, toEuclideanLin_one,
      LinearMap.id_apply, LinearMap.id_apply] at this
  have hWD' : Wᗮ = D' := by
    symm
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨y, rfl⟩
      rw [Submodule.mem_orthogonal]
      rintro _ ⟨z, rfl⟩
      simp only [toEuclideanLin_fromRows_apply, toEuclideanLin_one, LinearMap.id_apply]
      rw [inner_blk, map_neg, LinearMap.neg_apply, inner_neg_right,
        toEuclideanLin_conjTranspose_inner_right, add_neg_cancel]
    · have h := Submodule.finrank_add_finrank_orthogonal W
      rw [finrank_euclideanSpace, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
        hfinW] at h
      rw [hfinD']
      omega
  -- the power of `B` on the two blocks
  obtain ⟨Y, hY⟩ := exists_fromBlocks_pow T₁₁ T₁₂ T₂₂ k
  have hBk : ∀ u w, (B ^ k) (blk u w) = blk (toEuclideanLin (T₁₁ ^ k) u +
      toEuclideanLin Y w) (toEuclideanLin (T₂₂ ^ k) w) := fun u w => by
    rw [hB, ← toEuclideanLin_pow, hY, toEuclideanLin_fromBlocks_apply, map_zero,
      LinearMap.zero_apply, zero_add]
  -- the constants
  have hc : ∀ x, ‖Submodule.projection (p := D) (q := W) hDW x‖ ≤ (1 + lpOpNorm 2 X) * ‖x‖ := by
    intro x
    have hPix : Submodule.projection (p := D) (q := W) hDW x =
        blk (fstB x - toEuclideanLin X (sndB x)) 0 := by
      conv_lhs => rw [hdec x]
      rw [map_add, Submodule.projection_apply_of_mem_left (p := D) (q := W) hDW (hblkD _),
        (Submodule.projection_apply_eq_zero_iff (p := D) (q := W) hDW).2 (hblkW _), add_zero]
    rw [hPix]
    rw [norm_blk_zero_right]
    calc ‖fstB x - toEuclideanLin X (sndB x)‖ ≤ ‖fstB x‖ + lpOpNorm 2 X * ‖sndB x‖ :=
          (norm_sub_le _ _).trans (add_le_add le_rfl (norm_toEuclideanLin_le_lpOpNorm X _))
      _ ≤ ‖x‖ + lpOpNorm 2 X * ‖x‖ :=
          add_le_add (norm_fstB_le x)
            (mul_le_mul_of_nonneg_left (norm_sndB_le x) (lpOpNorm_nonneg 2 X))
      _ = (1 + lpOpNorm 2 X) * ‖x‖ := by ring
  have hprojDo : ∀ x, Dᗮ.starProjection x = blk 0 (sndB x) := fun x => by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
    · rw [Submodule.mem_orthogonal]
      intro y hy
      rw [hmemD] at hy
      rw [← blk_fstB_sndB y, hy, inner_blk, inner_zero_right, inner_zero_left, add_zero]
    · have hx : x - blk 0 (sndB x) = blk (fstB x) 0 := by
        rw [sub_eq_iff_eq_add, ← blk_add, add_zero, zero_add, blk_fstB_sndB]
      rw [hx]
      exact Submodule.inner_right_of_mem_orthogonal (hblkD _) hw
  have hβ : ∀ w ∈ Dᗮ, ‖Dᗮ.starProjection ((B ^ k) w)‖ ≤ lpOpNorm 2 (T₂₂ ^ k) * ‖w‖ := by
    intro w _
    have hw : (B ^ k) w = blk (toEuclideanLin (T₁₁ ^ k) (fstB w) + toEuclideanLin Y (sndB w))
        (toEuclideanLin (T₂₂ ^ k) (sndB w)) := by
      conv_lhs => rw [← blk_fstB_sndB w]
      exact hBk _ _
    rw [hprojDo, hw, norm_blk_zero_left]
    exact (norm_toEuclideanLin_le_lpOpNorm _ _).trans
      (mul_le_mul_of_nonneg_left (norm_sndB_le w) (lpOpNorm_nonneg 2 _))
  have hγ : ∀ u ∈ D, ‖u‖ ≤ lpOpNorm 2 (T₁₁⁻¹ ^ k) * ‖(B ^ k) u‖ := by
    intro u hu
    rw [hmemD] at hu
    have hu' : blk (fstB u) (0 : EuclideanSpace ℂ (Fin s)) = u := by rw [← hu, blk_fstB_sndB]
    have hBu : (B ^ k) u = blk (toEuclideanLin (T₁₁ ^ k) (fstB u)) 0 := by
      conv_lhs => rw [← hu']
      rw [hBk, map_zero, map_zero, add_zero]
    have hinv : T₁₁⁻¹ ^ k * T₁₁ ^ k = 1 := by
      rw [inv_pow', nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 (hT₁₁.pow k))]
    calc ‖u‖ = ‖fstB u‖ := by
          conv_lhs => rw [← hu']
          exact norm_blk_zero_right _
      _ = ‖toEuclideanLin (T₁₁⁻¹ ^ k) (toEuclideanLin (T₁₁ ^ k) (fstB u))‖ := by
          rw [← toEuclideanLin_mul_apply, hinv, toEuclideanLin_one, LinearMap.id_apply]
      _ ≤ lpOpNorm 2 (T₁₁⁻¹ ^ k) * ‖toEuclideanLin (T₁₁ ^ k) (fstB u)‖ :=
          norm_toEuclideanLin_le_lpOpNorm _ _
      _ = lpOpNorm 2 (T₁₁⁻¹ ^ k) * ‖(B ^ k) u‖ := by rw [hBu, norm_blk_zero_right]
  have hc0 : 0 ≤ 1 + lpOpNorm 2 X := by linarith [lpOpNorm_nonneg 2 X]
  have key : ∀ (K K' : Submodule ℂ (EuclideanSpace ℂ (Fin r ⊕ Fin s)))
      [K.HasOrthogonalProjection] [K'.HasOrthogonalProjection], K = K' → K.gap S = K'.gap S := by
    intro K K' _ _ h
    subst h
    rfl
  have hgW : Wᗮ.gap S = D'.gap S := key _ _ hWD'
  have h0' : Wᗮ.gap S < 1 := by rw [hgW]; exact h0
  refine (Krylov.gap_subspaceIterate_le_of_isCompl hDinv hWinv hDW (hdim.trans hfinD.symm) h0' k
    hc0 (lpOpNorm_nonneg 2 _) (lpOpNorm_nonneg 2 _) hc hβ hγ).trans (le_of_eq ?_)
  rw [hgW]

/-- Congruence for the gap, across the orthogonal-projection instances. -/
private theorem gap_congr' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {K K' L L' : Submodule ℂ E} [K.HasOrthogonalProjection] [K'.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] [L'.HasOrthogonalProjection] (hK : K = K') (hL : L = L') :
    K.gap L = K'.gap L' := by
  subst hK hL
  rfl

/-- **Orthogonal iteration converges to the dominant invariant subspace** ([golub2013matrix]
Theorem 7.3.1, corrected). Let `Q` be unitary with `Qᴴ A Q` reindexed along `e` equal to the block
triangular `[T₁₁ T₁₂; 0 T₂₂]` (`T₁₁` of size `r`, `0 < r < n`), both diagonal blocks upper
triangular, `|t_ii| ≥ a` on `T₁₁`, `|t_jj| ≤ b < a` on `T₂₂`, the strictly upper parts of both
blocks of Frobenius norm at most `ν`, `μ ≥ 0` with `ν < (1 + μ) a`, and `X` the solution of
`T₁₁ X - X T₂₂ = -T₁₂`. Let `D = ran Q [I; 0]` (the dominant invariant subspace `D_r(A)`),
`D' = ran Q [I; -Xᴴ]` (the book's `D_r(Aᴴ)`, the orthogonal complement of the complementary
invariant subspace `ran Q [X; I]`), and `S₀` of dimension `r` with `d̃₀ = dist(D', S₀) < 1`. Then
for every `k`,
`dist(D, A^k S₀) ≤ (1 + μ)^{n-2} (1 + ‖T₁₂‖_F / sep(T₁₁, T₂₂))
  ((b + ν/(1+μ)) / (a - ν/(1+μ)))^k · dist(D, S₀) / √(1 - d̃₀²)`.
The book's statement, with `a = |λ_r|`, `b = |λ_{r+1}|`, `ν = ‖N‖_F`, assumes `dist(D, S₀) < 1`
instead of `d̃₀ < 1` and is false (see the module doc); its proof uses `d̃₀`, and so does this one.
The block computation is `Matrix.gap_subspaceIterate_le_of_blocks`-shaped: the coordinate-free
`Krylov.gap_subspaceIterate_le_of_isCompl` with the powers bounded by Lemma 7.3.2
(`Matrix.l2_opNorm_pow_le_of_schur`, `Matrix.l2_opNorm_inv_pow_le_of_schur`) and
`‖X‖_F ≤ ‖T₁₂‖_F / sep` (`Matrix.frobenius_norm_le_div_sep`), transported by the isometry
`y ↦ Q (y ∘ e)` (`Submodule.gap_map_linearIsometryEquiv`). -/
theorem gap_subspaceIterate_le_of_schur {n r : ℕ} {A Q : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ) (e : Fin n ≃ Fin r ⊕ Fin (n - r))
    {T₁₁ : Matrix (Fin r) (Fin r) ℂ} {T₁₂ : Matrix (Fin r) (Fin (n - r)) ℂ}
    {T₂₂ : Matrix (Fin (n - r)) (Fin (n - r)) ℂ}
    (hT : (star Q * A * Q).reindex e e = fromBlocks T₁₁ T₁₂ 0 T₂₂)
    (hT₁₁ : T₁₁.IsUpperTriangular) (hT₂₂ : T₂₂.IsUpperTriangular) (hr : 0 < r) (hrn : r < n)
    {a b ν μ : ℝ} (hμ : 0 ≤ μ) (ha : ∀ i, a ≤ ‖T₁₁ i i‖) (hb : ∀ j, ‖T₂₂ j j‖ ≤ b)
    (hab : b < a) (hν₁ : ‖strictUpper T₁₁‖ ≤ ν) (hν₂ : ‖strictUpper T₂₂‖ ≤ ν)
    (hνa : ν < (1 + μ) * a) {X : Matrix (Fin r) (Fin (n - r)) ℂ}
    (hX : T₁₁ * X - X * T₂₂ = -T₁₂) {S₀ : Submodule ℂ (EuclideanSpace ℂ (Fin n))}
    (hdim : Module.finrank ℂ S₀ = r)
    (h0 : (LinearMap.range (toEuclideanLin
      (Q * (fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (-Xᴴ)).submatrix e id))).gap S₀ < 1)
    (k : ℕ) :
    (LinearMap.range (toEuclideanLin (Q * (fromRows (1 : Matrix (Fin r) (Fin r) ℂ)
        (0 : Matrix (Fin (n - r)) (Fin r) ℂ)).submatrix e id))).gap
        (Krylov.subspaceIterate (toEuclideanLin A) S₀ k) ≤
      (1 + μ) ^ (n - 2) * (1 + ‖T₁₂‖ / sep T₁₁ T₂₂) *
        ((b + ν / (1 + μ)) / (a - ν / (1 + μ))) ^ k *
        ((LinearMap.range (toEuclideanLin (Q * (fromRows (1 : Matrix (Fin r) (Fin r) ℂ)
          (0 : Matrix (Fin (n - r)) (Fin r) ℂ)).submatrix e id))).gap S₀ /
          Real.sqrt (1 - (LinearMap.range (toEuclideanLin
            (Q * (fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (-Xᴴ)).submatrix e id))).gap S₀ ^ 2)) :=
    by
  have hsp0 : 0 < n - r := by omega
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have : Nonempty (Fin (n - r)) := ⟨⟨0, hsp0⟩⟩
  have h1μ : 0 < 1 + μ := by linarith
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb ⟨0, hsp0⟩)
  have ha0 : 0 < a := lt_of_le_of_lt hb0 hab
  -- `T₁₁` is invertible and the spectra are disjoint
  have hT₁₁u : IsUnit T₁₁ := by
    rw [isUnit_iff_isUnit_det, det_of_isUpperTriangular hT₁₁, isUnit_iff_ne_zero,
      Finset.prod_ne_zero_iff]
    intro i _ h
    have := ha i
    rw [h, norm_zero] at this
    linarith
  have hsep : 0 < sep T₁₁ T₂₂ := by
    rw [sep_pos_iff_disjoint_spectrum]
    rw [Set.disjoint_left]
    intro μ' h₁ h₂
    obtain ⟨i, hi⟩ := exists_eq_of_mem_spectrum_of_isUpperTriangular hT₁₁ h₁
    obtain ⟨j, hj⟩ := exists_eq_of_mem_spectrum_of_isUpperTriangular hT₂₂ h₂
    have := ha i
    rw [hi, ← hj] at this
    linarith [hb j]
  -- the isometry `y ↦ Q (y ∘ e)`
  set Φ : EuclideanSpace ℂ (Fin r ⊕ Fin (n - r)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm).trans (unitaryLinearIsometryEquiv hQ)
    with hΦ
  have hΦapp : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (M : Matrix (Fin r ⊕ Fin (n - r)) κ ℂ)
      (y : EuclideanSpace ℂ κ),
      Φ (toEuclideanLin M y) = toEuclideanLin (Q * M.submatrix e id) y := by
    intro κ _ _ M y
    rw [hΦ, LinearIsometryEquiv.trans_apply, unitaryLinearIsometryEquiv_apply,
      toEuclideanLin_mul_apply]
    congr 1
  -- `A` is conjugate to the block matrix
  have h3 : fromBlocks T₁₁ T₁₂ 0 T₂₂ = (star Q * A * Q).submatrix e.symm e.symm := by
    rw [← hT]
    rfl
  set M := fromBlocks T₁₁ T₁₂ 0 T₂₂ with hM
  have hQQ : Q * star Q = 1 := mem_unitaryGroup_iff.1 hQ
  have hAQ : A * Q = Q * (star Q * A * Q) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
  have hconj : ∀ y, toEuclideanLin A (Φ y) = Φ (toEuclideanLin M y) := by
    intro y
    have h1 : Φ y = toEuclideanLin Q (WithLp.toLp 2 (WithLp.ofLp y ∘ e)) := by
      rw [hΦ, LinearIsometryEquiv.trans_apply, unitaryLinearIsometryEquiv_apply]
      rfl
    have h2 : Φ (toEuclideanLin M y) =
        toEuclideanLin Q (WithLp.toLp 2 (WithLp.ofLp (toEuclideanLin M y) ∘ e)) := by
      rw [hΦ, LinearIsometryEquiv.trans_apply, unitaryLinearIsometryEquiv_apply]
      rfl
    rw [h1, h2, ← toEuclideanLin_mul_apply, hAQ, toEuclideanLin_mul_apply]
    congr 1
    rw [h3]
    ext i
    simp
    rfl
  have hconjk : ∀ j y, (toEuclideanLin A ^ j) (Φ y) = Φ ((toEuclideanLin M ^ j) y) := by
    intro j
    induction j with
    | zero => intro y; rfl
    | succ j ih =>
      intro y
      rw [pow_succ', Module.End.mul_apply, ih, hconj, pow_succ', Module.End.mul_apply]
  -- transport of the subspaces
  set L : EuclideanSpace ℂ (Fin r ⊕ Fin (n - r)) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    (Φ.toLinearEquiv : EuclideanSpace ℂ (Fin r ⊕ Fin (n - r)) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
    with hL
  have hrange : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (N : Matrix (Fin r ⊕ Fin (n - r)) κ ℂ),
      LinearMap.range (toEuclideanLin (Q * N.submatrix e id)) =
        (LinearMap.range (toEuclideanLin N)).map L := by
    intro κ _ _ N
    rw [← LinearMap.range_comp]
    congr 1
    exact LinearMap.ext fun y => (hΦapp N y).symm
  set S := S₀.map (Φ.symm.toLinearEquiv :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin r ⊕ Fin (n - r))) with hSdef
  have hSmap : S.map L = S₀ := by
    rw [hSdef, ← Submodule.map_comp]
    convert Submodule.map_id S₀
    exact LinearMap.ext fun x => Φ.apply_symm_apply x
  have hiter : Krylov.subspaceIterate (toEuclideanLin A) S₀ k =
      (Krylov.subspaceIterate (toEuclideanLin M) S k).map L := by
    ext x
    rw [Krylov.mem_subspaceIterate, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(toEuclideanLin M ^ k) (Φ.symm y), ?_, ?_⟩
      · rw [Krylov.mem_subspaceIterate]
        exact ⟨Φ.symm y, ⟨y, hy, rfl⟩, rfl⟩
      · change Φ _ = _
        rw [← hconjk k, Φ.apply_symm_apply]
    · rintro ⟨z, hz, rfl⟩
      rw [Krylov.mem_subspaceIterate] at hz
      obtain ⟨t, ⟨y, hy, rfl⟩, rfl⟩ := hz
      refine ⟨y, hy, ?_⟩
      change _ = Φ _
      rw [← hconjk k]
      exact congrArg _ (Φ.apply_symm_apply y).symm
  have hdimS : Module.finrank ℂ S = r := by
    rw [hSdef, LinearEquiv.finrank_map_eq, hdim]
  -- the gaps in block coordinates
  have hgap1 : (LinearMap.range (toEuclideanLin (Q * (fromRows (1 : Matrix (Fin r) (Fin r) ℂ)
      (0 : Matrix (Fin (n - r)) (Fin r) ℂ)).submatrix e id))).gap
        (Krylov.subspaceIterate (toEuclideanLin A) S₀ k) =
      (LinearMap.range (toEuclideanLin (fromRows (1 : Matrix (Fin r) (Fin r) ℂ)
        (0 : Matrix (Fin (n - r)) (Fin r) ℂ)))).gap
        (Krylov.subspaceIterate (toEuclideanLin M) S k) := by
    exact (gap_congr' (hrange _) hiter).trans (Submodule.gap_map_linearIsometryEquiv Φ _ _)
  have hgap2 : (LinearMap.range (toEuclideanLin (Q * (fromRows (1 : Matrix (Fin r) (Fin r) ℂ)
      (0 : Matrix (Fin (n - r)) (Fin r) ℂ)).submatrix e id))).gap S₀ =
      (LinearMap.range (toEuclideanLin (fromRows (1 : Matrix (Fin r) (Fin r) ℂ)
        (0 : Matrix (Fin (n - r)) (Fin r) ℂ)))).gap S := by
    exact (gap_congr' (hrange _) hSmap.symm).trans (Submodule.gap_map_linearIsometryEquiv Φ _ _)
  have hgap3 : (LinearMap.range (toEuclideanLin
      (Q * (fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (-Xᴴ)).submatrix e id))).gap S₀ =
      (LinearMap.range (toEuclideanLin (fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (-Xᴴ)))).gap S := by
    exact (gap_congr' (hrange _) hSmap.symm).trans (Submodule.gap_map_linearIsometryEquiv Φ _ _)
  rw [hgap1, hgap2, hgap3]
  rw [hgap3] at h0
  refine (gap_subspaceIterate_le_of_blocks hT₁₁u hX hdimS h0 k).trans ?_
  -- the constants
  set Qf := (LinearMap.range (toEuclideanLin (fromRows (1 : Matrix (Fin r) (Fin r) ℂ)
    (0 : Matrix (Fin (n - r)) (Fin r) ℂ)))).gap S / Real.sqrt (1 - (LinearMap.range
      (toEuclideanLin (fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (-Xᴴ)))).gap S ^ 2) with hQf
  have hQf0 : 0 ≤ Qf := div_nonneg (Submodule.gap_nonneg _ _) (Real.sqrt_nonneg _)
  have hXn : lpOpNorm 2 X ≤ ‖T₁₂‖ / sep T₁₁ T₂₂ := by
    refine (l2_opNorm_le_frobenius_norm X).trans ?_
    have h := frobenius_norm_le_div_sep hsep X
    rwa [hX, norm_neg] at h
  set Bs := b + ν / (1 + μ) with hBs
  set As := a - ν / (1 + μ) with hAs
  have hAs0 : 0 < As := by
    rw [hAs, sub_pos, div_lt_iff₀ h1μ]
    linarith
  have hν0 : 0 ≤ ν := (norm_nonneg _).trans hν₁
  have hBs0 : 0 ≤ Bs := add_nonneg hb0 (div_nonneg hν0 h1μ.le)
  have hβ' : lpOpNorm 2 (T₂₂ ^ k) ≤ (1 + μ) ^ (n - r - 1) * Bs ^ k := by
    refine (l2_opNorm_pow_le_of_schur (A := T₂₂) (Q := 1) (T := T₂₂)
      (unitaryGroup (Fin (n - r)) ℂ).one_mem
      (by simp) hT₂₂ hμ k).trans ?_
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (add_nonneg
      (Real.iSup_nonneg fun _ => norm_nonneg _) (div_nonneg (norm_nonneg _) h1μ.le)) ?_ k)
      (pow_nonneg h1μ.le _)
    exact add_le_add (ciSup_le hb) (div_le_div_of_nonneg_right hν₂ h1μ.le)
  have hinf : a ≤ ⨅ i, ‖T₁₁ i i‖ := le_ciInf ha
  have hm : ‖strictUpper T₁₁‖ < (1 + μ) * ⨅ i, ‖T₁₁ i i‖ :=
    lt_of_le_of_lt hν₁ (lt_of_lt_of_le hνa (mul_le_mul_of_nonneg_left hinf h1μ.le))
  have hγ' : lpOpNorm 2 (T₁₁⁻¹ ^ k) ≤ (1 + μ) ^ (r - 1) * (1 / As) ^ k := by
    refine (l2_opNorm_inv_pow_le_of_schur (A := T₁₁) (Q := 1) (T := T₁₁)
      (unitaryGroup (Fin r) ℂ).one_mem
      (by simp) hT₁₁ hμ hm k).trans ?_
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (one_div_pos.2 (sub_pos.2
      ((div_lt_iff₀ h1μ).2 (by rw [mul_comm]; exact hm)))).le ?_ k) (pow_nonneg h1μ.le _)
    refine one_div_le_one_div_of_le hAs0 ?_
    rw [hAs]
    exact sub_le_sub hinf (div_le_div_of_nonneg_right hν₁ h1μ.le)
  have hpow : (1 + μ) ^ (n - r - 1) * (1 + μ) ^ (r - 1) = (1 + μ) ^ (n - 2) := by
    rw [← pow_add]
    congr 1
    omega
  calc (1 + lpOpNorm 2 X) * lpOpNorm 2 (T₂₂ ^ k) * lpOpNorm 2 (T₁₁⁻¹ ^ k) * Qf
      ≤ (1 + ‖T₁₂‖ / sep T₁₁ T₂₂) * ((1 + μ) ^ (n - r - 1) * Bs ^ k) *
          ((1 + μ) ^ (r - 1) * (1 / As) ^ k) * Qf := by
        have hc1 : 0 ≤ 1 + ‖T₁₂‖ / sep T₁₁ T₂₂ := by
          have := div_nonneg (norm_nonneg T₁₂) hsep.le
          linarith
        refine mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul (by linarith) hβ'
          (lpOpNorm_nonneg _ _) hc1) hγ' (lpOpNorm_nonneg _ _) ?_) hQf0
        exact mul_nonneg hc1 (mul_nonneg (pow_nonneg h1μ.le _) (pow_nonneg hBs0 _))
    _ = (1 + μ) ^ (n - 2) * (1 + ‖T₁₂‖ / sep T₁₁ T₂₂) * (Bs / As) ^ k * Qf := by
        rw [← hpow, div_eq_mul_one_div Bs As, mul_pow]
        ring

end OrthogonalIteration

end Matrix
