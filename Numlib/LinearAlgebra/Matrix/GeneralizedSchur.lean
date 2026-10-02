/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Schur` (once the real Schur form is there).
-/
import Mathlib.Data.Nat.Nth
import Mathlib.Topology.Instances.Matrix
import Numlib.Eigen.Pencil
import Numlib.LinearAlgebra.Matrix.QR
import Numlib.LinearAlgebra.Matrix.RealSchur
import Numlib.Topology.Instances.Matrix.UnitaryGroup

/-!
# The generalized real Schur form of a matrix pair

For real square matrices `A`, `B` of the same size there are orthogonal `U`, `Z` with `Uᵀ A Z`
quasi upper triangular (`Matrix.IsQuasiUpperTriangular`: block upper triangular with diagonal
blocks of size `1` or `2`) and `Uᵀ B Z` upper triangular
(`Matrix.exists_orthogonal_pencil_isQuasiUpperTriangular`). This is the real form of the
generalized Schur decomposition of a pencil ([golub1989matrix] Theorem 7.7.2;
[quarteroni2000numerical] §5.9.1, the statement after Property 5.10), and it holds for *every*
pair — no regularity of the pencil `A - λ B` is needed.

## The proof

For a nonsingular `B` the statement reduces to the real Schur form of `B⁻¹ A`
(`Matrix.exists_orthogonal_conj_isQuasiUpperTriangular`) and a QR factorization of `B Z`
(`Matrix.exists_unitary_mul_isUpperTriangular`): `Uᵀ B Z = R` is the triangular factor and
`Uᵀ A Z = R (Zᵀ B⁻¹ A Z)` is triangular times quasi-triangular
(`Matrix.exists_generalizedRealSchur_of_isUnit`, by
`Matrix.IsUpperTriangular.mul_isQuasiUpperTriangular`).

The general case is a limiting argument rather than the deflating-subspace induction of
Golub–Van Loan. `B + ε I` is nonsingular for all small `ε > 0`
(`Matrix.exists_forall_isUnit_det_add_smul_one`: `det (B + t I)` is the characteristic
polynomial of `-B` at `t`), so the pairs `(A, B + ε_k I)`, `ε_k → 0`, have generalized Schur
forms `(U_k, Z_k, p_k)`. Infinitely many `k` share the strict order relation `p_k j < p_k i`
(`Finite.exists_strictMono_forall_eq`: finitely many relations on `Fin n`), so along those `k`
the block-triangularity is for one fixed pattern; and the unitary group is compact, so a further
subsequence has `(U_k, Z_k) → (U, Z)` (`Matrix.exists_tendsto_subseq_of_mem_unitaryGroup₂`). A
vanishing entry of `U_kᴴ M_k Z_k` along convergent `M_k → M` vanishes in the limit
(`Matrix.star_mul_mul_apply_eq_zero_of_tendsto`), applied to `M_k = A` and to
`M_k = B + ε_k I → B`.

The same argument gives the complex generalized Schur form (both factors triangular) of an
arbitrary, possibly singular, complex pair from the regular case
`Matrix.exists_unitary_pencil_isUpperTriangular` of `Numlib/Eigen/Pencil`: this is
`Matrix.exists_generalizedSchur` ([golub2013matrix] Theorem 7.7.1), over any finite linearly
ordered index like its regular case.

## Main results

* `Matrix.exists_orthogonal_pencil_isQuasiUpperTriangular`, `Matrix.exists_generalizedSchur`: the
  two forms.
* The limiting tools, shared with the periodic Schur forms of `Numlib/Eigen/PeriodicSchur`:
  `Matrix.exists_tendsto_subseq_of_mem_unitaryGroup` (a convergent subsequence of a finite family
  of unitary sequences) and its pair form `Matrix.exists_tendsto_subseq_of_mem_unitaryGroup₂`,
  `Matrix.star_mul_mul_apply_eq_zero_of_tendsto` (vanishing entries pass to the limit), and
  `Finite.exists_strictMono_forall_eq` (a sequence in a finite type is constant along a
  subsequence).

## References

[golub1989matrix] §7.7; [quarteroni2000numerical] §5.9.1.
-/

open Filter Topology Matrix

/-- **Infinitely many pigeons, as a subsequence**: a sequence in a finite type is constant along a
strictly increasing subsequence (`Finite.exists_infinite_fiber` enumerated by `Nat.nth`). -/
theorem Finite.exists_strictMono_forall_eq {β : Type*} [Finite β] (f : ℕ → β) :
    ∃ b, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, f (φ k) = b := by
  obtain ⟨b, hb⟩ := Finite.exists_infinite_fiber f
  have hS : (Set.ofPred fun k => f k = b).Infinite := Set.infinite_coe_iff.1 hb
  exact ⟨b, Nat.nth fun k => f k = b, Nat.nth_strictMono hS, Nat.nth_mem_of_infinite hS⟩

namespace Matrix

/-! ### Limits of unitary factors -/

section Limits

variable {m 𝕜 : Type*} [Fintype m] [DecidableEq m] [RCLike 𝕜]

/-- **A convergent subsequence of unitary families**: a sequence of finite families
`U k : ι → Matrix m m 𝕜` of unitary matrices has a subsequence converging, member by member, to a
family of unitary matrices (the unitary group is compact, `Matrix.isCompact_unitaryGroup`). -/
theorem exists_tendsto_subseq_of_mem_unitaryGroup {ι : Type*} [Finite ι]
    {U : ℕ → ι → Matrix m m 𝕜} (hU : ∀ k i, U k i ∈ unitaryGroup m 𝕜) :
    ∃ U₀ : ι → Matrix m m 𝕜, (∀ i, U₀ i ∈ unitaryGroup m 𝕜) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, Tendsto (fun k => U (φ k) i) atTop (𝓝 (U₀ i)) := by
  have : SecondCountableTopology (Matrix m m 𝕜) :=
    inferInstanceAs (SecondCountableTopology (m → m → 𝕜))
  obtain ⟨U₀, hUs, φ, hφ, hlim⟩ :=
    (isCompact_univ_pi fun _ : ι => isCompact_unitaryGroup (n := m) (𝕜 := 𝕜)).tendsto_subseq
      (x := U) fun k => Set.mem_univ_pi.2 fun i => hU k i
  exact ⟨U₀, fun i => (Set.mem_univ_pi.1 hUs) i, φ, hφ, fun i => tendsto_pi_nhds.1 hlim i⟩

/-- **A convergent subsequence of unitary pairs**, the pair form of
`Matrix.exists_tendsto_subseq_of_mem_unitaryGroup`. -/
theorem exists_tendsto_subseq_of_mem_unitaryGroup₂ {U Z : ℕ → Matrix m m 𝕜}
    (hU : ∀ k, U k ∈ unitaryGroup m 𝕜) (hZ : ∀ k, Z k ∈ unitaryGroup m 𝕜) :
    ∃ U₀ ∈ unitaryGroup m 𝕜, ∃ Z₀ ∈ unitaryGroup m 𝕜, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => U (φ k)) atTop (𝓝 U₀) ∧ Tendsto (fun k => Z (φ k)) atTop (𝓝 Z₀) := by
  have : FirstCountableTopology (Matrix m m 𝕜) :=
    inferInstanceAs (FirstCountableTopology (m → m → 𝕜))
  obtain ⟨⟨U₀, Z₀⟩, hUZ, φ, hφ, hlim⟩ :=
    (isCompact_unitaryGroup.prod isCompact_unitaryGroup).tendsto_subseq
      (x := fun k => (U k, Z k)) fun k => ⟨hU k, hZ k⟩
  exact ⟨U₀, hUZ.1, Z₀, hUZ.2, φ, hφ, (continuous_fst.tendsto _).comp hlim,
    (continuous_snd.tendsto _).comp hlim⟩

omit [DecidableEq m] in
/-- **Vanishing entries pass to the limit**: an entry of `star (V k) * M k * W k` that vanishes
for every `k` vanishes for the limits of convergent sequences `V k → V₀`, `M k → M₀`,
`W k → W₀`. -/
theorem star_mul_mul_apply_eq_zero_of_tendsto {V M W : ℕ → Matrix m m 𝕜}
    {V₀ M₀ W₀ : Matrix m m 𝕜} (hV : Tendsto V atTop (𝓝 V₀)) (hM : Tendsto M atTop (𝓝 M₀))
    (hW : Tendsto W atTop (𝓝 W₀)) {i j : m} (hz : ∀ k, (star (V k) * M k * W k) i j = 0) :
    (star V₀ * M₀ * W₀) i j = 0 := by
  have ht : Tendsto (fun k => (star (V k) * M k * W k) i j) atTop
      (𝓝 ((star V₀ * M₀ * W₀) i j)) :=
    ((continuous_id.matrix_elem i j).tendsto _).comp ((hV.star.mul hM).mul hW)
  simp only [hz] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

end Limits

variable {n : ℕ}

/-! ### The nonsingular case -/

/-- **The generalized real Schur form of a pencil with nonsingular `B`**: take `Z` from the real
Schur form of `B⁻¹ A` (`Matrix.exists_orthogonal_conj_isQuasiUpperTriangular`), so that
`Zᵀ B⁻¹ A Z = T` is quasi upper triangular, and `U` from a QR factorization `B Z = U R`
(`Matrix.exists_unitary_mul_isUpperTriangular`); then `Uᵀ B Z = R` is upper triangular and
`Uᵀ A Z = R T` is quasi upper triangular, a triangular matrix times a quasi triangular one. -/
theorem exists_generalizedRealSchur_of_isUnit (A : Matrix (Fin n) (Fin n) ℝ)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : IsUnit B.det) :
    ∃ U ∈ orthogonalGroup (Fin n) ℝ, ∃ Z ∈ orthogonalGroup (Fin n) ℝ,
      (Uᵀ * A * Z).IsQuasiUpperTriangular ∧ (Uᵀ * B * Z).IsUpperTriangular := by
  obtain ⟨Z, hZ, p, hmono, hcard, htri⟩ := exists_orthogonal_conj_isQuasiUpperTriangular (B⁻¹ * A)
  obtain ⟨V, hV, hR⟩ := exists_unitary_mul_isUpperTriangular (B * Z)
  have hZZ : Z * Zᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hZ
  have hVU : Vᵀ ∈ orthogonalGroup (Fin n) ℝ := by
    rw [mem_orthogonalGroup_iff', transpose_transpose]
    exact (mem_orthogonalGroup_iff _ ℝ).1 hV
  refine ⟨Vᵀ, hVU, Z, hZ, ⟨p, hmono, hcard, ?_⟩, ?_⟩
  swap
  · rw [transpose_transpose, Matrix.mul_assoc]; exact hR
  have hAZ : (V * (B * Z)) * (Zᵀ * (B⁻¹ * A) * Z) = Vᵀᵀ * A * Z := by
    rw [transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Z Zᵀ, hZZ, Matrix.one_mul, ← Matrix.mul_assoc B B⁻¹,
      Matrix.mul_nonsing_inv B hB, Matrix.one_mul]
  rw [← hAZ]
  refine BlockTriangular.mul (fun i j hij => hR ?_) htri
  by_contra hji
  exact absurd (hmono (not_lt.1 hji)) (not_le.2 hij)

/-! ### The general case, by perturbation -/

/-- `B + t I` is nonsingular for all small real `t > 0`, over `ℝ` or `ℂ`: `det (B + t I)` is the
characteristic polynomial of `-B` at `t`, which has finitely many roots. -/
theorem exists_forall_isUnit_det_add_smul_one {m 𝕜 : Type*} [Fintype m] [DecidableEq m]
    [RCLike 𝕜] (B : Matrix m m 𝕜) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → IsUnit (B + t • (1 : Matrix m m 𝕜)).det := by
  classical
  have hdet : ∀ t : ℝ, (B + t • (1 : Matrix m m 𝕜)).det =
      (-B).charpoly.eval (t : 𝕜) := by
    intro t
    rw [eval_charpoly, sub_neg_eq_add, add_comm]
    congr 2
    ext i j
    simp [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply,
      RCLike.real_smul_eq_coe_mul]
  have hne : (-B).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  set S := ((-B).charpoly.roots.toFinset.image RCLike.re).filter fun t => 0 < t with hS
  refine ⟨if h : S.Nonempty then S.min' h else 1, ?_, fun t ht0 htδ => ?_⟩
  · split_ifs with h
    · exact (Finset.mem_filter.1 (S.min'_mem h)).2
    · exact one_pos
  · rw [isUnit_iff_ne_zero, hdet]
    intro hroot
    have htS : t ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_image]
      refine ⟨⟨(t : 𝕜), ?_, RCLike.ofReal_re t⟩, ht0⟩
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
      exact hroot
    have hne' : S.Nonempty := ⟨t, htS⟩
    rw [dite_eq_left hne'] at htδ
    exact absurd (S.min'_le t htS) (not_le.2 htδ)

/-- **The generalized real Schur form of an arbitrary real pair** ([quarteroni2000numerical]
§5.9.1, the statement after Property 5.10; Golub–Van Loan Theorem 7.7.2): for real `A`, `B`,
without any regularity hypothesis on the pencil, there are orthogonal `U`, `Z` with `Uᵀ A Z`
quasi upper triangular — block triangular for a monotone block index `p : Fin n → ℕ` with
blocks of size at most `2` — and `Uᵀ B Z` upper triangular.

The nonsingular case is `Matrix.exists_generalizedRealSchur_of_isUnit`. In general `B + ε I` is
nonsingular for all small `ε > 0`, giving orthogonal `U_ε`, `Z_ε` and a pattern `p_ε`; along a
sequence `ε_k → 0`, infinitely many `k` share the relation `p_ε j < p_ε i`
(`Finite.exists_strictMono_forall_eq`), and the orthogonal group being compact a further
subsequence has `U_k → U`, `Z_k → Z` (`Matrix.exists_tendsto_subseq_of_mem_unitaryGroup₂`). The
limits are orthogonal, and the vanishing entries of `U_kᵀ A Z_k` (for the common pattern) and of
`U_kᵀ (B + ε_k I) Z_k` (strictly below the diagonal) pass to the limit
(`Matrix.star_mul_mul_apply_eq_zero_of_tendsto`). -/
theorem exists_orthogonal_pencil_isQuasiUpperTriangular (A B : Matrix (Fin n) (Fin n) ℝ) :
    ∃ U ∈ orthogonalGroup (Fin n) ℝ, ∃ Z ∈ orthogonalGroup (Fin n) ℝ,
      (Uᵀ * A * Z).IsQuasiUpperTriangular ∧ (Uᵀ * B * Z).IsUpperTriangular := by
  obtain ⟨δ, hδ, hδunit⟩ := exists_forall_isUnit_det_add_smul_one B
  obtain ⟨ε, -, hε, hεtend⟩ := exists_seq_strictAnti_tendsto' hδ
  -- the generalized Schur forms of the perturbed pencils
  choose U hU Z hZ hquasi hupp using fun k =>
    exists_generalizedRealSchur_of_isUnit A (hδunit (ε k) (hε k).1 (hε k).2)
  choose p hmono hcard htri using hquasi
  -- a subsequence along which the strict order relation `p_k j < p_k i` is fixed
  obtain ⟨R, φ, hφ, hR⟩ := Finite.exists_strictMono_forall_eq fun k (i j : Fin n) =>
    decide (p k j < p k i)
  have hrel : ∀ k {i j}, p (φ 0) j < p (φ 0) i → p (φ k) j < p (φ k) i := by
    intro k i j h
    have h1 : decide (p (φ k) j < p (φ k) i) = R i j := congrFun (congrFun (hR k) i) j
    have h0 : decide (p (φ 0) j < p (φ 0) i) = R i j := congrFun (congrFun (hR 0) i) j
    exact of_decide_eq_true (h1.trans (h0.symm.trans (decide_eq_true h)))
  -- a further subsequence along which `(U_k, Z_k)` converges
  obtain ⟨U₀, hU₀, Z₀, hZ₀, ψ, hψ, hUlim, hZlim⟩ :=
    exists_tendsto_subseq_of_mem_unitaryGroup₂ (fun k => hU (φ k)) (fun k => hZ (φ k))
  have hlim : ∀ {M : ℕ → Matrix (Fin n) (Fin n) ℝ} {M₀}, Tendsto M atTop (𝓝 M₀) → ∀ {i j},
      (∀ k, ((U (φ (ψ k)))ᵀ * M k * Z (φ (ψ k))) i j = 0) → (U₀ᵀ * M₀ * Z₀) i j = 0 := by
    intro M M₀ hM i j hz
    simp only [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose] at hz ⊢
    exact star_mul_mul_apply_eq_zero_of_tendsto hUlim hM hZlim hz
  have hBlim : Tendsto (fun k => B + ε (φ (ψ k)) • (1 : Matrix (Fin n) (Fin n) ℝ)) atTop
      (𝓝 B) := by
    simpa using tendsto_const_nhds.add
      ((hεtend.comp (hφ.comp hψ).tendsto_atTop).smul_const (1 : Matrix (Fin n) (Fin n) ℝ))
  exact ⟨U₀, hU₀, Z₀, hZ₀, ⟨p (φ 0), hmono _, hcard _,
    fun i j hij => hlim tendsto_const_nhds fun k => htri (φ (ψ k)) (hrel (ψ k) hij)⟩,
    fun i j hij => hlim hBlim fun k => hupp (φ (ψ k)) hij⟩

/-- The generalized real Schur form with the block index of the quasi-triangular factor spelled
out (the former statement of `Matrix.exists_orthogonal_pencil_isQuasiUpperTriangular`). -/
@[deprecated exists_orthogonal_pencil_isQuasiUpperTriangular +typeChanged (since := "2026-09-30")]
theorem exists_generalizedRealSchur (A B : Matrix (Fin n) (Fin n) ℝ) :
    ∃ U ∈ orthogonalGroup (Fin n) ℝ, ∃ Z ∈ orthogonalGroup (Fin n) ℝ, ∃ p : Fin n → ℕ,
      Monotone p ∧ (∀ k, (Finset.univ.filter fun i => p i = k).card ≤ 2) ∧
        (Uᵀ * A * Z).BlockTriangular p ∧ (Uᵀ * B * Z).IsUpperTriangular := by
  obtain ⟨U, hU, Z, hZ, ⟨p, hp, hcard, hA⟩, hB⟩ :=
    exists_orthogonal_pencil_isQuasiUpperTriangular A B
  exact ⟨U, hU, Z, hZ, p, hp, hcard, hA, hB⟩

/-- **The complex generalized Schur form of an arbitrary pair** ([golub2013matrix] Theorem 7.7.1,
existence): for square `A`, `B` over an algebraically closed `RCLike` field (that is, over `ℂ`),
indexed by any finite linear order, with no regularity hypothesis on the pencil, there are
unitary `U`, `Z` with `Uᴴ A Z` and `Uᴴ B Z` both upper triangular. The regular case is
`Matrix.exists_unitary_pencil_isUpperTriangular`; in general `B + ε I` is nonsingular for all
small `ε > 0`, so the pencils `(A, B + ε_k I)` are regular, a subsequence of the unitary factors
`(U_k, Z_k)` converges (`Matrix.exists_tendsto_subseq_of_mem_unitaryGroup₂`), and the vanishing
entries pass to the limit, `B + ε_k I → B` (`Matrix.star_mul_mul_apply_eq_zero_of_tendsto`). The
argument of `Matrix.exists_orthogonal_pencil_isQuasiUpperTriangular`, without the block
pattern. -/
theorem exists_generalizedSchur {m 𝕜 : Type*} [Fintype m] [LinearOrder m] [RCLike 𝕜]
    [IsAlgClosed 𝕜] (A B : Matrix m m 𝕜) :
    ∃ U ∈ unitaryGroup m 𝕜, ∃ Z ∈ unitaryGroup m 𝕜,
      (star U * A * Z).IsUpperTriangular ∧ (star U * B * Z).IsUpperTriangular := by
  obtain ⟨δ, hδ, hδunit⟩ := exists_forall_isUnit_det_add_smul_one B
  obtain ⟨ε, -, hε, hεtend⟩ := exists_seq_strictAnti_tendsto' hδ
  -- the generalized Schur forms of the perturbed, regular, pencils
  choose U hU Z hZ hAtri hBtri using fun k => exists_unitary_pencil_isUpperTriangular
    (isRegularPencil_of_isUnit A (hδunit (ε k) (hε k).1 (hε k).2))
  obtain ⟨U₀, hU₀, Z₀, hZ₀, φ, hφ, hUlim, hZlim⟩ :=
    exists_tendsto_subseq_of_mem_unitaryGroup₂ hU hZ
  have hBlim : Tendsto (fun k => B + ε (φ k) • (1 : Matrix m m 𝕜)) atTop (𝓝 B) := by
    simpa using tendsto_const_nhds.add
      ((hεtend.comp hφ.tendsto_atTop).smul_const (1 : Matrix m m 𝕜))
  exact ⟨U₀, hU₀, Z₀, hZ₀,
    fun i j hij => star_mul_mul_apply_eq_zero_of_tendsto hUlim tendsto_const_nhds hZlim
      fun k => hAtri (φ k) hij,
    fun i j hij => star_mul_mul_apply_eq_zero_of_tendsto hUlim hBlim hZlim
      fun k => hBtri (φ k) hij⟩

end Matrix
