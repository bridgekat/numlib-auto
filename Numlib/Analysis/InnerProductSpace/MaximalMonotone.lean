/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.LinearPMap`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.MetricSpace.Contracting
import Numlib.Analysis.Normed.Operator.Unbounded.Basic

/-!
# Maximal monotone operators on a Hilbert space

Let $H$ be a Hilbert space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let
$A : D(A) \subseteq H \to H$ be a linear operator. The operator $A$ is **monotone** if
$\operatorname{Re} \langle A v, v \rangle \ge 0$ for all $v \in D(A)$, and **maximal monotone** if
moreover $R(I + A) = H$. This file develops the theory of §7.1, §7.3 and §7.4 of
[brezis2011functional]. A maximal monotone operator has a dense domain and a closed graph, and
$I + c A$ is a bijection from $D(A)$ onto $H$ for every $c > 0$. Its inverse, the **resolvent**
$J_c = (I + c A)^{-1}$, satisfies $\|J_c\| \le 1$. The **Yosida approximation**
$A_c = c^{-1} (I - J_c)$ is a bounded monotone operator with $\|A_c\| \le c^{-1}$, and
$A_c v \to A v$ as $c \to 0^+$ for $v \in D(A)$.

The domain $D(A^k)$ is a Hilbert space with the norm $\bigl(\sum_{j \le k} \|A^j u\|^2\bigr)^{1/2}$
when $A$ is closed. The part of $A$ in $D(A^k)$ is again maximal monotone, and symmetric when $A$
is. A symmetric maximal monotone operator is self-adjoint. The adjoint $A^*$ of a maximal monotone
operator is maximal monotone, and $A$ is maximal monotone if and only if $A$ is closed, densely
defined, and both $A$ and $A^*$ are monotone. Finally, for $B = A + c I$ the domains $D(B^k)$ and
$D(A^k)$ coincide as subspaces of $H$, and a bounded linear map transports one Hilbert-space
structure to the other.

## Main definitions

* `LinearPMap.IsMonotone`: $\operatorname{Re} \langle A v, v \rangle \ge 0$ for all $v \in D(A)$.
* `LinearPMap.IsMaximalMonotone`: $A$ is monotone and every $f \in H$ is $u + A u$ for some
  $u \in D(A)$.
* `LinearPMap.resolvent`: the resolvent $J_c = (I + c A)^{-1}$, a bounded operator on $H$.
* `LinearPMap.yosida`: the Yosida approximation $A_c = c^{-1} (I - J_c)$.
* `LinearPMap.powGraph`, `LinearPMap.PowDomain`: the space $D(A^k)$ of tuples
  $(u, A u, \dots, A^k u)$, with the norm $\bigl(\sum_{j \le k} \|A^j u\|^2\bigr)^{1/2}$.
* `LinearPMap.PowDomain.applyL`: the bounded operator $A^j : D(A^k) \to H$ for $j \le k$.
* `LinearPMap.powPart`: the part of $A$ in $D(A^k)$, the operator $u \mapsto A u$ from
  $D(A^{k+1}) \subseteq D(A^k)$ to $D(A^k)$.
* `LinearPMap.IsAddSmulId`: the relation $B = A + c I$ between two operators.
* `LinearPMap.IsAddSmulId.transport`: the bounded linear map $D(B^k) \to D(A^k)$, $(u, B u, \dots,
  B^k u) \mapsto (u, A u, \dots, A^k u)$, for $B = A + c I$.

## Main results

* `LinearPMap.IsMaximalMonotone.dense_domain`, `LinearPMap.IsMaximalMonotone.isClosed`,
  `LinearPMap.IsMaximalMonotone.exists_add_smul_eq`,
  `LinearPMap.IsMaximalMonotone.norm_resolvent_le_one`: the three parts of Proposition 7.1 of
  [brezis2011functional]. The domain is dense, the graph is closed, and for every $c > 0$ the map
  $I + c A$ is a bijection from $D(A)$ onto $H$ with $\|(I + c A)^{-1}\| \le 1$.
* `LinearPMap.IsMaximalMonotone.yosida_apply_eq_apply_resolvent`,
  `LinearPMap.IsMaximalMonotone.yosida_apply_eq_resolvent_apply`,
  `LinearPMap.IsMaximalMonotone.norm_yosida_apply_le_norm_apply`,
  `LinearPMap.IsMaximalMonotone.tendsto_resolvent_apply`,
  `LinearPMap.IsMaximalMonotone.tendsto_yosida_apply`,
  `LinearPMap.IsMaximalMonotone.re_inner_yosida_nonneg`,
  `LinearPMap.IsMaximalMonotone.norm_yosida_apply_le`: the properties of the Yosida approximation in
  Proposition 7.2 of [brezis2011functional].
* `LinearPMap.IsClosed.completeSpace_powDomain`: $D(A^k)$ is a Hilbert space when $A$ is closed.
* `LinearPMap.IsMaximalMonotone.powPart`, `LinearPMap.IsFormalAdjoint.powPart`: the part of $A$ in
  $D(A^k)$ is maximal monotone, and symmetric when $A$ is.
* `LinearPMap.IsMaximalMonotone.dense_range_castL`: $D(A^{k+1})$ is dense in $D(A^k)$ for the norm
  of $D(A^k)$; for $k = 1$ this is Lemma 7.2 of [brezis2011functional].
* `LinearPMap.IsMaximalMonotone.isSelfAdjoint_of_isFormalAdjoint`: a symmetric maximal monotone
  operator is self-adjoint (Proposition 7.6 of [brezis2011functional]).
* `LinearPMap.IsMaximalMonotone.adjoint`,
  `LinearPMap.isMaximalMonotone_iff_isClosed_dense_isMonotone`,
  `LinearPMap.isMaximalMonotone_iff_adjoint`: the characterizations of maximal monotonicity by the
  adjoint in Remark 8 of Chapter 7 of [brezis2011functional].
* `LinearPMap.IsAddSmulId.exists_applyL_zero_eq_iff`: for $B = A + c I$, the domains $D(B^k)$ and
  $D(A^k)$ are the same subspace of $H$.

## Implementation notes

* An operator $A : D(A) \subseteq H \to H$ is Mathlib's partially defined linear map
  `A : H →ₗ.[𝕜] H`. Symmetric operators are those with `A.IsFormalAdjoint A`, and self-adjoint
  operators are those with `IsSelfAdjoint A`, that is $A^* = A$, where $A^*$ is Mathlib's
  `LinearPMap.adjoint`, written `A†`.
* The whole file is over a field with `RCLike 𝕜`, with the condition
  $\operatorname{Re} \langle A v, v \rangle \ge 0$. The proofs are those of the real case, Mathlib's
  adjoint and self-adjointness are over `RCLike`, and the skew-adjoint case
  $\operatorname{Re} \langle A v, v \rangle = 0$ is included. The evolution equation $u' + A u = 0$,
  which differentiates in time, is in `Numlib.Analysis.ODE.HilleYosida`, over $\mathbb{R}$.
* The operator $I + \lambda A$ of the source is `LinearMap.id +ᵥ ((λ : 𝕜) • A)`, whose domain is
  `A.domain` by definition. `LinearPMap.IsMaximalMonotone.range_id_vadd_eq_top` states the range
  condition in this form.
* The resolvent and the Yosida approximation are total functions of $A$ and $c$. The resolvent is a
  bounded operator $J$ with $J f \in D(A)$ and $J f + c A (J f) = f$ for all $f$ if one exists, and
  $0$ otherwise, in the style of `LinearPMap.adjoint`. Their properties are stated for a maximal
  monotone $A$ and $c > 0$.
* The space $D(A^k)$ is the submodule `LinearPMap.powGraph` of the $\ell^2$ product
  `PiLp 2 (Fin (k + 1) → H)`: the tuples whose consecutive entries are related by $A$. Its norm and
  inner product are those of `PiLp` and `Submodule`, and so they are exactly the norm and inner
  product of the source. `A.PowDomain 1` is $D(A)$ with the graph norm, and `A.PowDomain 0` is $H$.
* No operator $A^k : H \to H$ is defined, because Mathlib's `LinearPMap.comp` requires the whole
  range of the inner operator to lie in the domain of the outer one. Only the domains with their
  norms are needed.
* The part of $A$ in $D(A^k)$ is the operator $A_1 : D(A^2) \subseteq D(A) \to D(A)$ of the proof of
  Theorem 7.5 of [brezis2011functional] and the operator $\tilde A : D(A^k) \subseteq D(A^{k-1}) \to
  D(A^{k-1})$ of the proof of Theorem 7.7, in one definition. The regularity theorems for the
  evolution equation are then inductions on one theorem.
* The transport between $D((A + cI)^k)$ and $D(A^k)$ lets Theorem 7.5 of [brezis2011functional],
  applied to $A + I$ for the wave operator of Chapter 10, make statements about $D(A^k)$.
-/

open RCLike Filter Topology Metric WithLp
open scoped InnerProductSpace

noncomputable section

namespace LinearPMap

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### Monotone and maximal monotone operators -/

/-- An operator $A : D(A) \subseteq H \to H$ is **monotone** if
$$\operatorname{Re} \langle A v, v \rangle \ge 0 \quad \text{for every } v \in D(A).$$
This is the definition of §7.1 of [brezis2011functional]; other authors say "accretive".

Over $\mathbb{K} = \mathbb{R}$ the real part is the identity. -/
def IsMonotone (A : H →ₗ.[𝕜] H) : Prop :=
  ∀ v : A.domain, 0 ≤ re ⟪A v, (v : H)⟫

/-- An operator $A : D(A) \subseteq H \to H$ is **maximal monotone** if it is monotone and $I + A$
maps $D(A)$ onto $H$: for every $f \in H$ there is $u \in D(A)$ with $u + A u = f$. This is the
definition of §7.1 of [brezis2011functional]. -/
structure IsMaximalMonotone (A : H →ₗ.[𝕜] H) : Prop where
  /-- A maximal monotone operator is monotone. -/
  isMonotone : A.IsMonotone
  /-- The range condition $R(I + A) = H$: every $f \in H$ is $u + A u$ for some $u \in D(A)$. -/
  exists_add_apply_eq : ∀ f : H, ∃ u : A.domain, (u : H) + A u = f

variable {A : H →ₗ.[𝕜] H}

/-- If $A$ is maximal monotone, then the operator $I + A$ has range $H$.

This is the range condition in the form of the source, with $I + A$ written as Mathlib's
`LinearMap.id +ᵥ A`, an operator with domain $D(A)$. -/
theorem IsMaximalMonotone.range_id_vadd_eq_top (hA : A.IsMaximalMonotone) :
    LinearMap.range ((LinearMap.id : H →ₗ[𝕜] H) +ᵥ A).toFun = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro f
  obtain ⟨u, hu⟩ := hA.exists_add_apply_eq f
  exact ⟨u, hu⟩

/-- If $A$ is monotone and the operator $I + A$, written `LinearMap.id +ᵥ A`, has range $H$, then
$A$ is maximal monotone. -/
theorem IsMaximalMonotone.of_range_id_vadd_eq_top (hA : A.IsMonotone)
    (h : LinearMap.range ((LinearMap.id : H →ₗ[𝕜] H) +ᵥ A).toFun = ⊤) : A.IsMaximalMonotone :=
  ⟨hA, fun f => by
    obtain ⟨u, hu⟩ := LinearMap.range_eq_top.1 h f
    exact ⟨u, hu⟩⟩

/-- For every operator $A$, every real $c$ and every $u \in D(A)$,
$$\operatorname{Re} \langle u + c A u, u \rangle = \|u\|^2 + c \operatorname{Re} \langle A u, u
  \rangle.$$
-/
theorem re_inner_add_smul_apply_self (A : H →ₗ.[𝕜] H) (c : ℝ) (u : A.domain) :
    re ⟪(u : H) + (c : 𝕜) • A u, (u : H)⟫ = ‖(u : H)‖ ^ 2 + c * re ⟪A u, (u : H)⟫ := by
  rw [inner_add_left, _root_.map_add, inner_self_eq_norm_sq, inner_smul_left, conj_ofReal,
    re_ofReal_mul]

/-- Let $A$ be monotone and let $c \ge 0$. Then for every $u \in D(A)$,
$$\|u\| \le \|u + c A u\|.$$

The proof is $\|u\|^2 \le \|u\|^2 + c \operatorname{Re} \langle A u, u \rangle =
\operatorname{Re} \langle u + c A u, u \rangle \le \|u + c A u\| \|u\|$, as in the proof of
Proposition 7.1(b) of [brezis2011functional]. -/
theorem IsMonotone.norm_le_norm_add_smul (hA : A.IsMonotone) {c : ℝ} (hc : 0 ≤ c)
    (u : A.domain) : ‖(u : H)‖ ≤ ‖(u : H) + (c : 𝕜) • A u‖ := by
  have h1 : ‖(u : H)‖ ^ 2 ≤ re ⟪(u : H) + (c : 𝕜) • A u, (u : H)⟫ := by
    rw [re_inner_add_smul_apply_self]
    exact le_add_of_nonneg_right (mul_nonneg hc (hA u))
  have h2 := re_inner_le_norm (𝕜 := 𝕜) ((u : H) + (c : 𝕜) • A u) (u : H)
  rcases (norm_nonneg (u : H)).eq_or_lt with h0 | h0
  · rw [← h0]
    exact norm_nonneg _
  · have : ‖(u : H)‖ * ‖(u : H)‖ ≤ ‖(u : H) + (c : 𝕜) • A u‖ * ‖(u : H)‖ := by
      rw [← sq]
      exact h1.trans h2
    exact le_of_mul_le_mul_right this h0

/-- Let $A$ be monotone and let $c \ge 0$. Then the map $u \mapsto u + c A u$ is injective on
$D(A)$. This is the uniqueness part of Proposition 7.1(b) and (c) of [brezis2011functional]. -/
theorem IsMonotone.injective_add_smul (hA : A.IsMonotone) {c : ℝ} (hc : 0 ≤ c) :
    Function.Injective fun u : A.domain => (u : H) + (c : 𝕜) • A u := by
  intro u v huv
  have h := hA.norm_le_norm_add_smul hc (u - v)
  simp only at huv
  rw [map_sub, Submodule.coe_sub, smul_sub,
    show (u : H) - v + ((c : 𝕜) • A u - (c : 𝕜) • A v) =
      ((u : H) + (c : 𝕜) • A u) - ((v : H) + (c : 𝕜) • A v) by abel,
    huv, sub_self, norm_zero] at h
  exact Subtype.ext (sub_eq_zero.1 (norm_le_zero_iff.1 h))

/-- Let $H$ be a Hilbert space and let $A$ be maximal monotone. Then $D(A)$ is dense in $H$. This is
Proposition 7.1(a) of [brezis2011functional].

If $f$ is orthogonal to $D(A)$, solve $v_0 + A v_0 = f$. Then $0 = \operatorname{Re} \langle
v_0, f \rangle = \|v_0\|^2 + \operatorname{Re} \langle A v_0, v_0 \rangle \ge \|v_0\|^2$, so
$v_0 = 0$ and $f = 0$. -/
theorem IsMaximalMonotone.dense_domain [CompleteSpace H] (hA : A.IsMaximalMonotone) :
    Dense (A.domain : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro f hf
  rw [Submodule.mem_orthogonal] at hf
  obtain ⟨v, hv⟩ := hA.exists_add_apply_eq f
  have h1 : ⟪(v : H), f⟫ = 0 := hf v v.2
  have h2 : ‖(v : H)‖ ^ 2 ≤ re ⟪(v : H), f⟫ := by
    rw [← hv, inner_add_right, _root_.map_add, inner_self_eq_norm_sq, inner_re_symm]
    exact le_add_of_nonneg_right (hA.isMonotone v)
  rw [h1, _root_.map_zero] at h2
  have hv0 : v = 0 :=
    Subtype.ext (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1
      (le_antisymm h2 (sq_nonneg _))))
  rw [← hv, hv0, map_zero, Submodule.coe_zero, add_zero]

/-- Let $H$ be a Hilbert space and let $A$ be monotone. Suppose that for some $c_0 > 0$ the map
$I + c_0 A$ sends $D(A)$ onto $H$. Then for every $c > c_0 / 2$ and every $f \in H$ there is
$u \in D(A)$ with $u + c A u = f$.

This is the contraction step of the proof of Proposition 7.1(c) of [brezis2011functional]. The
equation $u + c A u = f$ is the fixed-point equation
$$u = J_{c_0}\Bigl(\frac{c_0}{c} f + \Bigl(1 - \frac{c_0}{c}\Bigr) u\Bigr),$$
whose right-hand side is a contraction of $H$ with constant $|1 - c_0 / c| < 1$, because
$J_{c_0} = (I + c_0 A)^{-1}$ is nonexpansive. -/
theorem IsMonotone.exists_add_smul_eq_of_exists_add_smul_eq [CompleteSpace H]
    (hA : A.IsMonotone) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (h : ∀ f : H, ∃ u : A.domain, (u : H) + (c₀ : 𝕜) • A u = f) {c : ℝ} (hc : c₀ / 2 < c)
    (f : H) : ∃ u : A.domain, (u : H) + (c : 𝕜) • A u = f := by
  choose J hJ using h
  have hc' : 0 < c := by linarith
  -- the inverse `J` of `I + c₀ A` is nonexpansive
  have hlip : ∀ x y : H, ‖(J x : H) - J y‖ ≤ ‖x - y‖ := fun x y => by
    have := hA.norm_le_norm_add_smul hc₀.le (J x - J y)
    rwa [map_sub, Submodule.coe_sub, smul_sub,
      show (J x : H) - J y + ((c₀ : 𝕜) • A (J x) - (c₀ : 𝕜) • A (J y)) =
        ((J x : H) + (c₀ : 𝕜) • A (J x)) - ((J y : H) + (c₀ : 𝕜) • A (J y)) by abel,
      hJ, hJ] at this
  set θ : ℝ := c₀ / c with hθ
  have hθ0 : 0 < θ := div_pos hc₀ hc'
  have hθ2 : θ < 2 := by
    rw [hθ, div_lt_iff₀ hc']
    linarith
  -- the contraction
  let Φ : H → H := fun u => J ((θ : 𝕜) • f + ((1 - θ : ℝ) : 𝕜) • u)
  have hΦ : LipschitzWith (Real.toNNReal |1 - θ|) Φ := by
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    simp only [Φ, dist_eq_norm, Real.coe_toNNReal _ (abs_nonneg _)]
    calc ‖(J ((θ : 𝕜) • f + ((1 - θ : ℝ) : 𝕜) • u) : H) -
          J ((θ : 𝕜) • f + ((1 - θ : ℝ) : 𝕜) • v)‖
        ≤ ‖((θ : 𝕜) • f + ((1 - θ : ℝ) : 𝕜) • u) - ((θ : 𝕜) • f + ((1 - θ : ℝ) : 𝕜) • v)‖ :=
          hlip _ _
      _ = |1 - θ| * ‖u - v‖ := by
          rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, norm_ofReal]
  have hcontr : ContractingWith (Real.toNNReal |1 - θ|) Φ := by
    refine ⟨Real.toNNReal_lt_one.2 ?_, hΦ⟩
    rw [abs_lt]
    constructor <;> linarith
  obtain ⟨u, hu⟩ : ∃ u : H, Φ u = u := ⟨_, hcontr.fixedPoint_isFixedPt⟩
  set w : H := (θ : 𝕜) • f + ((1 - θ : ℝ) : 𝕜) • u with hw
  have hJu : (J w : H) = u := hu
  have hspec : (J w : H) + (c₀ : 𝕜) • A (J w) = w := hJ w
  rw [hJu] at hspec
  refine ⟨J w, ?_⟩
  rw [hJu]
  have hθc : (c₀ : 𝕜) = (θ : 𝕜) * (c : 𝕜) := by
    rw [← ofReal_mul, hθ, div_mul_cancel₀ _ hc'.ne']
  have hθne : (θ : 𝕜) ≠ 0 := by exact_mod_cast hθ0.ne'
  apply smul_right_injective H hθne
  simp only
  rw [smul_add, smul_smul, ← hθc]
  have h1 : ((1 - θ : ℝ) : 𝕜) • u = u - (θ : 𝕜) • u := by
    rw [ofReal_sub, ofReal_one, sub_smul, one_smul]
  have hspec' : u + (c₀ : 𝕜) • A (J w) = (θ : 𝕜) • f + (u - (θ : 𝕜) • u) := by
    rw [hspec, hw, h1]
  calc (θ : 𝕜) • u + (c₀ : 𝕜) • A (J w) = (u + (c₀ : 𝕜) • A (J w)) - (u - (θ : 𝕜) • u) := by
        abel
    _ = (θ : 𝕜) • f := by rw [hspec']; abel

/-- Let $H$ be a Hilbert space and let $A$ be maximal monotone. Then for every $c > 0$ and every
$f \in H$ there is $u \in D(A)$ with $u + c A u = f$: the map $I + c A$ sends $D(A)$ onto $H$.
This is the surjectivity part of Proposition 7.1(c) of [brezis2011functional].

The proof starts from $c_0 = 1$. By induction, the contraction step
`LinearPMap.IsMonotone.exists_add_smul_eq_of_exists_add_smul_eq` gives every $c > 2^{-n}$. -/
theorem IsMaximalMonotone.exists_add_smul_eq [CompleteSpace H] (hA : A.IsMaximalMonotone)
    {c : ℝ} (hc : 0 < c) (f : H) : ∃ u : A.domain, (u : H) + (c : 𝕜) • A u = f := by
  suffices h : ∀ n : ℕ, ∀ c : ℝ, (1 / 2 : ℝ) ^ n < c →
      ∀ f : H, ∃ u : A.domain, (u : H) + (c : 𝕜) • A u = f by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hc (by norm_num : (1 / 2 : ℝ) < 1)
    exact h n c hn f
  intro n
  induction n with
  | zero =>
    intro c hc f
    rw [pow_zero] at hc
    refine hA.isMonotone.exists_add_smul_eq_of_exists_add_smul_eq one_pos (fun f => ?_)
      (by linarith) f
    obtain ⟨u, hu⟩ := hA.exists_add_apply_eq f
    exact ⟨u, by rwa [ofReal_one, one_smul]⟩
  | succ n ih =>
    intro c hc f
    have h2 : (1 / 2 : ℝ) ^ n < 2 * c := by
      rw [pow_succ] at hc
      linarith
    exact hA.isMonotone.exists_add_smul_eq_of_exists_add_smul_eq
      (c₀ := ((1 / 2 : ℝ) ^ n + 2 * c) / 2)
      (by have := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n; linarith) (ih _ (by linarith))
      (by linarith) f

/-! ### The resolvent -/

variable (A) in
open scoped Classical in
/-- The **resolvent** $J_c = (I + c A)^{-1}$ of $A$ at $c \in \mathbb{R}$, defined in §7.1 of
[brezis2011functional]. If there is a bounded operator $J$ on $H$ with $J f \in D(A)$ and
$J f + c A (J f) = f$ for every $f \in H$, then $J_c$ is such an operator; otherwise $J_c = 0$.

Such an operator is unique as soon as $I + c A$ is injective, in particular for a monotone $A$
and $c \ge 0$. The properties of $J_c$ are stated for a maximal monotone $A$ and $c > 0$, where
$J_c$ exists by `LinearPMap.IsMaximalMonotone.exists_resolvent`. -/
def resolvent (c : ℝ) : H →L[𝕜] H :=
  if h : ∃ J : H →L[𝕜] H, ∀ f : H, ∃ hf : J f ∈ A.domain, J f + (c : 𝕜) • A ⟨J f, hf⟩ = f then
    h.choose
  else 0

/-- Let $H$ be a Hilbert space, let $A$ be maximal monotone and let $c > 0$. Then there is a bounded
operator $J$ on $H$ with $J f \in D(A)$ and $J f + c A (J f) = f$ for every $f \in H$: the
operator $I + c A$ has a bounded inverse.

The solution comes from `LinearPMap.IsMaximalMonotone.exists_add_smul_eq`. It is linear because
$I + c A$ is injective (`LinearPMap.IsMonotone.injective_add_smul`), and bounded by
`LinearPMap.IsMonotone.norm_le_norm_add_smul`. -/
theorem IsMaximalMonotone.exists_resolvent [CompleteSpace H] (hA : A.IsMaximalMonotone) {c : ℝ}
    (hc : 0 < c) :
    ∃ J : H →L[𝕜] H, ∀ f : H, ∃ hf : J f ∈ A.domain, J f + (c : 𝕜) • A ⟨J f, hf⟩ = f := by
  choose g hg using hA.exists_add_smul_eq hc
  have hinj := hA.isMonotone.injective_add_smul hc.le
  let L : H →ₗ[𝕜] H :=
    { toFun := fun f => (g f : H)
      map_add' := fun x y => by
        have : g (x + y) = g x + g y := by
          apply hinj
          simp only
          calc (g (x + y) : H) + (c : 𝕜) • A (g (x + y)) = x + y := hg _
            _ = ((g x : H) + (c : 𝕜) • A (g x)) + ((g y : H) + (c : 𝕜) • A (g y)) := by
                rw [hg, hg]
            _ = (g x + g y : A.domain) + (c : 𝕜) • A (g x + g y) := by
                rw [Submodule.coe_add, map_add, smul_add]
                abel
        simp only [this, Submodule.coe_add]
      map_smul' := fun a x => by
        have : g (a • x) = a • g x := by
          apply hinj
          simp only
          calc (g (a • x) : H) + (c : 𝕜) • A (g (a • x)) = a • x := hg _
            _ = a • ((g x : H) + (c : 𝕜) • A (g x)) := by rw [hg]
            _ = (a • g x : A.domain) + (c : 𝕜) • A (a • g x) := by
                rw [Submodule.coe_smul, map_smul, smul_add, smul_comm]
        simp only [this, Submodule.coe_smul, RingHom.id_apply] }
  refine ⟨L.mkContinuous 1 fun f => ?_, fun f => ⟨(g f).2, hg f⟩⟩
  rw [one_mul]
  have := hA.isMonotone.norm_le_norm_add_smul hc.le (g f)
  rwa [hg f] at this

/-- Let $H$ be a Hilbert space, let $A$ be maximal monotone and let $c > 0$. Then for every
$f \in H$, $J_c f \in D(A)$ and $J_c f + c A (J_c f) = f$. -/
theorem IsMaximalMonotone.resolvent_spec [CompleteSpace H] (hA : A.IsMaximalMonotone) {c : ℝ}
    (hc : 0 < c) (f : H) :
    ∃ hf : A.resolvent c f ∈ A.domain, A.resolvent c f + (c : 𝕜) • A ⟨A.resolvent c f, hf⟩ = f := by
  have h := hA.exists_resolvent hc
  unfold resolvent
  rw [dite_eq_left h]
  exact h.choose_spec f

/-- Let $H$ be a Hilbert space, let $A$ be maximal monotone and let $c > 0$. Then $J_c f \in D(A)$
for every $f \in H$. -/
theorem IsMaximalMonotone.resolvent_apply_mem_domain [CompleteSpace H] (hA : A.IsMaximalMonotone)
    {c : ℝ} (hc : 0 < c) (f : H) : A.resolvent c f ∈ A.domain :=
  (hA.resolvent_spec hc f).fst

/-- Let $H$ be a Hilbert space, let $A$ be maximal monotone and let $c > 0$. Then for every
$f \in H$,
$$J_c f + c A (J_c f) = f,$$
so the resolvent is a right inverse of $I + c A$. -/
theorem IsMaximalMonotone.resolvent_add_smul_apply [CompleteSpace H] (hA : A.IsMaximalMonotone)
    {c : ℝ} (hc : 0 < c) (f : H) :
    A.resolvent c f + (c : 𝕜) • A ⟨A.resolvent c f, hA.resolvent_apply_mem_domain hc f⟩ = f :=
  (hA.resolvent_spec hc f).snd

/-- Let $H$ be a Hilbert space, let $A$ be maximal monotone and let $c > 0$. Then for $u \in D(A)$
and $f \in H$,
$$J_c f = u \iff u + c A u = f.$$
-/
theorem IsMaximalMonotone.resolvent_eq_iff [CompleteSpace H] (hA : A.IsMaximalMonotone) {c : ℝ}
    (hc : 0 < c) (u : A.domain) (f : H) :
    A.resolvent c f = u ↔ (u : H) + (c : 𝕜) • A u = f := by
  have h := hA.resolvent_add_smul_apply hc f
  constructor
  · intro hu
    have : (⟨A.resolvent c f, hA.resolvent_apply_mem_domain hc f⟩ : A.domain) = u :=
      Subtype.ext hu
    rw [← this]
    exact h
  · intro hu
    have := hA.isMonotone.injective_add_smul hc.le
      (a₁ := ⟨A.resolvent c f, hA.resolvent_apply_mem_domain hc f⟩) (a₂ := u) (h.trans hu.symm)
    exact congrArg Subtype.val this

/-- Let $H$ be a Hilbert space, let $A$ be maximal monotone and let $c > 0$. Then
$J_c (u + c A u) = u$ for every $u \in D(A)$, so the resolvent is a left inverse of $I + c A$. -/
theorem IsMaximalMonotone.resolvent_apply_add_smul [CompleteSpace H] (hA : A.IsMaximalMonotone)
    {c : ℝ} (hc : 0 < c) (u : A.domain) :
    A.resolvent c ((u : H) + (c : 𝕜) • A u) = u :=
  (hA.resolvent_eq_iff hc u _).2 rfl

/-- Let $H$ be a Hilbert space, let $A$ be maximal monotone and let $c > 0$. Then
$\|J_c f\| \le \|f\|$ for every $f \in H$. This is the bound of Proposition 7.1(c) of
[brezis2011functional], pointwise. -/
theorem IsMaximalMonotone.norm_resolvent_apply_le [CompleteSpace H] (hA : A.IsMaximalMonotone)
    {c : ℝ} (hc : 0 < c) (f : H) : ‖A.resolvent c f‖ ≤ ‖f‖ := by
  have := hA.isMonotone.norm_le_norm_add_smul hc.le
    ⟨A.resolvent c f, hA.resolvent_apply_mem_domain hc f⟩
  rwa [hA.resolvent_add_smul_apply hc f] at this

/-- Let $H$ be a Hilbert space, let $A$ be maximal monotone and let $c > 0$. Then the resolvent has
operator norm $\|J_c\| \le 1$. This is the bound of Proposition 7.1(c) of
[brezis2011functional]. -/
theorem IsMaximalMonotone.norm_resolvent_le_one [CompleteSpace H] (hA : A.IsMaximalMonotone)
    {c : ℝ} (hc : 0 < c) : ‖A.resolvent c‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [one_mul]
    exact hA.norm_resolvent_apply_le hc f

/-- Let $H$ be a Hilbert space. A maximal monotone operator $A$ on $H$ is closed. This is
Proposition 7.1(b) of [brezis2011functional].

The graph of $A$ is the set $\{(x, y) : x = J_1 (x + y)\}$, the preimage of the diagonal under a
continuous map. -/
theorem IsMaximalMonotone.isClosed [CompleteSpace H] (hA : A.IsMaximalMonotone) : A.IsClosed := by
  have hgraph : (A.graph : Set (H × H)) = {p | p.1 = A.resolvent 1 (p.1 + p.2)} := by
    ext ⟨x, y⟩
    simp only [SetLike.mem_coe, mem_graph_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, rfl, rfl⟩
      have := hA.resolvent_apply_add_smul one_pos u
      rw [ofReal_one, one_smul] at this
      exact this.symm
    · intro hx
      set u : A.domain := ⟨A.resolvent 1 (x + y), hA.resolvent_apply_mem_domain one_pos (x + y)⟩
      have hu : (u : H) = x := hx.symm
      have h := hA.resolvent_add_smul_apply one_pos (x + y)
      rw [ofReal_one, one_smul] at h
      refine ⟨u, hu, ?_⟩
      calc A u = ((u : H) + A u) - (u : H) := by abel
        _ = y := by rw [h, hu]; abel
  change _root_.IsClosed (A.graph : Set (H × H))
  rw [hgraph]
  exact isClosed_eq continuous_fst
    ((A.resolvent 1).continuous.comp (continuous_fst.add continuous_snd))

/-- Let $H$ be a Hilbert space, let $A$ be maximal monotone and let $c > 0$. Then $c A$ is maximal
monotone. This is Remark 1 of Chapter 7 of [brezis2011functional]. -/
theorem IsMaximalMonotone.smul [CompleteSpace H] (hA : A.IsMaximalMonotone) {c : ℝ}
    (hc : 0 < c) : ((c : 𝕜) • A).IsMaximalMonotone where
  isMonotone v := by
    change 0 ≤ re ⟪(c : 𝕜) • A v, (v : H)⟫
    rw [inner_smul_left, conj_ofReal, re_ofReal_mul]
    exact mul_nonneg hc.le (hA.isMonotone v)
  exists_add_apply_eq f := by
    obtain ⟨u, hu⟩ := hA.exists_add_smul_eq hc f
    exact ⟨u, hu⟩

/-! ### The Yosida approximation -/

variable (A) in
/-- The **Yosida approximation** of $A$ at $c \in \mathbb{R}$ is the bounded operator
$$A_c = c^{-1} (I - J_c),$$
defined in §7.1 of [brezis2011functional].

Like the resolvent, it is a total function of $A$ and $c$. At $c = 0$ it is $0$, because Lean's
$0^{-1}$ is $0$. -/
def yosida (c : ℝ) : H →L[𝕜] H :=
  ((c⁻¹ : ℝ) : 𝕜) • (ContinuousLinearMap.id 𝕜 H - A.resolvent c)

variable (A) in
/-- For every $c \in \mathbb{R}$ and $v \in H$, $A_c v = c^{-1} (v - J_c v)$. -/
theorem yosida_apply (c : ℝ) (v : H) :
    A.yosida c v = ((c⁻¹ : ℝ) : 𝕜) • (v - A.resolvent c v) :=
  rfl

variable (A) in
/-- For $c \ne 0$ and $v \in H$, $c A_c v = v - J_c v$. -/
theorem smul_yosida_apply {c : ℝ} (hc : c ≠ 0) (v : H) :
    (c : 𝕜) • A.yosida c v = v - A.resolvent c v := by
  rw [yosida_apply, smul_smul, ← ofReal_mul, mul_inv_cancel₀ hc, ofReal_one, one_smul]

/-- Let $H$ be a Hilbert space, let $A$ be maximal monotone and let $c > 0$. Then for every
$v \in H$,
$$A_c v = A (J_c v).$$
This is Proposition 7.2(a₁) of [brezis2011functional]. It is a rearrangement of
$J_c v + c A (J_c v) = v$. -/
theorem IsMaximalMonotone.yosida_apply_eq_apply_resolvent [CompleteSpace H]
    (hA : A.IsMaximalMonotone) {c : ℝ} (hc : 0 < c) (v : H) :
    A.yosida c v = A ⟨A.resolvent c v, hA.resolvent_apply_mem_domain hc v⟩ := by
  rw [yosida_apply, ← eq_sub_of_add_eq' (hA.resolvent_add_smul_apply hc v), smul_smul,
    ← ofReal_mul, inv_mul_cancel₀ hc.ne', ofReal_one, one_smul]

/-- Let $H$ be a Hilbert space, let $A$ be maximal monotone and let $c > 0$. Then the resolvent
commutes with $A$ on $D(A)$: for every $u \in D(A)$,
$$J_c (A u) = A (J_c u).$$

Both sides solve $w + c A w = A u$. For the right-hand side, $A (J_c u) = c^{-1} (u - J_c u)$
lies in $D(A)$. This is the argument of the proof of Proposition 7.2(a₂) of
[brezis2011functional]. -/
theorem IsMaximalMonotone.resolvent_apply_comm [CompleteSpace H] (hA : A.IsMaximalMonotone)
    {c : ℝ} (hc : 0 < c) (u : A.domain) :
    A.resolvent c (A u) = A ⟨A.resolvent c u, hA.resolvent_apply_mem_domain hc u⟩ := by
  set j : A.domain := ⟨A.resolvent c u, hA.resolvent_apply_mem_domain hc u⟩ with hj
  have h : (j : H) + (c : 𝕜) • A j = u := hA.resolvent_add_smul_apply hc u
  set w : A.domain := ((c⁻¹ : ℝ) : 𝕜) • (u - j) with hw
  have hwH : (w : H) = A j := by
    rw [hw, Submodule.coe_smul, Submodule.coe_sub, ← eq_sub_of_add_eq' h, smul_smul,
      ← ofReal_mul, inv_mul_cancel₀ hc.ne', ofReal_one, one_smul]
  have hAw : A w = ((c⁻¹ : ℝ) : 𝕜) • (A u - A j) := by rw [hw, map_smul, map_sub]
  have key : (w : H) + (c : 𝕜) • A w = A u := by
    rw [hwH, hAw, smul_smul, ← ofReal_mul, mul_inv_cancel₀ hc.ne', ofReal_one, one_smul]
    abel
  rw [(hA.resolvent_eq_iff hc w (A u)).2 key, hwH]

/-- Let $H$ be a Hilbert space, let $A$ be maximal monotone and let $c > 0$. Then for every
$v \in D(A)$,
$$A_c v = J_c (A v).$$
This is Proposition 7.2(a₂) of [brezis2011functional]. -/
theorem IsMaximalMonotone.yosida_apply_eq_resolvent_apply [CompleteSpace H]
    (hA : A.IsMaximalMonotone) {c : ℝ} (hc : 0 < c) (v : A.domain) :
    A.yosida c v = A.resolvent c (A v) := by
  rw [hA.yosida_apply_eq_apply_resolvent hc, hA.resolvent_apply_comm hc]

/-- Let $H$ be a Hilbert space, let $A$ be maximal monotone and let $c > 0$. Then for every
$v \in D(A)$,
$$\|A_c v\| \le \|A v\|.$$
This is Proposition 7.2(b) of [brezis2011functional]. -/
theorem IsMaximalMonotone.norm_yosida_apply_le_norm_apply [CompleteSpace H]
    (hA : A.IsMaximalMonotone) {c : ℝ} (hc : 0 < c) (v : A.domain) :
    ‖A.yosida c v‖ ≤ ‖A v‖ := by
  rw [hA.yosida_apply_eq_resolvent_apply hc]
  exact hA.norm_resolvent_apply_le hc _

/-- Let $H$ be a Hilbert space, let $A$ be maximal monotone and let $c > 0$. Then for every
$v \in D(A)$,
$$\|v - J_c v\| \le c \|A v\|.$$
This is the rate in the proof of Proposition 7.2(c) of [brezis2011functional]. -/
theorem IsMaximalMonotone.norm_sub_resolvent_apply_le [CompleteSpace H]
    (hA : A.IsMaximalMonotone) {c : ℝ} (hc : 0 < c) (v : A.domain) :
    ‖(v : H) - A.resolvent c v‖ ≤ c * ‖A v‖ := by
  rw [← smul_yosida_apply A hc.ne', norm_smul, norm_ofReal, abs_of_pos hc]
  exact mul_le_mul_of_nonneg_left (hA.norm_yosida_apply_le_norm_apply hc v) hc.le

/-- Let $H$ be a Hilbert space and let $A$ be maximal monotone. Then for every $v \in H$,
$$J_c v \to v \quad \text{as } c \to 0^+.$$
This is Proposition 7.2(c) of [brezis2011functional].

On $D(A)$ the convergence follows from the rate $\|v - J_c v\| \le c \|A v\|$. In general it
follows from the density of $D(A)$ and the bound $\|J_c\| \le 1$. -/
theorem IsMaximalMonotone.tendsto_resolvent_apply [CompleteSpace H] (hA : A.IsMaximalMonotone)
    (v : H) : Tendsto (fun c : ℝ => A.resolvent c v) (𝓝[>] 0) (𝓝 v) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨v₁, hv₁, hd⟩ := hA.dense_domain.exists_dist_lt v (by positivity : 0 < ε / 3)
  rw [dist_eq_norm] at hd
  refine ⟨ε / 3 / (‖A ⟨v₁, hv₁⟩‖ + 1), by positivity, fun c hc hcd => ?_⟩
  have hc' : 0 < c := hc
  rw [Real.dist_eq, sub_zero, abs_of_pos hc', lt_div_iff₀ (by positivity)] at hcd
  rw [dist_eq_norm]
  calc ‖A.resolvent c v - v‖
      = ‖A.resolvent c (v - v₁) + (A.resolvent c v₁ - v₁) + (v₁ - v)‖ := by
        rw [_root_.map_sub]
        congr 1
        abel
    _ ≤ ‖A.resolvent c (v - v₁)‖ + ‖A.resolvent c v₁ - v₁‖ + ‖v₁ - v‖ := norm_add₃_le
    _ ≤ ‖v - v₁‖ + c * ‖A ⟨v₁, hv₁⟩‖ + ‖v₁ - v‖ := by
        gcongr
        · exact hA.norm_resolvent_apply_le hc' _
        · rw [norm_sub_rev]
          exact hA.norm_sub_resolvent_apply_le hc' ⟨v₁, hv₁⟩
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [norm_sub_rev v₁ v]
        gcongr
        linarith
    _ = ε := by ring

/-- Let $H$ be a Hilbert space and let $A$ be maximal monotone. Then for every $v \in D(A)$,
$$A_c v \to A v \quad \text{as } c \to 0^+.$$
This is Proposition 7.2(d) of [brezis2011functional]. -/
theorem IsMaximalMonotone.tendsto_yosida_apply [CompleteSpace H] (hA : A.IsMaximalMonotone)
    (v : A.domain) : Tendsto (fun c : ℝ => A.yosida c v) (𝓝[>] 0) (𝓝 (A v)) := by
  refine (hA.tendsto_resolvent_apply (A v)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact (hA.yosida_apply_eq_resolvent_apply hc v).symm

/-- Let $H$ be a Hilbert space, let $A$ be maximal monotone and let $c > 0$. Then for every
$v \in H$,
$$c \|A_c v\|^2 \le \operatorname{Re} \langle A_c v, v \rangle.$$
This is the inequality (3) of the proof of Proposition 7.2(e) of [brezis2011functional].

The proof writes $\operatorname{Re} \langle A_c v, v \rangle = \operatorname{Re} \langle A_c v,
v - J_c v \rangle + \operatorname{Re} \langle A_c v, J_c v \rangle = c \|A_c v\|^2 +
\operatorname{Re} \langle A (J_c v), J_c v \rangle$. -/
theorem IsMaximalMonotone.smul_norm_sq_yosida_le_re_inner [CompleteSpace H]
    (hA : A.IsMaximalMonotone) {c : ℝ} (hc : 0 < c) (v : H) :
    c * ‖A.yosida c v‖ ^ 2 ≤ re ⟪A.yosida c v, v⟫ := by
  have hv : (c : 𝕜) • A.yosida c v + A.resolvent c v = v := by
    rw [smul_yosida_apply A hc.ne']
    abel
  have : re ⟪A.yosida c v, v⟫ =
      re ⟪A.yosida c v, (c : 𝕜) • A.yosida c v + A.resolvent c v⟫ := by rw [hv]
  rw [this, inner_add_right, _root_.map_add, inner_smul_right, re_ofReal_mul,
    inner_self_eq_norm_sq]
  refine le_add_of_nonneg_right ?_
  have := hA.isMonotone ⟨A.resolvent c v, hA.resolvent_apply_mem_domain hc v⟩
  rwa [← hA.yosida_apply_eq_apply_resolvent hc] at this

/-- Let $H$ be a Hilbert space, let $A$ be maximal monotone and let $c > 0$. Then the bounded
operator $A_c$ is monotone:
$$\operatorname{Re} \langle A_c v, v \rangle \ge 0 \quad \text{for every } v \in H.$$
This is Proposition 7.2(e) of [brezis2011functional]. -/
theorem IsMaximalMonotone.re_inner_yosida_nonneg [CompleteSpace H] (hA : A.IsMaximalMonotone)
    {c : ℝ} (hc : 0 < c) (v : H) : 0 ≤ re ⟪A.yosida c v, v⟫ :=
  (mul_nonneg hc.le (sq_nonneg _)).trans (hA.smul_norm_sq_yosida_le_re_inner hc v)

/-- Let $H$ be a Hilbert space, let $A$ be maximal monotone and let $c > 0$. Then for every
$v \in H$,
$$\|A_c v\| \le c^{-1} \|v\|.$$
This is Proposition 7.2(f) of [brezis2011functional], pointwise. It follows from the inequality
(3) and the Cauchy–Schwarz inequality. -/
theorem IsMaximalMonotone.norm_yosida_apply_le [CompleteSpace H] (hA : A.IsMaximalMonotone)
    {c : ℝ} (hc : 0 < c) (v : H) : ‖A.yosida c v‖ ≤ c⁻¹ * ‖v‖ := by
  have h1 := hA.smul_norm_sq_yosida_le_re_inner hc v
  have h2 := re_inner_le_norm (𝕜 := 𝕜) (A.yosida c v) v
  rcases (norm_nonneg (A.yosida c v)).eq_or_lt with h0 | h0
  · rw [← h0]
    positivity
  · rw [le_inv_mul_iff₀ hc]
    have : c * ‖A.yosida c v‖ * ‖A.yosida c v‖ ≤ ‖v‖ * ‖A.yosida c v‖ :=
      calc c * ‖A.yosida c v‖ * ‖A.yosida c v‖ = c * ‖A.yosida c v‖ ^ 2 := by ring
        _ ≤ re ⟪A.yosida c v, v⟫ := h1
        _ ≤ ‖A.yosida c v‖ * ‖v‖ := h2
        _ = ‖v‖ * ‖A.yosida c v‖ := mul_comm _ _
    exact le_of_mul_le_mul_right this h0

/-- Let $H$ be a Hilbert space, let $A$ be maximal monotone and let $c > 0$. Then
$\|A_c\| \le c^{-1}$. This is Proposition 7.2(f) of [brezis2011functional]. -/
theorem IsMaximalMonotone.norm_yosida_le [CompleteSpace H] (hA : A.IsMaximalMonotone) {c : ℝ}
    (hc : 0 < c) : ‖A.yosida c‖ ≤ c⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hc.le) (hA.norm_yosida_apply_le hc)

/-- Let $H$ be a Hilbert space, let $A$ be maximal monotone and let $c, d > 0$. Then for all
$x, y \in H$,
$$\operatorname{Re} \langle A_c x - A_d y, c A_c x - d A_d y \rangle \le \operatorname{Re}
  \langle A_c x - A_d y, x - y \rangle.$$
This is the inequality (12) of the proof of Theorem 7.4 (the Hille–Yosida theorem), Step 3, in
[brezis2011functional], here for arbitrary vectors.

The proof writes $x - y = (c A_c x - d A_d y) + (J_c x - J_d y)$ and uses $\operatorname{Re}
\langle A_c x - A_d y, J_c x - J_d y \rangle = \operatorname{Re} \langle A (J_c x - J_d y), J_c
x - J_d y \rangle \ge 0$. -/
theorem IsMaximalMonotone.re_inner_yosida_sub_yosida_ge [CompleteSpace H]
    (hA : A.IsMaximalMonotone) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (x y : H) :
    re ⟪A.yosida c x - A.yosida d y, (c : 𝕜) • A.yosida c x - (d : 𝕜) • A.yosida d y⟫ ≤
      re ⟪A.yosida c x - A.yosida d y, x - y⟫ := by
  have hxy : x - y = ((c : 𝕜) • A.yosida c x - (d : 𝕜) • A.yosida d y) +
      (A.resolvent c x - A.resolvent d y) := by
    rw [smul_yosida_apply A hc.ne', smul_yosida_apply A hd.ne']
    abel
  rw [hxy, inner_add_right, _root_.map_add]
  refine le_add_of_nonneg_right ?_
  have := hA.isMonotone (⟨A.resolvent c x, hA.resolvent_apply_mem_domain hc x⟩ -
    ⟨A.resolvent d y, hA.resolvent_apply_mem_domain hd y⟩)
  rwa [map_sub, Submodule.coe_sub, ← hA.yosida_apply_eq_apply_resolvent hc,
    ← hA.yosida_apply_eq_apply_resolvent hd] at this

/-! ### The domains $D(A^k)$ as Hilbert spaces -/

section PowDomain

variable (A) in
/-- The **graph of the powers** of $A$ up to $k$: the subspace of the $\ell^2$ product $H^{k+1}$
(`PiLp 2 (Fin (k + 1) → H)`) of the tuples $(x_0, \dots, x_k)$ with $x_i \in D(A)$ and
$A x_i = x_{i+1}$ for every $i < k$. These are the tuples $(u, A u, \dots, A^k u)$ for
$u \in D(A^k)$, as in the definition of $D(A^k)$ in §7.3 of [brezis2011functional]. -/
def powGraph (k : ℕ) : Submodule 𝕜 (PiLp 2 fun _ : Fin (k + 1) => H) where
  carrier := {x | ∀ i : Fin k, ∃ h : x i.castSucc ∈ A.domain, A ⟨x i.castSucc, h⟩ = x i.succ}
  zero_mem' := fun i => ⟨by simp, by
    have h : (⟨(0 : PiLp 2 fun _ : Fin (k + 1) => H) i.castSucc, by simp⟩ : A.domain) = 0 :=
      Subtype.ext (by simp)
    rw [h, map_zero]
    simp⟩
  add_mem' := by
    rintro x y hx hy i
    obtain ⟨hx1, hx2⟩ := hx i
    obtain ⟨hy1, hy2⟩ := hy i
    refine ⟨by simpa using add_mem hx1 hy1, ?_⟩
    have : (⟨(x + y) i.castSucc, by simpa using add_mem hx1 hy1⟩ : A.domain) =
        ⟨x i.castSucc, hx1⟩ + ⟨y i.castSucc, hy1⟩ := by
      ext
      simp
    rw [this, map_add, hx2, hy2]
    simp
  smul_mem' := by
    rintro c x hx i
    obtain ⟨hx1, hx2⟩ := hx i
    refine ⟨by simpa using Submodule.smul_mem _ c hx1, ?_⟩
    have : (⟨(c • x) i.castSucc, by simpa using Submodule.smul_mem _ c hx1⟩ : A.domain) =
        c • ⟨x i.castSucc, hx1⟩ := by
      ext
      simp
    rw [this, map_smul, hx2]
    simp

variable (A) in
/-- A tuple $(x_0, \dots, x_k)$ lies in `LinearPMap.powGraph A k` if and only if $x_i \in D(A)$ and
$A x_i = x_{i+1}$ for every $i < k$. -/
theorem mem_powGraph_iff {k : ℕ} {x : PiLp 2 fun _ : Fin (k + 1) => H} :
    x ∈ A.powGraph k ↔
      ∀ i : Fin k, ∃ h : x i.castSucc ∈ A.domain, A ⟨x i.castSucc, h⟩ = x i.succ :=
  Iff.rfl

variable (A) in
/-- The Hilbert space $D(A^k)$ of §7.3 of [brezis2011functional]: the tuples
$(u, A u, \dots, A^k u)$, as a subspace of the $\ell^2$ product $H^{k+1}$, with the inner
product and the norm
$$\langle u, v \rangle_{D(A^k)} = \sum_{j \le k} \langle A^j u, A^j v \rangle, \qquad
  \|u\|_{D(A^k)} = \Bigl(\sum_{j \le k} \|A^j u\|^2\Bigr)^{1/2}.$$

The inner product and the norm are those of the subspace (`LinearPMap.PowDomain.inner_def`,
`LinearPMap.PowDomain.norm_sq_eq`). `A.PowDomain 1` is $D(A)$ with the graph norm, and
`A.PowDomain 0` is $H$. -/
abbrev PowDomain (k : ℕ) : Type _ := ↥(A.powGraph k)

namespace PowDomain

variable (A) in
/-- For $j \le k$, the bounded operator $A^j : D(A^k) \to H$, which takes the $j$-th entry of the
tuple.

The inclusion $D(A^k) \to H$ is the operator `applyL A k 0`. The operator `applyL A 1 1` is $A$
on $D(A)$. -/
def applyL (k : ℕ) (j : Fin (k + 1)) : A.PowDomain k →L[𝕜] H :=
  (PiLp.proj (𝕜 := 𝕜) (p := 2) (fun _ : Fin (k + 1) => H) j).comp (A.powGraph k).subtypeL

variable {k : ℕ}

/-- `applyL A k j x` is the $j$-th entry of the tuple $x$. -/
theorem applyL_apply (j : Fin (k + 1)) (x : A.PowDomain k) :
    applyL A k j x = (x : PiLp 2 fun _ : Fin (k + 1) => H) j :=
  rfl

/-- Two elements of $D(A^k)$ with the same entries are equal. -/
theorem ext {x y : A.PowDomain k} (h : ∀ j, applyL A k j x = applyL A k j y) : x = y :=
  Subtype.ext (PiLp.ext h)

/-- The inner product of $D(A^k)$ is $\langle x, y \rangle = \sum_{j \le k} \langle A^j x, A^j y
\rangle$. -/
theorem inner_def (x y : A.PowDomain k) : ⟪x, y⟫ = ∑ j, ⟪applyL A k j x, applyL A k j y⟫ :=
  rfl

/-- The norm of $D(A^k)$ satisfies $\|x\|^2 = \sum_{j \le k} \|A^j x\|^2$. -/
theorem norm_sq_eq (x : A.PowDomain k) : ‖x‖ ^ 2 = ∑ j, ‖applyL A k j x‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ (x : PiLp 2 fun _ : Fin (k + 1) => H)

/-- Every entry map is a contraction: $\|A^j x\| \le \|x\|_{D(A^k)}$ for $j \le k$. -/
theorem norm_applyL_apply_le (j : Fin (k + 1)) (x : A.PowDomain k) : ‖applyL A k j x‖ ≤ ‖x‖ :=
  PiLp.norm_apply_le (x : PiLp 2 fun _ : Fin (k + 1) => H) j

/-- The entries $0, \dots, k - 1$ of an element of $D(A^k)$ lie in $D(A)$. -/
theorem applyL_mem_domain (x : A.PowDomain k) (i : Fin k) :
    applyL A k i.castSucc x ∈ A.domain :=
  (x.2 i).fst

/-- Consecutive entries of an element $x$ of $D(A^k)$ are related by $A$: $A (A^i x) = A^{i+1} x$
for $i < k$. -/
theorem apply_applyL (x : A.PowDomain k) (i : Fin k) :
    A ⟨applyL A k i.castSucc x, applyL_mem_domain x i⟩ = applyL A k i.succ x :=
  (x.2 i).snd

/-- If $a \in D(A)$ with $A a = b$, and $a' = a$, $b' = b$, then $a' \in D(A)$ and $A a' = b'$. This
is the membership condition of `LinearPMap.powGraph`, transported along equalities of the
entries. -/
theorem exists_apply_eq_of_eq {a b : H} (ha : a ∈ A.domain) (hab : A ⟨a, ha⟩ = b) {a' b' : H}
    (h1 : a' = a) (h2 : b' = b) : ∃ h : a' ∈ A.domain, A ⟨a', h⟩ = b' := by
  subst h1
  subst h2
  exact ⟨ha, hab⟩

/-- An element of $D(A^k)$ is determined by its entry $u$ of index $0$, because the other entries
are $A u, A^2 u, \dots$: the map $A^0 : D(A^k) \to H$ is injective. -/
theorem applyL_zero_injective : Function.Injective (applyL A k 0) := by
  intro x y hxy
  refine ext fun j => ?_
  induction j using Fin.induction with
  | zero => exact hxy
  | succ i ih =>
    rw [← apply_applyL x i, ← apply_applyL y i]
    congr 1
    exact Subtype.ext ih

variable (A) in
/-- The element of $D(A^k)$ with entries $f_0, \dots, f_k$, for a tuple $f$ with $f_i \in D(A)$ and
$A f_i = f_{i+1}$ for every $i < k$. -/
def mk (f : Fin (k + 1) → H)
    (hf : ∀ i : Fin k, ∃ h : f i.castSucc ∈ A.domain, A ⟨f i.castSucc, h⟩ = f i.succ) :
    A.PowDomain k :=
  ⟨toLp 2 f, hf⟩

/-- The entries of `LinearPMap.PowDomain.mk A f hf` are $f_0, \dots, f_k$. -/
@[simp]
theorem applyL_mk (f : Fin (k + 1) → H) (hf) (j : Fin (k + 1)) : applyL A k j (mk A f hf) = f j :=
  rfl

/-- Let $e : \{0, \dots, l\} \to \{0, \dots, k\}$ be injective and let $x \in D(A^k)$. If the tuple
$(A^{e(i)} x)_{i \le l}$ lies in $D(A^l)$, then its norm in $D(A^l)$ is at most
$\|x\|_{D(A^k)}$. -/
theorem norm_mk_comp_le {l : ℕ} (e : Fin (l + 1) → Fin (k + 1)) (he : Function.Injective e)
    (x : A.PowDomain k) (hf) : ‖mk A (fun i => applyL A k (e i) x) hf‖ ≤ ‖x‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq, norm_sq_eq]
  simp only [applyL_mk]
  rw [← Finset.sum_image (f := fun i => ‖applyL A k i x‖ ^ 2) he.injOn]
  exact Finset.sum_le_univ_sum_of_nonneg fun i => sq_nonneg _

variable (A) in
/-- The inclusion $D(A^{k+1}) \subseteq D(A^k)$, which drops the last entry of the tuple. It is a
contraction. -/
def castL (k : ℕ) : A.PowDomain (k + 1) →L[𝕜] A.PowDomain k :=
  LinearMap.mkContinuous
    { toFun := fun x => mk A (fun j => applyL A (k + 1) j.castSucc x) fun i =>
        exists_apply_eq_of_eq (applyL_mem_domain x i.castSucc) (apply_applyL x i.castSucc) rfl
          (by rw [Fin.succ_castSucc])
      map_add' := fun x y => ext fun j => by simp
      map_smul' := fun c x => ext fun j => by simp }
    1 fun x => by
      rw [one_mul]
      exact norm_mk_comp_le _ (Fin.castSucc_injective _) x _

/-- The entries of `castL A k x` are the first $k + 1$ entries of $x$. -/
@[simp]
theorem applyL_castL (j : Fin (k + 1)) (x : A.PowDomain (k + 1)) :
    applyL A k j (castL A k x) = applyL A (k + 1) j.castSucc x :=
  rfl

/-- The inclusion $D(A^{k+1}) \to D(A^k)$ is a contraction. -/
theorem norm_castL_apply_le (x : A.PowDomain (k + 1)) : ‖castL A k x‖ ≤ ‖x‖ :=
  norm_mk_comp_le _ (Fin.castSucc_injective _) x _

variable (A) in
/-- The operator $A$ from $D(A^{k+1})$ to $D(A^k)$, which drops the first entry of the tuple. It is
a contraction. -/
def shiftL (k : ℕ) : A.PowDomain (k + 1) →L[𝕜] A.PowDomain k :=
  LinearMap.mkContinuous
    { toFun := fun x => mk A (fun j => applyL A (k + 1) j.succ x) fun i =>
        exists_apply_eq_of_eq (applyL_mem_domain x i.succ) (apply_applyL x i.succ)
          (by rw [Fin.succ_castSucc]) rfl
      map_add' := fun x y => ext fun j => by simp
      map_smul' := fun c x => ext fun j => by simp }
    1 fun x => by
      rw [one_mul]
      exact norm_mk_comp_le _ (Fin.succ_injective _) x _

/-- The entries of `shiftL A k x` are the last $k + 1$ entries of $x$. -/
@[simp]
theorem applyL_shiftL (j : Fin (k + 1)) (x : A.PowDomain (k + 1)) :
    applyL A k j (shiftL A k x) = applyL A (k + 1) j.succ x :=
  rfl

/-- The operator $A : D(A^{k+1}) \to D(A^k)$ is a contraction. -/
theorem norm_shiftL_apply_le (x : A.PowDomain (k + 1)) : ‖shiftL A k x‖ ≤ ‖x‖ :=
  norm_mk_comp_le _ (Fin.succ_injective _) x _

/-- The entry of index $0$ of `shiftL A k x` is $A$ applied to the entry of index $0$ of $x$. -/
theorem applyL_zero_shiftL (x : A.PowDomain (k + 1)) :
    applyL A k 0 (shiftL A k x) = A ⟨applyL A (k + 1) 0 x, applyL_mem_domain x 0⟩ := by
  rw [applyL_shiftL]
  exact (apply_applyL x 0).symm

variable (A) in
/-- For $j \le k$, the inclusion $D(A^k) \subseteq D(A^j)$, which keeps the first $j + 1$ entries.
It is a contraction, and `LinearPMap.PowDomain.castL` is the case $j + 1 = k$. -/
def castLE {j : ℕ} (h : j ≤ k) : A.PowDomain k →L[𝕜] A.PowDomain j :=
  LinearMap.mkContinuous
    { toFun := fun x => mk A (fun i => applyL A k (Fin.castLE (by omega) i) x) fun i =>
        exists_apply_eq_of_eq (applyL_mem_domain x (Fin.castLE (by omega) i))
          (apply_applyL x (Fin.castLE (by omega) i)) (by simp) (by simp)
      map_add' := fun x y => ext fun i => by simp
      map_smul' := fun c x => ext fun i => by simp }
    1 fun x => by
      rw [one_mul]
      exact norm_mk_comp_le _ (Fin.castLE_injective _) x _

/-- The entries of `castLE A h x` are the first $j + 1$ entries of $x$. -/
@[simp]
theorem applyL_castLE {j : ℕ} (h : j ≤ k) (i : Fin (j + 1)) (x : A.PowDomain k) :
    applyL A j i (castLE A h x) = applyL A k (Fin.castLE (by omega) i) x :=
  rfl

/-- The inclusion $D(A^k) \to D(A^j)$ is a contraction. -/
theorem norm_castLE_apply_le {j : ℕ} (h : j ≤ k) (x : A.PowDomain k) :
    ‖castLE A h x‖ ≤ ‖x‖ :=
  norm_mk_comp_le _ (Fin.castLE_injective _) x _

/-- The inclusion $D(A^k) \to D(A^k)$ is the identity. -/
@[simp]
theorem castLE_rfl (x : A.PowDomain k) : castLE A le_rfl x = x :=
  ext fun i => by simp

/-- The inclusions compose: $D(A^k) \to D(A^l) \to D(A^j)$ is the inclusion $D(A^k) \to D(A^j)$ for
$j \le l \le k$. -/
theorem castLE_castLE {j l : ℕ} (hjl : j ≤ l) (hlk : l ≤ k) (x : A.PowDomain k) :
    castLE A hjl (castLE A hlk x) = castLE A (hjl.trans hlk) x :=
  ext fun i => by simp

/-- For $j + 1 \le k$, the inclusion $D(A^k) \to D(A^{j+1})$ followed by
`LinearPMap.PowDomain.castL` is the inclusion $D(A^k) \to D(A^j)$. -/
theorem castL_castLE {j : ℕ} (h : j + 1 ≤ k) (x : A.PowDomain k) :
    castL A j (castLE A h x) = castLE A (by omega) x :=
  ext fun i => by simp

/-- The inclusion $D(A^{k+1}) \to D(A^k)$ given by `LinearPMap.PowDomain.castLE` is
`LinearPMap.PowDomain.castL`. -/
theorem castLE_succ_eq_castL (x : A.PowDomain (k + 1)) :
    castLE A (Nat.le_succ k) x = castL A k x :=
  ext fun _ => rfl

/-- The extension of an element $x = (u, \dots, A^k u)$ of $D(A^k)$ whose last entry $A^k u$ lies in
$D(A)$: the element $(u, \dots, A^k u, A^{k+1} u)$ of $D(A^{k+1})$. -/
def snoc (x : A.PowDomain k) (h : applyL A k (Fin.last k) x ∈ A.domain) :
    A.PowDomain (k + 1) :=
  mk A (Fin.snoc (fun i => applyL A k i x) (A ⟨applyL A k (Fin.last k) x, h⟩)) fun i => by
    induction i using Fin.lastCases with
    | last =>
      exact exists_apply_eq_of_eq h rfl (Fin.snoc_castSucc _ _ _)
        (by rw [Fin.succ_last, Fin.snoc_last])
    | cast i =>
      exact exists_apply_eq_of_eq (applyL_mem_domain x i) (apply_applyL x i)
        (Fin.snoc_castSucc _ _ _) (by rw [Fin.succ_castSucc, Fin.snoc_castSucc])

/-- The first $k + 1$ entries of `snoc x h` are those of $x$. -/
@[simp]
theorem applyL_snoc_castSucc (x : A.PowDomain k) (h) (i : Fin (k + 1)) :
    applyL A (k + 1) i.castSucc (snoc x h) = applyL A k i x := by
  unfold snoc
  rw [applyL_mk, Fin.snoc_castSucc]

/-- The last entry of `snoc x h` is $A$ applied to the last entry of $x$. -/
@[simp]
theorem applyL_snoc_last (x : A.PowDomain k) (h) :
    applyL A (k + 1) (Fin.last (k + 1)) (snoc x h) = A ⟨applyL A k (Fin.last k) x, h⟩ := by
  unfold snoc
  rw [applyL_mk, Fin.snoc_last]

/-- Dropping the last entry undoes `LinearPMap.PowDomain.snoc`: `castL A k (snoc x h) = x`. -/
@[simp]
theorem castL_snoc (x : A.PowDomain k) (h) : castL A k (snoc x h) = x :=
  ext fun i => by simp

end PowDomain

open PowDomain

/-- If $A$ is closed, then for every $k$ the subspace `LinearPMap.powGraph A k` of the $\ell^2$
product $H^{k+1}$ is closed.

The subspace is the intersection of the preimages of the closed graph of $A$ under the
continuous maps $x \mapsto (x_i, x_{i+1})$, as in §7.3 of [brezis2011functional]. -/
theorem isClosed_powGraph (hA : A.IsClosed) (k : ℕ) :
    _root_.IsClosed (A.powGraph k : Set (PiLp 2 fun _ : Fin (k + 1) => H)) := by
  have hA' : _root_.IsClosed (A.graph : Set (H × H)) := hA
  have : (A.powGraph k : Set (PiLp 2 fun _ : Fin (k + 1) => H)) =
      ⋂ i : Fin k, (fun x : PiLp 2 fun _ : Fin (k + 1) => H => (x i.castSucc, x i.succ)) ⁻¹'
        (A.graph : Set (H × H)) := by
    ext x
    simp only [SetLike.mem_coe, mem_powGraph_iff, Set.mem_iInter, Set.mem_preimage, mem_graph_iff]
    refine forall_congr' fun i => ⟨fun ⟨h, hx⟩ => ⟨⟨_, h⟩, rfl, hx⟩, fun ⟨y, hy, hx⟩ => ?_⟩
    exact exists_apply_eq_of_eq y.2 hx hy.symm rfl
  rw [this]
  refine isClosed_iInter fun i => hA'.preimage ?_
  exact ((PiLp.proj (𝕜 := 𝕜) (p := 2) _ i.castSucc).continuous).prodMk
    ((PiLp.proj (𝕜 := 𝕜) (p := 2) _ i.succ).continuous)

/-- If $H$ is a Hilbert space and $A$ is closed, then $D(A^k)$ is complete for every $k$, so it is a
Hilbert space. This is the statement "it is easily seen that $D(A^k)$ is a Hilbert space" of
§7.3 of [brezis2011functional].

This is not an instance, because the hypothesis is a proof. A user writes
`haveI := hA.completeSpace_powDomain k`. -/
theorem IsClosed.completeSpace_powDomain [CompleteSpace H] (hA : A.IsClosed) (k : ℕ) :
    CompleteSpace (A.PowDomain k) :=
  (isClosed_powGraph hA k).completeSpace_coe

/-! ### The part of $A$ in $D(A^k)$ -/

variable (A) in
/-- The domain of the part of $A$ in $D(A^k)$: the elements of $D(A^k)$ whose last entry $A^k u$
lies in $D(A)$. This is $D(A^{k+1})$ as a subspace of $D(A^k)$, the range of
`LinearPMap.PowDomain.castL`. -/
def powPartDomain (k : ℕ) : Submodule 𝕜 (A.PowDomain k) where
  carrier := {x | applyL A k (Fin.last k) x ∈ A.domain}
  zero_mem' := by simp
  add_mem' := fun hx hy => by simpa using add_mem hx hy
  smul_mem' := fun c x hx => by simpa using Submodule.smul_mem _ c hx

/-- An element of $D(A^k)$ lies in the domain of the part of $A$ if and only if its last entry lies
in $D(A)$. -/
theorem mem_powPartDomain_iff {k : ℕ} {x : A.PowDomain k} :
    x ∈ A.powPartDomain k ↔ applyL A k (Fin.last k) x ∈ A.domain :=
  Iff.rfl

/-- If $x$ lies in the domain of the part of $A$ in $D(A^k)$, then all entries of $x$ lie in $D(A)$.
-/
theorem applyL_mem_domain_of_mem_powPartDomain {k : ℕ} {x : A.PowDomain k}
    (hx : x ∈ A.powPartDomain k) (i : Fin (k + 1)) : applyL A k i x ∈ A.domain := by
  induction i using Fin.lastCases with
  | last => exact hx
  | cast i => exact applyL_mem_domain x i

/-- If $a, b \in D(A)$, then $A (a + b) = A a + A b$, with the proof of $a + b \in D(A)$ given
separately. -/
theorem apply_mk_add {a b : H} (h : a + b ∈ A.domain) (ha : a ∈ A.domain) (hb : b ∈ A.domain) :
    A ⟨a + b, h⟩ = A ⟨a, ha⟩ + A ⟨b, hb⟩ :=
  map_add A ⟨a, ha⟩ ⟨b, hb⟩

/-- If $a \in D(A)$ and $c \in \mathbb{K}$, then $A (c a) = c A a$, with the proof of $c a \in D(A)$
given separately. -/
theorem apply_mk_smul {c : 𝕜} {a : H} (h : c • a ∈ A.domain) (ha : a ∈ A.domain) :
    A ⟨c • a, h⟩ = c • A ⟨a, ha⟩ :=
  map_smul A c ⟨a, ha⟩

/-- For $x = (u, \dots, A^k u)$ in the domain of the part of $A$, the tuple
$(A u, A^2 u, \dots, A^{k+1} u)$ has consecutive entries related by $A$: for every $i < k$,
$A (A x_i) = A x_{i+1}$. -/
theorem powPart_mem_aux {k : ℕ} {x : A.PowDomain k} (hx : x ∈ A.powPartDomain k) (i : Fin k) :
    ∃ h : A ⟨applyL A k i.castSucc x, applyL_mem_domain_of_mem_powPartDomain hx i.castSucc⟩ ∈
      A.domain, A ⟨_, h⟩ =
        A ⟨applyL A k i.succ x, applyL_mem_domain_of_mem_powPartDomain hx i.succ⟩ :=
  exists_apply_eq_of_eq (a := applyL A k i.succ x)
    (applyL_mem_domain_of_mem_powPartDomain hx i.succ) rfl (apply_applyL x i) rfl

variable (A) in
/-- The **part of $A$ in $D(A^k)$**: the operator $D(A^{k+1}) \subseteq D(A^k) \to D(A^k)$,
$u \mapsto A u$, which sends $(u, A u, \dots, A^k u)$ to $(A u, A^2 u, \dots, A^{k+1} u)$.

This is the operator $A_1 : D(A^2) \subseteq D(A) \to D(A)$ of the proof of Theorem 7.5 of
[brezis2011functional] and the operator $\tilde A : D(A^k) \subseteq D(A^{k-1}) \to D(A^{k-1})$
of the proof of Theorem 7.7, in one definition (§7.3 and §7.4 of [brezis2011functional]). -/
def powPart (k : ℕ) : A.PowDomain k →ₗ.[𝕜] A.PowDomain k where
  domain := A.powPartDomain k
  toFun :=
    { toFun := fun x => PowDomain.mk A
        (fun i => A ⟨applyL A k i x, applyL_mem_domain_of_mem_powPartDomain x.2 i⟩)
        (powPart_mem_aux x.2)
      map_add' := fun x y => PowDomain.ext fun i => by
        simp only [applyL_mk, Submodule.coe_add, _root_.map_add]
        exact apply_mk_add _ _ _
      map_smul' := fun c x => PowDomain.ext fun i => by
        simp only [applyL_mk, Submodule.coe_smul, _root_.map_smul, RingHom.id_apply]
        exact apply_mk_smul _ _ }

/-- The domain of the part of $A$ in $D(A^k)$ is `LinearPMap.powPartDomain A k`. -/
theorem powPart_domain (k : ℕ) : (A.powPart k).domain = A.powPartDomain k :=
  rfl

/-- An element of $D(A^k)$ lies in the domain of the part of $A$ if and only if its last entry lies
in $D(A)$. -/
theorem mem_powPart_domain_iff {k : ℕ} {x : A.PowDomain k} :
    x ∈ (A.powPart k).domain ↔ applyL A k (Fin.last k) x ∈ A.domain :=
  Iff.rfl

/-- The entries of the part of $A$: for $x$ in the domain of the part of $A$ in $D(A^k)$ and
$i \le k$, the $i$-th entry of $A x$ is $A x_i$. -/
@[simp]
theorem applyL_powPart_apply {k : ℕ} (x : (A.powPart k).domain) (i : Fin (k + 1)) :
    applyL A k i (A.powPart k x) =
      A ⟨applyL A k i x, applyL_mem_domain_of_mem_powPartDomain x.2 i⟩ :=
  rfl

/-- For $x$ in the domain of the part of $A$ in $D(A^k)$, the entry of index $0$ of $A x$ is $A u$,
where $u$ is the entry of index $0$ of $x$. So the part of $A$ acts as $A$; this is
$A_1 u = A u$ in the proof of Theorem 7.5 of [brezis2011functional]. -/
theorem applyL_zero_powPart_apply {k : ℕ} (x : (A.powPart k).domain) :
    applyL A k 0 (A.powPart k x) =
      A ⟨applyL A k 0 x, applyL_mem_domain_of_mem_powPartDomain x.2 0⟩ :=
  rfl

/-- The part of $A$ in $D(A^k)$ is the composite of `LinearPMap.PowDomain.snoc` and
`LinearPMap.PowDomain.shiftL`: it extends $(u, \dots, A^k u)$ to $(u, \dots, A^{k+1} u)$ and
then drops the first entry, which gives $(A u, \dots, A^{k+1} u)$. -/
theorem powPart_apply_eq_shiftL_snoc {k : ℕ} (x : (A.powPart k).domain) :
    A.powPart k x = shiftL A k (snoc (x : A.PowDomain k) (mem_powPart_domain_iff.1 x.2)) := by
  refine PowDomain.ext fun i => ?_
  rw [applyL_powPart_apply, applyL_shiftL]
  induction i using Fin.lastCases with
  | last => exact (applyL_snoc_last _ _).symm
  | cast i => rw [Fin.succ_castSucc, applyL_snoc_castSucc, apply_applyL]

/-- For every $x \in D(A^{k+1})$, the element `castL A k x` of $D(A^k)$ lies in the domain of the
part of $A$. -/
theorem castL_mem_powPart_domain {k : ℕ} (x : A.PowDomain (k + 1)) :
    castL A k x ∈ (A.powPart k).domain := by
  rw [mem_powPart_domain_iff, applyL_castL]
  exact applyL_mem_domain x (Fin.last k)

/-- The range of the inclusion $D(A^{k+1}) \to D(A^k)$ is the domain of the part of $A$ in $D(A^k)$,
as sets. -/
theorem range_castL {k : ℕ} :
    Set.range (castL A k) = ((A.powPart k).domain : Set (A.PowDomain k)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact castL_mem_powPart_domain y
  · intro hx
    exact ⟨snoc x (mem_powPart_domain_iff.1 hx), castL_snoc x _⟩

/-- If $A$ is monotone, then for every $k$ the part of $A$ in $D(A^k)$ is monotone. This is in the
proof of Theorem 7.5 of [brezis2011functional].

The proof uses $\operatorname{Re} \langle A x, x \rangle_{D(A^k)} = \sum_{j \le k}
\operatorname{Re} \langle A x_j, x_j \rangle$. -/
theorem IsMonotone.powPart (hA : A.IsMonotone) (k : ℕ) : (A.powPart k).IsMonotone := by
  intro x
  rw [inner_def, _root_.map_sum]
  simp only [applyL_powPart_apply]
  exact Finset.sum_nonneg fun i _ => hA _

/-- If $A$ is symmetric, then for every $k$ the part of $A$ in $D(A^k)$ is symmetric. This is the
statement "$\tilde A$ is symmetric in $\tilde H$" in the proof of Theorem 7.7 of
[brezis2011functional]. -/
theorem IsFormalAdjoint.powPart (hs : A.IsFormalAdjoint A) (k : ℕ) :
    (A.powPart k).IsFormalAdjoint (A.powPart k) := by
  intro x y
  rw [inner_def, inner_def]
  simp only [applyL_powPart_apply]
  exact Finset.sum_congr rfl fun i _ => hs ⟨applyL A k i x, _⟩ ⟨applyL A k i y, _⟩

/-- Let $H$ be a Hilbert space and let $A$ be maximal monotone. Then for every $k$ the part of $A$
in $D(A^k)$ is maximal monotone. This is the statement "it is easy to check that $A_1$ is
maximal monotone in $H_1$" in the proof of Theorem 7.5 of [brezis2011functional].

The solution of $x + A x = f$ in $D(A^k)$ is the tuple $(J_1 f_j)_j$, because $J_1$ commutes
with $A$. -/
theorem IsMaximalMonotone.powPart [CompleteSpace H] (hA : A.IsMaximalMonotone) (k : ℕ) :
    (A.powPart k).IsMaximalMonotone := by
  refine ⟨hA.isMonotone.powPart k, fun f => ?_⟩
  have hJ : ∀ v, A.resolvent 1 v ∈ A.domain := hA.resolvent_apply_mem_domain one_pos
  have hJ' : ∀ v, A.resolvent 1 v + A ⟨A.resolvent 1 v, hJ v⟩ = v := fun v => by
    have := hA.resolvent_add_smul_apply one_pos v
    rwa [ofReal_one, one_smul] at this
  let x : A.PowDomain k := PowDomain.mk A (fun i => A.resolvent 1 (applyL A k i f)) fun i =>
    ⟨hJ _, by rw [← apply_applyL f i, hA.resolvent_apply_comm one_pos]⟩
  refine ⟨⟨x, hJ _⟩, PowDomain.ext fun i => ?_⟩
  rw [_root_.map_add, applyL_powPart_apply]
  exact hJ' _

/-- Let $H$ be a Hilbert space and let $A$ be maximal monotone. Then for every $k$, the space
$D(A^{k+1})$ is dense in $D(A^k)$ for the norm of $D(A^k)$: the range of the inclusion
`LinearPMap.PowDomain.castL A k` is dense. For $k = 1$ this is Lemma 7.2 of
[brezis2011functional], "$D(A^2)$ is dense in $D(A)$ for the graph norm".

The tuple $(J_c x_j)_j$ lies in the range of the inclusion and converges to $x$ as $c \to 0^+$. -/
theorem IsMaximalMonotone.dense_range_castL [CompleteSpace H] (hA : A.IsMaximalMonotone)
    (k : ℕ) : Dense (Set.range (castL A k)) := by
  intro x
  rw [Metric.mem_closure_iff]
  intro ε hε
  -- the tuples `(J_c x_j)_j` converge to `x` in the `ℓ²`-norm
  have hΦ : Tendsto (fun c : ℝ => (toLp 2 fun i => A.resolvent c (applyL A k i x) :
      PiLp 2 fun _ : Fin (k + 1) => H)) (𝓝[>] 0) (𝓝 (x : PiLp 2 fun _ : Fin (k + 1) => H)) := by
    have h1 : Tendsto (fun c : ℝ => fun i => A.resolvent c (applyL A k i x)) (𝓝[>] 0)
        (𝓝 fun i => applyL A k i x) :=
      tendsto_pi_nhds.2 fun i => hA.tendsto_resolvent_apply _
    exact ((PiLp.continuous_toLp (p := 2) (β := fun _ : Fin (k + 1) => H)).tendsto _).comp h1
  obtain ⟨c, hd, hc⟩ := ((hΦ.eventually (Metric.ball_mem_nhds _ hε)).and
    self_mem_nhdsWithin).exists
  have hc'' : (0 : ℝ) < c := hc
  -- the tuple `(J_c x_j)_j` lies in `D(A^k)`, and its last entry lies in `D(A)`
  let y : A.PowDomain k := PowDomain.mk A (fun i => A.resolvent c (applyL A k i x)) fun i =>
    ⟨hA.resolvent_apply_mem_domain hc'' _, by
      rw [← apply_applyL x i, hA.resolvent_apply_comm hc'']⟩
  refine ⟨y, ⟨snoc y (hA.resolvent_apply_mem_domain hc'' _), castL_snoc _ _⟩, ?_⟩
  rw [dist_comm] at hd
  exact hd

end PowDomain

/-! ### Symmetric and self-adjoint operators -/

section SelfAdjoint

variable [CompleteSpace H]

/-- Let $H$ be a Hilbert space. A self-adjoint operator $A$, with $A^* = A$, is symmetric. This is
the easy direction of Remark 7 of Chapter 7 of [brezis2011functional]. -/
theorem _root_.IsSelfAdjoint.isFormalAdjoint_self (hA : IsSelfAdjoint A) :
    A.IsFormalAdjoint A := by
  have h := adjoint_isFormalAdjoint hA.dense_domain
  rwa [isSelfAdjoint_def.mp hA] at h

/-- Let $H$ be a Hilbert space and let $A$ be densely defined. Then $A$ is symmetric if and only if
$A \subseteq A^*$, that is, $D(A) \subseteq D(A^*)$ and $A^* = A$ on $D(A)$. This is Remark 7 of
Chapter 7 of [brezis2011functional]. -/
theorem IsFormalAdjoint.le_adjoint_iff (hd : Dense (A.domain : Set H)) :
    A.IsFormalAdjoint A ↔ A ≤ A† := by
  refine ⟨fun h => h.le_adjoint hd, fun h x y => ?_⟩
  rw [apply_comp_inclusion h x]
  exact adjoint_isFormalAdjoint hd _ y

/-- Let $H$ be a Hilbert space, let $A$ be a symmetric maximal monotone operator and let $c > 0$.
Then the resolvent $J_c$ is self-adjoint.

With $u_1 = J_c u$ and $v_1 = J_c v$, one has $\langle u_1, v \rangle = \langle u_1, v_1 + c A
v_1 \rangle = \langle u_1 + c A u_1, v_1 \rangle = \langle u, v_1 \rangle$. This is the argument
of the proof of Proposition 7.6 and of $J_\lambda^* = J_\lambda$ in the proof of Theorem 7.7 of
[brezis2011functional]. -/
theorem IsMaximalMonotone.isSelfAdjoint_resolvent (hA : A.IsMaximalMonotone)
    (hs : A.IsFormalAdjoint A) {c : ℝ} (hc : 0 < c) : IsSelfAdjoint (A.resolvent c) := by
  refine LinearMap.IsSymmetric.isSelfAdjoint fun u v => ?_
  simp only [ContinuousLinearMap.coe_coe]
  set u₁ : A.domain := ⟨A.resolvent c u, hA.resolvent_apply_mem_domain hc u⟩
  set v₁ : A.domain := ⟨A.resolvent c v, hA.resolvent_apply_mem_domain hc v⟩
  have hu : (u₁ : H) + (c : 𝕜) • A u₁ = u := hA.resolvent_add_smul_apply hc u
  have hv : (v₁ : H) + (c : 𝕜) • A v₁ = v := hA.resolvent_add_smul_apply hc v
  calc ⟪(u₁ : H), v⟫ = ⟪(u₁ : H), (v₁ : H) + (c : 𝕜) • A v₁⟫ := by rw [hv]
    _ = ⟪(u₁ : H), v₁⟫ + (c : 𝕜) * ⟪(u₁ : H), A v₁⟫ := by
        rw [inner_add_right, inner_smul_right]
    _ = ⟪(u₁ : H), v₁⟫ + (c : 𝕜) * ⟪A u₁, (v₁ : H)⟫ := by rw [hs u₁ v₁]
    _ = ⟪(u₁ : H) + (c : 𝕜) • A u₁, (v₁ : H)⟫ := by
        rw [inner_add_left, inner_smul_left, conj_ofReal]
    _ = ⟪u, v₁⟫ := by rw [hu]

/-- Let $H$ be a Hilbert space, let $A$ be a symmetric maximal monotone operator and let $c > 0$.
Then the Yosida approximation $A_c$ is self-adjoint. This is $A_\lambda^* = A_\lambda$ in the
proof of Theorem 7.7 of [brezis2011functional]. -/
theorem IsMaximalMonotone.isSelfAdjoint_yosida (hA : A.IsMaximalMonotone)
    (hs : A.IsFormalAdjoint A) {c : ℝ} (hc : 0 < c) : IsSelfAdjoint (A.yosida c) := by
  have hJ : ∀ u v, ⟪A.resolvent c u, v⟫ = ⟪u, A.resolvent c v⟫ := fun u v =>
    (hA.isSelfAdjoint_resolvent hs hc).isSymmetric u v
  refine LinearMap.IsSymmetric.isSelfAdjoint fun u v => ?_
  simp only [ContinuousLinearMap.coe_coe, yosida_apply, inner_smul_left, inner_smul_right,
    inner_sub_left, inner_sub_right, conj_ofReal]
  rw [hJ u v]

/-- Let $H$ be a Hilbert space. A symmetric maximal monotone operator $A$ on $H$ is self-adjoint:
$A^* = A$. This is Proposition 7.6 of [brezis2011functional].

Every symmetric operator satisfies $A \subseteq A^*$. Conversely, for $u \in D(A^*)$ and
$f = u + A^* u$, one has $\langle f, J_1 w \rangle = \langle u, w \rangle$ for every $w$. So
$u = J_1 f \in D(A)$, because $J_1$ is self-adjoint. -/
theorem IsMaximalMonotone.isSelfAdjoint_of_isFormalAdjoint (hA : A.IsMaximalMonotone)
    (hs : A.IsFormalAdjoint A) : IsSelfAdjoint A := by
  have hd := hA.dense_domain
  have hle : A ≤ A† := hs.le_adjoint hd
  rw [isSelfAdjoint_def]
  refine (eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun u hu => ?_)).symm
  set f : H := u + A† ⟨u, hu⟩ with hf
  have hJ : ∀ x y, ⟪A.resolvent 1 x, y⟫ = ⟪x, A.resolvent 1 y⟫ := fun x y =>
    (hA.isSelfAdjoint_resolvent hs one_pos).isSymmetric x y
  have key : A.resolvent 1 f = u := by
    refine ext_inner_right 𝕜 fun w => ?_
    rw [hJ]
    set w₁ : A.domain := ⟨A.resolvent 1 w, hA.resolvent_apply_mem_domain one_pos w⟩
    have hw : (w₁ : H) + A w₁ = w := by
      have := hA.resolvent_add_smul_apply one_pos w
      rwa [ofReal_one, one_smul] at this
    calc ⟪f, (w₁ : H)⟫ = ⟪u, (w₁ : H)⟫ + ⟪A† ⟨u, hu⟩, (w₁ : H)⟫ := by rw [hf, inner_add_left]
      _ = ⟪u, (w₁ : H)⟫ + ⟪u, A w₁⟫ := by rw [adjoint_isFormalAdjoint hd ⟨u, hu⟩ w₁]
      _ = ⟪u, (w₁ : H) + A w₁⟫ := by rw [inner_add_right]
      _ = ⟪u, w⟫ := by rw [hw]
  rw [← key]
  exact hA.resolvent_apply_mem_domain one_pos f

end SelfAdjoint

/-!
### Maximal monotonicity and the adjoint

These results are Remark 8 of Chapter 7 of [brezis2011functional].
-/

section Adjoint

variable [CompleteSpace H]

/-- Let $H$ be a Hilbert space and let $A$ be maximal monotone. Then the adjoint $A^*$ is monotone.
This is in Remark 8 of Chapter 7 of [brezis2011functional].

For $v \in D(A^*)$, $\operatorname{Re} \langle A^* v, J_c v \rangle = \operatorname{Re} \langle
v, A (J_c v) \rangle = \operatorname{Re} \langle A_c v, v \rangle \ge 0$, and $J_c v \to v$ as
$c \to 0^+$. -/
theorem IsMaximalMonotone.isMonotone_adjoint (hA : A.IsMaximalMonotone) : A†.IsMonotone := by
  intro v
  have hd := hA.dense_domain
  have h1 : Tendsto (fun c : ℝ => re ⟪A† v, A.resolvent c v⟫) (𝓝[>] 0)
      (𝓝 (re ⟪A† v, (v : H)⟫)) :=
    (continuous_re.tendsto _).comp (tendsto_const_nhds.inner (hA.tendsto_resolvent_apply v))
  refine ge_of_tendsto h1 ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  rw [show ⟪A† v, A.resolvent c v⟫ =
      ⟪(v : H), A ⟨A.resolvent c v, hA.resolvent_apply_mem_domain hc v⟩⟫ from
      adjoint_isFormalAdjoint hd v ⟨_, _⟩, ← hA.yosida_apply_eq_apply_resolvent hc, inner_re_symm]
  exact hA.re_inner_yosida_nonneg hc v

/-- Let $H$ be a Hilbert space and let $A$ be densely defined. Then the adjoint of $I + A$ is
$I + A^*$:
$$(I + A)^* = I + A^*.$$
This is used in Remark 8 of Chapter 7 of [brezis2011functional].

Both domains are the set of $y$ such that $x \mapsto \langle y, A x \rangle$ is continuous on
$D(A)$, and $\langle y + A^* y, x \rangle = \langle y, x + A x \rangle$. The operator $I + A$ is
written `LinearMap.id +ᵥ A`. -/
theorem adjoint_id_vadd (hd : Dense (A.domain : Set H)) :
    ((LinearMap.id : H →ₗ[𝕜] H) +ᵥ A)† = (LinearMap.id : H →ₗ[𝕜] H) +ᵥ A† := by
  have hd' : Dense ((((LinearMap.id : H →ₗ[𝕜] H) +ᵥ A).domain : Submodule 𝕜 H) : Set H) := hd
  have hdom : ((LinearMap.id : H →ₗ[𝕜] H) +ᵥ A)†.domain = A†.domain := by
    ext y
    rw [mem_adjoint_domain_iff, mem_adjoint_domain_iff]
    have hc : Continuous ((innerₛₗ 𝕜 y).comp A.domain.subtype) :=
      ((innerSL 𝕜 y).comp A.domain.subtypeL).continuous
    have heq : ((innerₛₗ 𝕜 y).comp ((LinearMap.id : H →ₗ[𝕜] H) +ᵥ A).toFun :
        A.domain →ₗ[𝕜] 𝕜) = (innerₛₗ 𝕜 y).comp A.domain.subtype + (innerₛₗ 𝕜 y).comp A.toFun := by
      ext x
      simp [inner_add_right]
    rw [heq, LinearMap.coe_add]
    exact ⟨fun h => by simpa using h.sub hc, fun h => hc.add h⟩
  refine LinearPMap.ext hdom fun x hx hx' => ?_
  refine adjoint_apply_eq hd' ⟨x, hx⟩ fun z => ?_
  rw [vadd_apply, vadd_apply, LinearMap.id_apply, LinearMap.id_apply, inner_add_left,
    inner_add_right, adjoint_isFormalAdjoint hd ⟨x, hx'⟩ z]

/-- Let $H$ be a Hilbert space. If $A$ is maximal monotone, then its adjoint $A^*$ is maximal
monotone. This is the forward implication of Remark 8 of Chapter 7 of [brezis2011functional].

For $f \in H$, the vector $u = J_1^* f$ satisfies $\langle u, v + A v \rangle = \langle f, J_1
(v + A v) \rangle = \langle f, v \rangle$ for all $v \in D(A)$. So $u \in D(A^*)$ and
$A^* u = f - u$. -/
theorem IsMaximalMonotone.adjoint (hA : A.IsMaximalMonotone) : A†.IsMaximalMonotone := by
  refine ⟨hA.isMonotone_adjoint, fun f => ?_⟩
  have hd := hA.dense_domain
  set u := ContinuousLinearMap.adjoint (A.resolvent 1) f with hu
  have key : ∀ v : A.domain, ⟪u, (v : H) + A v⟫ = ⟪f, v⟫ := fun v => by
    rw [hu, ContinuousLinearMap.adjoint_inner_left]
    congr 1
    have := hA.resolvent_apply_add_smul one_pos v
    rwa [ofReal_one, one_smul] at this
  have hsub : ∀ v : A.domain, ⟪f - u, (v : H)⟫ = ⟪u, A v⟫ := fun v => by
    rw [inner_sub_left, ← key v, inner_add_right]
    abel
  have hmem : u ∈ A†.domain := mem_adjoint_domain_of_exists u ⟨f - u, hsub⟩
  refine ⟨⟨u, hmem⟩, ?_⟩
  rw [adjoint_apply_eq hd ⟨u, hmem⟩ hsub]
  abel

/-- Let $H$ be a Hilbert space. An operator $A$ on $H$ is maximal monotone if and only if $A$ is
closed, $D(A)$ is dense, and both $A$ and $A^*$ are monotone. This is the second equivalence of
Remark 8 of Chapter 7 of [brezis2011functional], and the Hilbert-space case of Problem 16 there.

For the reverse implication, $R(I + A)$ is closed, because $I + A$ is closed and bounded below
by $\|u\| \le \|u + A u\|$. Also $R(I + A)^\perp = 0$: if $w \perp R(I + A)$, then
$w \in D(A^*)$ with $A^* w = -w$, and $0 \le \operatorname{Re} \langle A^* w, w \rangle =
-\|w\|^2$. -/
theorem isMaximalMonotone_iff_isClosed_dense_isMonotone :
    A.IsMaximalMonotone ↔
      A.IsClosed ∧ Dense (A.domain : Set H) ∧ A.IsMonotone ∧ A†.IsMonotone := by
  refine ⟨fun hA => ⟨hA.isClosed, hA.dense_domain, hA.isMonotone, hA.isMonotone_adjoint⟩, ?_⟩
  rintro ⟨hcl, hd, hm, hm'⟩
  set B : H →ₗ.[𝕜] H := (LinearMap.id : H →ₗ[𝕜] H) +ᵥ A with hB
  -- `I + A` is closed
  have hBcl : B.IsClosed := by
    have hA' : _root_.IsClosed (A.graph : Set (H × H)) := hcl
    have : (B.graph : Set (H × H)) =
        (fun p : H × H => (p.1, p.2 - p.1)) ⁻¹' (A.graph : Set (H × H)) := by
      ext ⟨x, y⟩
      simp only [SetLike.mem_coe, mem_graph_iff, Set.mem_preimage]
      constructor
      · rintro ⟨u, rfl, rfl⟩
        exact ⟨u, rfl, by change A u = (u : H) + A u - u; abel⟩
      · rintro ⟨u, hu, hAu⟩
        exact ⟨u, hu, by change (u : H) + A u = y; rw [hAu, hu]; abel⟩
    change _root_.IsClosed (B.graph : Set (H × H))
    rw [this]
    exact hA'.preimage (continuous_fst.prodMk (continuous_snd.sub continuous_fst))
  -- `R(I + A)` is closed
  have hrange : _root_.IsClosed (LinearMap.range B.toFun : Set H) :=
    hBcl.isClosed_range_of_norm_le (C := 1) fun u => by
      rw [one_mul]
      have := hm.norm_le_norm_add_smul zero_le_one u
      rwa [ofReal_one, one_smul] at this
  -- `R(I + A)ᗮ = 0`
  have horth : (LinearMap.range B.toFun)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    rw [Submodule.mem_orthogonal] at hw
    have hw' : ∀ v : A.domain, ⟪(-w : H), (v : H)⟫ = ⟪w, A v⟫ := fun v => by
      have h1 : ⟪(v : H) + A v, w⟫ = 0 := hw (B v) ⟨v, rfl⟩
      have h2 : ⟪w, (v : H)⟫ + ⟪w, A v⟫ = 0 := by
        rw [← inner_conj_symm w (v : H), ← inner_conj_symm w (A v), ← _root_.map_add,
          ← inner_add_left, h1, _root_.map_zero]
      rw [inner_neg_left]
      exact neg_eq_of_add_eq_zero_right h2
    have hmem : w ∈ A†.domain := mem_adjoint_domain_of_exists w ⟨-w, hw'⟩
    have hval : A† ⟨w, hmem⟩ = -w := adjoint_apply_eq hd ⟨w, hmem⟩ hw'
    have := hm' ⟨w, hmem⟩
    rw [hval, inner_neg_left, _root_.map_neg, inner_self_eq_norm_sq] at this
    have h0 : ‖w‖ ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0)
  have htop : LinearMap.range B.toFun = ⊤ := by
    have : CompleteSpace (LinearMap.range B.toFun) := hrange.completeSpace_coe
    exact Submodule.orthogonal_eq_bot_iff.1 horth
  exact IsMaximalMonotone.of_range_id_vadd_eq_top hm htop

/-- Let $H$ be a Hilbert space and let $A$ be a closed, densely defined operator on $H$ whose
adjoint $A^*$ is densely defined. Then $A$ is maximal monotone if and only if $A^*$ is maximal
monotone. This is the first equivalence of Remark 8 of Chapter 7 of [brezis2011functional].

For the reverse implication, $A \subseteq A^{**}$ and $A^{**}$ is monotone, so $A$ is monotone,
and the second equivalence `LinearPMap.isMaximalMonotone_iff_isClosed_dense_isMonotone` applies. -/
theorem isMaximalMonotone_iff_adjoint (hcl : A.IsClosed) (hd : Dense (A.domain : Set H))
    (hd' : Dense (A†.domain : Set H)) : A.IsMaximalMonotone ↔ A†.IsMaximalMonotone := by
  refine ⟨fun hA => hA.adjoint, fun hA => ?_⟩
  rw [isMaximalMonotone_iff_isClosed_dense_isMonotone]
  refine ⟨hcl, hd, ?_, hA.isMonotone⟩
  have hle : A ≤ A†† := (adjoint_isFormalAdjoint hd).le_adjoint hd'
  have hm := hA.isMonotone_adjoint
  intro v
  rw [apply_comp_inclusion hle v]
  exact hm (Submodule.inclusion hle.1 v)

/-- Let $H$ be a Hilbert space and let $A$ be a closed, densely defined operator on $H$ whose
adjoint $A^*$ is densely defined. Then $A^{**} = A$.

The proof works with graphs. The graph of $A^{**}$ comes from the graph of $A$, a closed
subspace of the Hilbert space `WithLp 2 (H × H)`, by taking the adjoint construction twice, and
a closed subspace is its own double orthogonal complement. This is used in Remark 8 of Chapter 7
of [brezis2011functional], with the definition of the adjoint in §2.6 there. -/
theorem adjoint_adjoint (hcl : A.IsClosed) (hd : Dense (A.domain : Set H))
    (hd' : Dense (A†.domain : Set H)) : A†† = A := by
  refine eq_of_eq_graph ?_
  rw [adjoint_graph_eq_graph_adjoint hd', adjoint_graph_eq_graph_adjoint hd]
  refine le_antisymm (fun p hp => ?_) (fun p hp => ?_)
  · rw [Submodule.mem_adjoint_iff] at hp
    by_contra hpg
    have hA' : _root_.IsClosed (A.graph : Set (H × H)) := hcl
    -- the graph, transported to the Hilbert space `WithLp 2 (H × H)`
    set K : Submodule 𝕜 (WithLp 2 (H × H)) :=
      A.graph.map (WithLp.linearEquiv 2 𝕜 (H × H)).symm.toLinearMap with hK
    have hKmem : ∀ x, x ∈ K ↔ ofLp x ∈ A.graph := fun x => by
      rw [hK, Submodule.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨ofLp x, hx, rfl⟩
    have hKcl : _root_.IsClosed (K : Set (WithLp 2 (H × H))) := by
      have : (K : Set (WithLp 2 (H × H))) = ofLp ⁻¹' (A.graph : Set (H × H)) := by
        ext x
        exact hKmem x
      rw [this]
      exact hA'.preimage (WithLp.prod_continuous_ofLp _ _ _)
    have : CompleteSpace K := hKcl.completeSpace_coe
    have hpK : toLp 2 p ∉ K := fun h => hpg ((hKmem _).1 h)
    rw [← Submodule.orthogonal_orthogonal K] at hpK
    have hne : ¬ ∀ u ∈ Kᗮ, ⟪u, toLp 2 p⟫ = 0 := fun h => hpK ((Submodule.mem_orthogonal _ _).2 h)
    simp only [not_forall, exists_prop] at hne
    obtain ⟨q, hqK, hq⟩ := hne
    -- `(q₂, -q₁)` lies in the adjoint of the graph
    have hq' : ((ofLp q).2, -(ofLp q).1) ∈ A.graph.adjoint := by
      rw [Submodule.mem_adjoint_iff]
      intro a b hab
      have h1 := (Submodule.mem_orthogonal _ _).1 hqK (toLp 2 (a, b)) ((hKmem _).2 hab)
      rw [WithLp.prod_inner_apply] at h1
      rw [inner_neg_right]
      linear_combination h1
    have h2 := hp _ _ hq'
    apply hq
    rw [WithLp.prod_inner_apply]
    rw [inner_neg_left] at h2
    linear_combination -h2
  · rw [Submodule.mem_adjoint_iff]
    intro a b hab
    rw [Submodule.mem_adjoint_iff] at hab
    have h1 := hab p.1 p.2 hp
    have h2 : ⟪p.1, b⟫ - ⟪p.2, a⟫ = 0 := by linear_combination -h1
    rw [← inner_conj_symm b, ← inner_conj_symm a, ← _root_.map_sub, h2, _root_.map_zero]

end Adjoint

section Shift

variable {B : H →ₗ.[𝕜] H}

/-! ### Prepending an entry, and the shift $A + c I$ -/

namespace PowDomain

variable {k : ℕ}

/-- The **prepending constructor**: for $u \in D(A)$ and $y \in D(A^k)$ whose entry of index $0$ is
$A u$, the element $(u, A u, \dots, A^{k+1} u)$ of $D(A^{k+1})$, whose entries are $u$ followed
by the entries of $y$. The constructor `LinearPMap.PowDomain.snoc` adds an entry at the other
end. -/
def cons (u : A.domain) (y : A.PowDomain k) (h : A u = applyL A k 0 y) : A.PowDomain (k + 1) :=
  mk A (Fin.cons (u : H) fun i => applyL A k i y) fun i => by
    induction i using Fin.cases with
    | zero => exact exists_apply_eq_of_eq u.2 h (by simp) (by simp)
    | succ i =>
      exact exists_apply_eq_of_eq (applyL_mem_domain y i) (apply_applyL y i)
        (by rw [← Fin.succ_castSucc, Fin.cons_succ]) (by rw [Fin.cons_succ])

/-- The entry of index $0$ of `cons u y h` is $u$. -/
@[simp]
theorem applyL_cons_zero (u : A.domain) (y : A.PowDomain k) (h) :
    applyL A (k + 1) 0 (cons u y h) = u := by
  unfold cons
  rw [applyL_mk, Fin.cons_zero]

/-- The entries $1, \dots, k + 1$ of `cons u y h` are those of $y$. -/
@[simp]
theorem applyL_cons_succ (u : A.domain) (y : A.PowDomain k) (h) (i : Fin (k + 1)) :
    applyL A (k + 1) i.succ (cons u y h) = applyL A k i y := by
  unfold cons
  rw [applyL_mk, Fin.cons_succ]

/-- Dropping the first entry undoes `LinearPMap.PowDomain.cons`: `shiftL A k (cons u y h) = y`. -/
@[simp]
theorem shiftL_cons (u : A.domain) (y : A.PowDomain k) (h) : shiftL A k (cons u y h) = y :=
  PowDomain.ext fun i => by rw [applyL_shiftL, applyL_cons_succ]

/-- The norm of `cons u y h` satisfies $\|\mathrm{cons}(u, y)\|^2 = \|u\|^2 + \|y\|^2$. -/
theorem norm_cons_sq (u : A.domain) (y : A.PowDomain k) (h) :
    ‖cons u y h‖ ^ 2 = ‖(u : H)‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [norm_sq_eq, norm_sq_eq, Fin.sum_univ_succ, applyL_cons_zero]
  simp only [applyL_cons_succ]

/-- The norm of `cons u y h` satisfies $\|\mathrm{cons}(u, y)\| \le \|u\| + \|y\|$. -/
theorem norm_cons_le (u : A.domain) (y : A.PowDomain k) (h) :
    ‖cons u y h‖ ≤ ‖(u : H)‖ + ‖y‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [norm_cons_sq]
  nlinarith [norm_nonneg (u : H), norm_nonneg y]

/-- A vector $u \in H$ lies in $D(A^{k+1})$ if and only if $u \in D(A)$ and $A u \in D(A^k)$. This
is the recursive description of the domains of the powers, by `LinearPMap.PowDomain.shiftL` and
`LinearPMap.PowDomain.cons`.

Here "$u$ lies in $D(A^k)$" means that $u$ is the entry of index $0$ of an element of
`A.PowDomain k`. -/
theorem exists_applyL_zero_eq_succ_iff {u : H} :
    (∃ x : A.PowDomain (k + 1), applyL A (k + 1) 0 x = u) ↔
      ∃ hu : u ∈ A.domain, ∃ y : A.PowDomain k, applyL A k 0 y = A ⟨u, hu⟩ := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨applyL_mem_domain x 0, shiftL A k x, applyL_zero_shiftL x⟩
  · rintro ⟨hu, y, hy⟩
    exact ⟨cons ⟨u, hu⟩ y hy.symm, applyL_cons_zero _ _ _⟩

end PowDomain

open PowDomain

/-- The relation **$B = A + c I$** between two operators $B$ and $A$ on $H$ and a scalar
$c \in \mathbb{K}$: $D(B) = D(A)$, and $B u = A u + c u$ for every $u$ in this domain.

The operator `(c • LinearMap.id) +ᵥ A` satisfies it (`LinearPMap.isAddSmulId_smul_id_vadd`), and
so does `LinearMap.id +ᵥ A` with $c = 1$ (`LinearPMap.isAddSmulId_id_vadd`). The relation is
symmetric with $c$ replaced by $-c$ (`LinearPMap.IsAddSmulId.symm`). -/
structure IsAddSmulId (B A : H →ₗ.[𝕜] H) (c : 𝕜) : Prop where
  /-- The domains agree: $D(B) = D(A)$. -/
  mem_domain_iff : ∀ u, u ∈ B.domain ↔ u ∈ A.domain
  /-- The operators differ by $c I$: $B u = A u + c u$. -/
  apply_eq : ∀ (u : H) (hB : u ∈ B.domain) (hA : u ∈ A.domain), B ⟨u, hB⟩ = A ⟨u, hA⟩ + c • u

variable (A) in
/-- For every $c \in \mathbb{K}$, the operator $c I + A$, written `(c • LinearMap.id) +ᵥ A`, is
$A + c I$. -/
theorem isAddSmulId_smul_id_vadd (c : 𝕜) :
    IsAddSmulId ((c • LinearMap.id : H →ₗ[𝕜] H) +ᵥ A) A c :=
  ⟨fun _ => Iff.rfl, fun u hB hA => by
    rw [vadd_apply, LinearMap.smul_apply, LinearMap.id_apply, add_comm]⟩

variable (A) in
/-- The operator $I + A$, written `LinearMap.id +ᵥ A`, is $A + 1 \cdot I$. -/
theorem isAddSmulId_id_vadd : IsAddSmulId ((LinearMap.id : H →ₗ[𝕜] H) +ᵥ A) A 1 :=
  ⟨fun _ => Iff.rfl, fun u hB hA => by
    rw [vadd_apply, LinearMap.id_apply, add_comm, one_smul]⟩

/-- If $B = A + c I$, then $A = B + (-c) I$. -/
theorem IsAddSmulId.symm {c : 𝕜} (h : IsAddSmulId B A c) : IsAddSmulId A B (-c) :=
  ⟨fun u => (h.mem_domain_iff u).symm, fun u hA hB => by
    rw [h.apply_eq u hB hA, neg_smul, add_neg_cancel_right]⟩

/-- If $B = A + c I$ and $B$ is closed, then $A$ is closed.

The graph of $A$ is the preimage of the graph of $B$ under the homeomorphism
$(x, y) \mapsto (x, y + c x)$. -/
theorem IsAddSmulId.isClosed {c : 𝕜} (h : IsAddSmulId B A c) (hB : B.IsClosed) : A.IsClosed := by
  have hΦ : Continuous fun p : H × H => (p.1, p.2 + c • p.1) := by fun_prop
  have hgraph : (A.graph : Set (H × H)) =
      (fun p : H × H => (p.1, p.2 + c • p.1)) ⁻¹' (B.graph : Set (H × H)) := by
    ext ⟨x, y⟩
    simp only [SetLike.mem_coe, mem_graph_iff, Set.mem_preimage]
    constructor
    · rintro ⟨z, rfl, hz2⟩
      refine ⟨⟨z, (h.mem_domain_iff _).2 z.2⟩, rfl, ?_⟩
      have e := h.apply_eq (z : H) ((h.mem_domain_iff _).2 z.2) z.2
      have e' : A ⟨(z : H), z.2⟩ = y := hz2
      rw [e, e']
    · rintro ⟨z, rfl, hz2⟩
      refine ⟨⟨z, (h.mem_domain_iff _).1 z.2⟩, rfl, ?_⟩
      have e := h.apply_eq (z : H) z.2 ((h.mem_domain_iff _).1 z.2)
      have e2 : B ⟨(z : H), z.2⟩ = y + c • (z : H) := hz2
      rw [e2] at e
      exact (add_right_cancel e).symm
  change _root_.IsClosed (A.graph : Set (H × H))
  rw [hgraph]
  exact hB.preimage hΦ

namespace IsAddSmulId

variable {c : 𝕜}

variable (A B) in
/-- The transport $D(B^0) \to D(A^0)$; both spaces are $H$, and the map keeps the vector. -/
noncomputable def transportZero : B.PowDomain 0 →L[𝕜] A.PowDomain 0 :=
  LinearMap.mkContinuous
    { toFun := fun x => PowDomain.mk A (fun _ => applyL B 0 0 x) fun i => i.elim0
      map_add' := fun x y => PowDomain.ext fun i => by simp
      map_smul' := fun a x => PowDomain.ext fun i => by simp }
    1 fun x => by
      rw [one_mul]
      change ‖PowDomain.mk A (fun _ => applyL B 0 0 x) fun i => i.elim0‖ ≤ ‖x‖
      refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
      rw [norm_sq_eq, Fin.sum_univ_one, applyL_mk]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_applyL_apply_le _ _) 2

/-- The transport $D(B^0) \to D(A^0)$ preserves the entry of index $0$. -/
theorem applyL_zero_transportZero (x : B.PowDomain 0) :
    applyL A 0 0 (transportZero A B x) = applyL B 0 0 x :=
  rfl

/-- If $B = A + c I$, then the entry of index $0$ of an element of $D(B^{k+1})$ lies in $D(A)$. -/
theorem applyL_zero_mem_domain (h : IsAddSmulId B A c) {k : ℕ} (x : B.PowDomain (k + 1)) :
    applyL B (k + 1) 0 x ∈ A.domain :=
  (h.mem_domain_iff _).1 (applyL_mem_domain x 0)

/-- Let $B = A + c I$, and let $\Phi : D(B^k) \to D(A^k)$ be a bounded linear map that preserves the
entry of index $0$. Then for $x = (u, B u, \dots) \in D(B^{k+1})$,
$$A u = \bigl(\Phi(B u, \dots) - c\, \Phi(u, \dots)\bigr)_0.$$
This is the identity behind the transport step. Here $(B u, \dots)$ and $(u, \dots)$ are the
tuples `shiftL B k x` and `castL B k x`. -/
theorem apply_eq_applyL_zero_sub (h : IsAddSmulId B A c) {k : ℕ}
    (Φ : B.PowDomain k →L[𝕜] A.PowDomain k) (hΦ : ∀ y, applyL A k 0 (Φ y) = applyL B k 0 y)
    (x : B.PowDomain (k + 1)) :
    A ⟨applyL B (k + 1) 0 x, h.applyL_zero_mem_domain x⟩ =
      applyL A k 0 (Φ (shiftL B k x) - c • Φ (castL B k x)) := by
  have e1 : applyL A k 0 (Φ (shiftL B k x) - c • Φ (castL B k x))
      = applyL B k 0 (shiftL B k x) - c • applyL B k 0 (castL B k x) := by
    rw [_root_.map_sub, _root_.map_smul, hΦ, hΦ]
  have e2 : applyL B k 0 (shiftL B k x) = B ⟨applyL B (k + 1) 0 x, applyL_mem_domain x 0⟩ :=
    applyL_zero_shiftL x
  have e3 : applyL B k 0 (castL B k x) = applyL B (k + 1) 0 x := rfl
  have e4 := h.apply_eq (applyL B (k + 1) 0 x) (applyL_mem_domain x 0)
    (h.applyL_zero_mem_domain x)
  rw [e1, e2, e3, e4, add_sub_cancel_right]

/-- **One step of the transport.** Let $B = A + c I$, and let $\Phi : D(B^k) \to D(A^k)$ be a
bounded linear map that preserves the entry of index $0$. The bounded linear map
$D(B^{k+1}) \to D(A^{k+1})$ sends $x = (u, B u, \dots)$ to
$$\mathrm{cons}\bigl(u, \Phi(B u, \dots) - c\, \Phi(u, \dots)\bigr),$$
whose entries are $u$ followed by those of $\Phi(B u, \dots) - c\, \Phi(u, \dots)$, the element
over $A u = B u - c u$. -/
noncomputable def transportStep (h : IsAddSmulId B A c) {k : ℕ}
    (Φ : B.PowDomain k →L[𝕜] A.PowDomain k) (hΦ : ∀ y, applyL A k 0 (Φ y) = applyL B k 0 y) :
    B.PowDomain (k + 1) →L[𝕜] A.PowDomain (k + 1) :=
  LinearMap.mkContinuous
    { toFun := fun x => cons ⟨applyL B (k + 1) 0 x, h.applyL_zero_mem_domain x⟩
        (Φ (shiftL B k x) - c • Φ (castL B k x)) (h.apply_eq_applyL_zero_sub Φ hΦ x)
      map_add' := fun x y => PowDomain.ext fun i => by
        induction i using Fin.cases with
        | zero => simp
        | succ i =>
          simp only [_root_.map_add, applyL_cons_succ, _root_.map_sub, _root_.map_smul, smul_add]
          abel
      map_smul' := fun a x => PowDomain.ext fun i => by
        induction i using Fin.cases with
        | zero => simp
        | succ i =>
          simp only [_root_.map_smul, applyL_cons_succ, _root_.map_sub, RingHom.id_apply, smul_sub,
            smul_comm a c] }
    (1 + (1 + ‖c‖) * ‖Φ‖) fun x => by
      refine (norm_cons_le ⟨applyL B (k + 1) 0 x, h.applyL_zero_mem_domain x⟩
        (Φ (shiftL B k x) - c • Φ (castL B k x)) (h.apply_eq_applyL_zero_sub Φ hΦ x)).trans ?_
      have h1 : ‖applyL B (k + 1) 0 x‖ ≤ ‖x‖ := norm_applyL_apply_le _ _
      have h2 : ‖Φ (shiftL B k x) - c • Φ (castL B k x)‖ ≤ (1 + ‖c‖) * ‖Φ‖ * ‖x‖ := by
        calc ‖Φ (shiftL B k x) - c • Φ (castL B k x)‖
            ≤ ‖Φ (shiftL B k x)‖ + ‖c • Φ (castL B k x)‖ := norm_sub_le _ _
          _ ≤ ‖Φ‖ * ‖x‖ + ‖c‖ * (‖Φ‖ * ‖x‖) := by
            rw [norm_smul]
            gcongr
            · exact (Φ.le_opNorm _).trans (by gcongr; exact norm_shiftL_apply_le x)
            · exact (Φ.le_opNorm _).trans (by gcongr; exact norm_castL_apply_le x)
          _ = (1 + ‖c‖) * ‖Φ‖ * ‖x‖ := by ring
      calc ‖((⟨applyL B (k + 1) 0 x, h.applyL_zero_mem_domain x⟩ : A.domain) : H)‖
            + ‖Φ (shiftL B k x) - c • Φ (castL B k x)‖
          ≤ ‖x‖ + (1 + ‖c‖) * ‖Φ‖ * ‖x‖ := add_le_add h1 h2
        _ = (1 + (1 + ‖c‖) * ‖Φ‖) * ‖x‖ := by ring

/-- The transport step preserves the entry of index $0$. -/
theorem applyL_zero_transportStep (h : IsAddSmulId B A c) {k : ℕ}
    (Φ : B.PowDomain k →L[𝕜] A.PowDomain k) (hΦ : ∀ y, applyL A k 0 (Φ y) = applyL B k 0 y)
    (x : B.PowDomain (k + 1)) :
    applyL A (k + 1) 0 (h.transportStep Φ hΦ x) = applyL B (k + 1) 0 x :=
  applyL_cons_zero ⟨applyL B (k + 1) 0 x, h.applyL_zero_mem_domain x⟩
    (Φ (shiftL B k x) - c • Φ (castL B k x)) (h.apply_eq_applyL_zero_sub Φ hΦ x)

/-- The transports $D(B^k) \to D(A^k)$ for every $k$, together with the property that they preserve
the entry of index $0$, by recursion on $k$. -/
noncomputable def transportAux (h : IsAddSmulId B A c) :
    ∀ k : ℕ, {Φ : B.PowDomain k →L[𝕜] A.PowDomain k // ∀ y, applyL A k 0 (Φ y) = applyL B k 0 y}
  | 0 => ⟨transportZero A B, applyL_zero_transportZero⟩
  | k + 1 => ⟨h.transportStep (h.transportAux k).1 (h.transportAux k).2,
      h.applyL_zero_transportStep _ _⟩

/-- **The transport for $B = A + c I$**: the bounded linear map $D(B^k) \to D(A^k)$ that sends
$(u, B u, \dots, B^k u)$ to $(u, A u, \dots, A^k u)$.

The spaces $D(B^k)$ and $D(A^k)$ are the same subspace of $H$
(`LinearPMap.IsAddSmulId.exists_applyL_zero_eq_iff`), but their norms differ, and this map
identifies them. The map is built by recursion on $k$ with
`LinearPMap.IsAddSmulId.transportStep`: since $A u = B u - c u$, the tuple over $u$ is
$\mathrm{cons}(u, \Phi_k(B u, \dots) - c\, \Phi_k(u, \dots))$. -/
noncomputable def transport (h : IsAddSmulId B A c) (k : ℕ) : B.PowDomain k →L[𝕜] A.PowDomain k :=
  (h.transportAux k).1

/-- The transport preserves the entry of index $0$: $(\mathrm{transport}\, x)_0 = x_0$. -/
@[simp]
theorem applyL_zero_transport (h : IsAddSmulId B A c) {k : ℕ} (x : B.PowDomain k) :
    applyL A k 0 (h.transport k x) = applyL B k 0 x :=
  (h.transportAux k).2 x

/-- If $B = A + c I$, then $D(B^k) = D(A^k)$ as subspaces of $H$: a vector $u$ is the entry of index
$0$ of an element of $D(B^k)$ if and only if it is the entry of index $0$ of an element of
$D(A^k)$. -/
theorem exists_applyL_zero_eq_iff (h : IsAddSmulId B A c) {k : ℕ} {u : H} :
    (∃ x : B.PowDomain k, applyL B k 0 x = u) ↔ ∃ x : A.PowDomain k, applyL A k 0 x = u :=
  ⟨fun ⟨x, hx⟩ => ⟨h.transport k x, by rw [applyL_zero_transport, hx]⟩,
    fun ⟨x, hx⟩ => ⟨h.symm.transport k x, by rw [applyL_zero_transport, hx]⟩⟩

end IsAddSmulId

end Shift

end LinearPMap
