import io, os

p = 'NumlibSurface/AtkinsonHan/Chapter02/Section08.lean'
s = io.open(p, encoding='utf-8').read()

old = """subspace because `λ` *is* an eigenvalue of `K`. The other half of the clause, the equality of
dimensions `dim N(λ - K) = dim N(conj λ - K*)` — that `λ - K` has Fredholm index zero — is not
stated: it needs the Riesz ascent–descent theory, which the backbone does not develop. -/"""
new = """subspace because `λ` *is* an eigenvalue of `K`. The other half of the clause, the equality of
dimensions, is `theorem_2_8_14_dim`. -/"""
assert s.count(old) == 1
s = s.replace(old, new)

anchor = """/-! ### Theorem 2.8.15: the spectral theorem for a compact self-adjoint operator -/"""
addition = """/-- **Theorem 2.8.14 (1)**, the dimension clause: for compact `K` on a Hilbert space and `λ ≠ 0`,
`dim N(λ - K) = dim N(conj λ - K*)`. Equivalently `λ - K` has Fredholm index zero, so the second
kind equation `(λ - K) u = f` has as many independent homogeneous solutions as the adjoint equation
has — which is what makes the solvability criterion (2.8.29) of `theorem_2_8_14` a finite set of
conditions of exactly the size of the deficiency. -/
theorem theorem_2_8_14_dim {K : V →L[𝕜] V} (hK : IsCompactOperator K) {l : 𝕜} (hl : l ≠ 0) :
    Module.finrank 𝕜 ((l • (1 : V →L[𝕜] V) - K).ker)
      = Module.finrank 𝕜 (((starRingEnd 𝕜) l • (1 : V →L[𝕜] V)
          - ContinuousLinearMap.adjoint K).ker) :=
  hK.finrank_ker_eq_finrank_ker_adjoint hl

"""
assert s.count(anchor) == 1
s = s.replace(anchor, addition + anchor)

old2 = """* `theorem_2_8_14`, `theorem_2_8_14_isCompl` — solvability of `(λ - K) u = f` and the orthogonal
  decomposition (2.8.30) it gives; `theorem_2_8_14_hasEigenvalue_adjoint` for the half of clause (1)
  that needs no ascent–descent theory, that `conj λ` is an eigenvalue of `K*`."""
new2 = """* `theorem_2_8_14`, `theorem_2_8_14_isCompl` — solvability of `(λ - K) u = f` and the orthogonal
  decomposition (2.8.30) it gives; `theorem_2_8_14_hasEigenvalue_adjoint` and `theorem_2_8_14_dim`
  for clause (1), that `conj λ` is an eigenvalue of `K*` and that the two null spaces have equal
  dimension."""
assert s.count(old2) == 1
s = s.replace(old2, new2)

old3 = """Also not stated: the dimension clause `dim N(λ - K) = dim N(conj λ - K*)` of
Theorem 2.8.14 (1), which is a Fredholm index statement and does not follow from the
ascent–descent theory that `Numlib/Analysis/Normed/Operator/Riesz` now provides.
"""
assert s.count(old3) == 1
s = s.replace(old3, "")

io.open(p + '.tmp', 'w', encoding='utf-8', newline='').write(s)
os.replace(p + '.tmp', p)
print('ok')
