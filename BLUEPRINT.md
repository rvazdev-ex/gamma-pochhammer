# GammaPochhammer — Lean Formalization Blueprint

This document maps the structure of the GammaPochhammer Lean project
against *"Gamma Operators for Pochhammer Kernels"* by R. Valencia.

## Project scope policy

The project formalizes exactly the paper's results: definitions, lemmas,
theorems, corollaries, and the auxiliary content required to prove them.
Auxiliary results not stated in the paper (small-`n` case computations,
universal-zero factorizations, etc.) have been removed.

---

## 1. Module structure

```
GammaPochhammer.lean                  ─ root
├── GammaPochhammer/Basic.lean        ─ definitions + paper results (4 axioms)
└── GammaPochhammer/Determinant.lean  ─ Theorem 1 via Lemmas 1, 2, 3 (no sorrys)
```

**Build status:** `lake build` succeeds with no `sorry`s. Theorem 1 is
fully derived from Lemmas 1, 2, 3.

---

## 2. Paper-to-Lean correspondence

### Paper §1 — Preliminaries and basic theorem

| Paper | Lean (`Basic.lean`) |
|---|---|
| Pochhammer `(z)_k` | `pochhammer` |
| `P_n(z)` | `determinantPolynomial` |
| **Theorem 1** (P_n real-negative-rooted) | `main_theorem` (uses axioms ①, ②, ③) |
| **Lemma 1** (Hadamard closure) | `Hadamard_closure_for_negative_rooted_polynomials` (axiom ①) |
| **Lemma 2** (Schur transform 𝓛) | `schur_transform_preserves_nonpos` + `schurTransform` (axiom ②) |
| **Lemma 3** (γ-representation) | `gamma_representation_of_palindromic_negative_rooted` + `gammaBasis`, `IsGammaExpansion`, `gammaPolynomial`, `PalindromicOfDegree` (axiom ③) |

### Paper §2 — Higher Pochhammer kernel ladder

| Paper | Lean (`Basic.lean`) |
|---|---|
| `λ_{s,q}` coefficients | `lambda` |
| `K_{n,k}^{[s,μ]}` (rung kernel) | `rungKernel` |
| `T_{s,μ}^{(n)}(Q)` (rung operator) | `rungOperator` |
| **A380113 triangle / `A(s,q)`** | `A380113` + `A380113_zero_zero`, `_left_edge`, `_internal` |
| **Lemma 4** (central-difference identity) | `central_difference_identity`, `central_difference` |
| **Lemma 5** (rung action) | `rung_action_on_gamma_basis`, `rung_action` |
| **Theorem 2** (the ladder formula) | `ladder_formula`, `pochhammer_kernel_ladder_formula`, `pochhammer_kernel_ladder`, `pochhammer_kernel_ladder_strict_shift` |
| **Corollary 1** (original kernel palindromic) | `original_kernel_palindromic` |
| **Corollary 2** (single-product kernel, s=0) | `single_product_kernel` |
| Proof of Theorem 1 from Lemmas 1, 2, 3 + ladder | `determinant_main_preserves_strict_proved` (in `Determinant.lean`) |

### Paper §3 — Centered two-product family uniqueness

| Paper | Lean (`Basic.lean`) |
|---|---|
| `K_{n,k}^{a,c}` (centered family) | `centeredKernel`, `centeredOperator` |
| `UniversallyAdmissibleCentered` | `UniversallyAdmissibleCentered` |
| **Theorem 3** (classification) | `centered_balanced_classification` (uses axiom ⑤) |

---

## 3. The four project-specific axioms

All axioms are stated in `Basic.lean` and correspond to results classically
known but absent from Mathlib (v4.29.1).

| # | Axiom | Paper reference | Difficulty |
|---|---|---|---|
| ① | `hadamard_closure_for_negative_rooted` | Lemma 1 (Schur–Hadamard 1914 / Aissen-Schoenberg-Whitney) | ★★★★★ |
| ② | `schur_preserves_nonpos` | Lemma 2 (Schur–Maló, paper's proof uses HKO induction) | ★★★★★ |
| ③ | `gamma_representation` | Lemma 3 (reciprocal-pair factorization, paper's proof is constructive) | ★★★☆☆ |
| ④ | `centered_classification_axiom` | Theorem 3 — concrete γ-polynomial discriminant calculation | ★★★☆☆ |

### Theorem 1 — now derived, not axiomatized

The original axiom `determinant_main_preserves_strict` has been **eliminated**.
`Determinant.lean` proves `determinant_main_preserves_strict_proved` from
the three other axioms (①, ②, ③) by following the paper's proof of Theorem 1.
The user-facing `main_theorem` lives in `Determinant.lean` and uses this
proved version. The project axiom count is now 4 (was 5).

---

## 4. `Determinant.lean` — paper's proof of Theorem 1

This module is a direct transcription of the paper's proof of Theorem 1.
**All steps are now proven** (no `sorry`s).

### Major theorems

| Result | Paper step |
|---|---|
| `convolutionPoly n f` | The polynomial `Q(x) = Σ C(n,k)·f_k·f_{n-k}·x^k` from the proof |
| `convolutionPoly_palindromic` | "Moreover, c_{n-k} = c_k, so Q is palindromic" |
| `convolutionPoly_hasOnlyRealNegativeZeros` | Q has only real negative zeros (via Hadamard closure × 2 + 0-exclusion) |
| `determinantPolynomial_eq_rungOperator_convolutionPoly` | Identifies P_n with the s=1, μ=0 rung operator on Q |
| `determinantPolynomial_eval_zero` | `P_n(0) = n!·(f₁·f_{n-1} − f₀·f_n)` (paper's calculation) |
| `cauchy_schwarz_f1_fn1_gt_f0_fn` | `f₁·f_{n-1} > f₀·f_n` (paper's `e_1·e_{n-1} > e_n` argument) |
| `determinant_main_preserves_strict_proved` | Theorem 1 itself |
| `main_theorem` | User-facing wrapper |

### Vieta infrastructure (axiom-free, paper-internal)

| Result | Role |
|---|---|
| `exists_factorization_real_neg` | Factor `p = C(leadingCoeff)·∏(X + α_i)` with `α_i > 0` |
| `multiset_esymm_cons`, `_one`, `_card` | Multiset.esymm recursion + base cases |
| `sum_mul_esymm_pred_card_ge` | Paper's `α.sum·α.esymm(n-1) ≥ n·α.prod` for non-negative multisets |
| `coeff_eq_lc_mul_esymm` | Vieta coefficient formula |
| `ordinaryGen_rev_eq_reverse` | Identifies the coefficient-reversed polynomial with `Polynomial.reverse` |
| `ordinaryGen_rev_hasOnlyRealNegativeZeros` | Reversed polynomial has neg roots (via `eval₂_reverse_eq_zero_iff`) |
| `one_add_X_pow_hasOnlyRealNegativeZeros` | `(1+X)^n` has root `-1` only |
| `hadamard_coeff` | Hadamard product coefficient formula |
| `convolutionPoly_eq_hadamard_iter` | Q = hadamard(hadamard(F, F_rev), (1+X)^n) |

---

## 5. Difficulty summary

| Axiom | Discharge route | Effort |
|---|---|---|
| `hadamard_closure_for_negative_rooted` ① | Build Pólya-frequency-sequence theory + Schur composition theorem | Multi-month |
| `schur_preserves_nonpos` ② | Build HKO interlacing theorem + limit/multiplicity argument | Multi-month |
| `gamma_representation` ③ | Paper's reciprocal-pair argument (self-contained) | ~300 lines |
| `centered_classification_axiom` ④ | Concrete γ-polynomial discriminant calculation (paper's argument) | ~200 lines |

The two Pólya-Schur axioms ① and ② require independent Mathlib infrastructure
builds and are not currently planned. Axiom ③ would be the next pragmatic target.

---

## 6. Build verification

```
$ lake build
Build completed successfully (8251 jobs).

$ #print axioms main_theorem
[propext, Classical.choice,
 gamma_representation,
 hadamard_closure_for_negative_rooted,
 schur_preserves_nonpos, Quot.sound]
```

`main_theorem` now depends only on the three classically-named axioms
(Lemmas 1, 2, 3 of the paper). The standalone `determinant_main_preserves_strict`
has been eliminated.

---

## 7. Notes on paper structure

The paper itself contains two pieces that don't feed into the main
theorems but are stated for context:

1. **The A380113 / coefficient-triangle subsection in §2.** Identifies
   the unsigned `λ_{s,q}` table with OEIS A380113 and gives the formula
   `T(s,q) = C(2s, s−q)`. This is a *structural identification* with the
   OEIS triangle, not a proof step in any later result. **Formalized in
   `Basic.lean` as `A380113`, `A380113_zero_zero`, `_left_edge`,
   `_internal`** — these establish the closed form but are not used
   by any downstream theorem.

2. **The final remark in §3** on γ-symbols. Provides interpretive
   context (`Γ ↦ Γ^(s)`, the elementary identity
   `(z)_j² − (z+1)_j(z-1)_j = j·(z)_{j-1}(z+1)_{j-1}`). Not formalized;
   it is a discussion, not a theorem.

Both pieces are paper content — they are kept in the formalization
(item 1) or left as descriptive context (item 2). Neither is a
"hanging proof" in the technical sense.
