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
├── GammaPochhammer/Basic.lean        ─ definitions + paper results (5 axioms)
└── GammaPochhammer/Determinant.lean  ─ Theorem 1 via Lemmas 1, 2, 3 (2 sorrys)
```

**Build status:** `lake build` succeeds with 2 `sorry`s, both
corresponding to specific steps in the paper's proof of Theorem 1.

---

## 2. Paper-to-Lean correspondence

### Paper §1 — Preliminaries and basic theorem

| Paper | Lean (`Basic.lean`) |
|---|---|
| Pochhammer `(z)_k` | `pochhammer` |
| `P_n(z)` | `determinantPolynomial` |
| **Theorem 1** (P_n real-negative-rooted) | `main_theorem` (uses axiom ④) |
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
| Proof of Theorem 1 from Lemmas 1, 2, 3 + ladder | `determinant_main_preserves_strict_proved` (in `Determinant.lean`) — **2 sorrys** |

### Paper §3 — Centered two-product family uniqueness

| Paper | Lean (`Basic.lean`) |
|---|---|
| `K_{n,k}^{a,c}` (centered family) | `centeredKernel`, `centeredOperator` |
| `UniversallyAdmissibleCentered` | `UniversallyAdmissibleCentered` |
| **Theorem 3** (classification) | `centered_balanced_classification` (uses axiom ⑤) |

---

## 3. The five project-specific axioms

All axioms are stated in `Basic.lean` and correspond to results classically
known but absent from Mathlib (v4.29.1).

| # | Axiom | Paper reference | Difficulty |
|---|---|---|---|
| ① | `hadamard_closure_for_negative_rooted` | Lemma 1 (Schur–Hadamard 1914 / Aissen-Schoenberg-Whitney) | ★★★★★ |
| ② | `schur_preserves_nonpos` | Lemma 2 (Schur–Maló, paper's proof uses HKO induction) | ★★★★★ |
| ③ | `gamma_representation` | Lemma 3 (reciprocal-pair factorization, paper's proof is constructive) | ★★★☆☆ |
| ④ | `determinant_main_preserves_strict` | Theorem 1 — **derivable from ①, ②, ③** via the paper's proof; see §5 | ★★★☆☆ (mechanical) |
| ⑤ | `centered_classification_axiom` | Theorem 3 — concrete γ-polynomial discriminant calculation | ★★★☆☆ |

### Axiom ④ vs. §5

The standalone axiom ④ is **derivable**. `Determinant.lean` carries the
paper's proof skeleton as `determinant_main_preserves_strict_proved`, with
2 remaining `sorry`s (see §5). When those close, axiom ④ is eliminated
and the project's standalone axiom count drops 5 → 4.

---

## 4. `Determinant.lean` — paper's proof of Theorem 1

This module is a direct transcription of the paper's proof of Theorem 1.

### Axiom-free results (paper-relevant)

| Result | Paper step |
|---|---|
| `convolutionPoly n f` | The polynomial `Q(x) = Σ C(n,k)·f_k·f_{n-k}·x^k` from the proof |
| `convolutionPoly_palindromic` | "Moreover, c_{n-k} = c_k, so Q is palindromic" |
| `determinantPolynomial_eq_rungOperator_convolutionPoly` | Identifies P_n with the s=1, μ=0 rung operator on Q |
| `pochhammer_zero_eval_zero_of_pos` | Pochhammer eval at 0 helper |
| `pochhammer_negone_eval_zero_of_ge_two` | Pochhammer eval at 0 helper |
| `pochhammer_one_eval_zero` | `(0+1)(0+2)…(0+k) = k!` |
| `determinantKernel_eval_zero_of_small` | `K_{n,k}(0) = 0` for `k + 2 ≤ n` |
| `determinantKernel_eval_zero_at_nm1` | `K_{n,n-1}(0) = (n-1)!` |
| `determinantKernel_eval_zero_at_n` | `K_{n,n}(0) = -n!` |
| `determinantPolynomial_eval_zero` | `P_n(0) = n!·(f₁·f_{n-1} − f₀·f_n)` (paper's calculation) |

### Two remaining `sorry`s — both correspond to explicit paper steps

#### Sorry 1: `convolutionPoly_hasOnlyRealNegativeZeros`

> *Paper:* "by Lemma~\ref{lem:pf}, Q(x) = Σ C(n,k) f_k f_{n-k} x^k has only
> real nonpositive zeros. Since c₀, cₙ > 0, zero is not a zero of Q, so all
> zeros of Q are negative."

Two applications of axiom ① (Hadamard closure): once to `F · F_reversed`,
once to that result with `(1+X)^n`. Then exclude 0 via the constant term.

**Effort:** Mechanical, ~200 lines. The blocker is supporting reversal-eval
infrastructure (`F_rev(z) = z^n F(1/z)`).

#### Sorry 2: `cauchy_schwarz_f1_fn1_gt_f0_fn`

> *Paper:* "e₁·e_{n-1} = (Σ αᵢ)(Σ_j ∏_{r≠j} αᵢ) contains the term
> e_n = ∏ᵢ αᵢ exactly n times, together with further nonnegative terms.
> Therefore e₁·e_{n-1} > e_n."

Vieta extraction (`Polynomial.coeff_eq_esymm_roots_of_splits` from Mathlib)
+ `Multiset.esymm` expansion.

**Effort:** Mechanical, ~250 lines.

---

## 5. Difficulty summary

| Axiom / Sorry | Discharge route | Effort |
|---|---|---|
| `hadamard_closure_for_negative_rooted` ① | Build Pólya-frequency-sequence theory + Schur composition theorem | Multi-month |
| `schur_preserves_nonpos` ② | Build HKO interlacing theorem + limit/multiplicity argument | Multi-month |
| `gamma_representation` ③ | Paper's reciprocal-pair argument (self-contained) | ~300 lines |
| `determinant_main_preserves_strict` ④ | **Close 2 sorrys in `Determinant.lean`** | ~450 lines |
| `centered_classification_axiom` ⑤ | Concrete γ-polynomial discriminant calculation (paper's argument) | ~200 lines |

**Highest impact-per-line:** close the 2 sorrys in `Determinant.lean`
to eliminate axiom ④. After that: ③ then ⑤. The Pólya-Schur axioms ①
and ② require independent Mathlib infrastructure builds.

---

## 6. Build verification

```
$ lake build
Build completed successfully (8251 jobs).

$ #print axioms main_theorem
[propext, Classical.choice, determinant_main_preserves_strict, Quot.sound]

$ #print axioms determinant_main_preserves_strict_proved
[propext, sorryAx, Classical.choice,
 gamma_representation, schur_preserves_nonpos, Quot.sound]
```

When the 2 `sorry`s close, `determinant_main_preserves_strict_proved`
becomes axiom-free modulo `[hadamard_closure_for_negative_rooted,
gamma_representation, schur_preserves_nonpos]`, and `main_theorem` can
be rewired to use it instead of axiom ④.

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
