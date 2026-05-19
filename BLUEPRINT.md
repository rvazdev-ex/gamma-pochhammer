# GammaPochhammer — Lean Formalization Blueprint

This document maps the structure of the GammaPochhammer Lean project,
identifies remaining gaps (axioms and `sorry`s), and quantifies the
difficulty of closing each.

The project formalizes results from *"Gamma Operators for Pochhammer
Kernels"*, including the main theorem that the Pochhammer determinant
polynomial `P_n(z)` has only real strictly negative zeros when its input
sequence's ordinary generating function does.

---

## 1. Module structure

```
GammaPochhammer.lean             ─ root
├── GammaPochhammer/Basic.lean   ─ definitions, paper theorems, 5 axioms
├── GammaPochhammer/Schur.lean   ─ partial discharge of schur_preserves_nonpos
└── GammaPochhammer/Determinant.lean ─ partial discharge of determinant_main_preserves_strict
```

**Build status:** `lake build` succeeds. 4 `sorry`s remain, isolated and named.

---

## 2. Core definitions

Defined in `Basic.lean`:

| Definition | Signature | Purpose |
|---|---|---|
| `toComplex` | `ℝ[X] → ℂ[X]` | Lift real polynomial to complex |
| `HasOnlyRealNonposZeros` | `ℝ[X] → Prop` | All complex roots are real `≤ 0` |
| `HasOnlyRealNegativeZeros` | `ℝ[X] → Prop` | All complex roots are real `< 0` |
| `HasDegree` | `ℝ[X] → ℕ → Prop` | `p ≠ 0 ∧ natDegree p = n` |
| `pochhammer a k` | `ℝ → ℕ → ℝ[X]` | `(X+a)(X+a+1)⋯(X+a+k-1)` |
| `ordinaryGen n f` | `ℕ → (ℕ → ℝ) → ℝ[X]` | `Σ_{k=0..n} f(k)·X^k` |
| `hadamard n A B` | Truncated `Σ aₖbₖ X^k` | Coeff-wise product |
| `PalindromicOfDegree n Q` | predicate | `c_k = c_{n-k}` for k ≤ n |
| `gammaBasis n j` | `X^j·(1+X)^(n-2j)` | γ-expansion basis |
| `IsGammaExpansion n m Q γ` | predicate | `Q = Σ γⱼ·gammaBasisⱼ` |
| `gammaPolynomial m γ` | `Σ γⱼ X^j` | The γ-polynomial of Q |
| `determinantKernel n k` | `(X)_k(X)_{n-k} − (X+1)_k(X-1)_{n-k}` | The k-th kernel |
| `determinantPolynomial n f` | `Σ f(k)·f(n-k)·C(n,k)·K_{n,k}` | The paper's `P_n` |
| `rungKernel n k s μ` | `Σ_q λ_{s,q}·(X+μ+q)_k(X+μ-q)_{n-k}` | s-th rung kernel |
| `rungOperator n s μ Q` | `Σ Q.coeff(k)·K_{n,k}^{[s,μ]}` | s-th rung operator |
| `schurTransform ell α B` | `Σ B.coeff(r)·(X)_r·(X+r+α)_{ell-r}` | Schur transform |
| `centeredKernel n k a c` | `(X+a)_k(X-a)_{n-k} − (X+c)_k(X-c)_{n-k}` | Centered family |
| `centeredOperator n a c Q` | `Σ Q.coeff(k)·centeredKernel(n,k,a,c)` | |
| `UniversallyAdmissibleCentered a c` | predicate | preserves on palindromic real-neg inputs |
| `convolutionPoly n f` | `ordinaryGen n (k ↦ f(k)·f(n-k)·C(n,k))` | Paper's `Q` |

---

## 3. The five project-specific axioms

All axioms are stated in `Basic.lean`. They correspond to results
classically known but **not** yet in Mathlib (v4.29.1).

### 3.1 `hadamard_closure_for_negative_rooted` (Basic.lean:251)

```
∀ (n : ℕ) (A B : ℝ[X]),
  (∀ k ≤ n, 0 ≤ A.coeff k) → (∀ k ≤ n, 0 ≤ B.coeff k) →
  HasOnlyRealNonposZeros A → HasOnlyRealNonposZeros B →
  HasOnlyRealNonposZeros (hadamard n A B)
```

**Classical name:** Schur–Hadamard theorem (Schur 1914). The Hadamard
(coefficient-wise) product of two polynomials with only real non-positive
zeros has only real non-positive zeros.

**Equivalent to:** Aissen–Schoenberg–Whitney theorem (finite Pólya-frequency
sequences are closed under Hadamard products).

**Difficulty (estimated):** ★★★★★ (research-level formalization).
Requires building Pólya-frequency-sequence theory and the
Schur composition theorem on totally non-negative matrices —
both absent from Mathlib.

**Downstream consumers (in this project):** Only
`Hadamard_closure_for_negative_rooted_polynomials` (wrapper),
plus indirectly the conjectural `convolutionPoly_hasOnlyRealNegativeZeros`
(currently `sorry`).

### 3.2 `schur_preserves_nonpos` (Basic.lean:259)

```
∀ (ell : ℕ) {α : ℝ}, 0 < α → ∀ (B : ℝ[X]),
  HasOnlyRealNonposZeros B → HasOnlyRealNonposZeros (schurTransform ell α B)
```

**Classical name:** Schur–Maló preservation theorem (Lemma 2 in the paper).
The Schur-type transform `B ↦ Σ B.coeff(r)·(X)_r·(X+r+α)_{ell-r}` preserves
real-non-positive-rootedness.

**Paper's proof (Lemma 2):** Induction on `ell` using
Hermite–Kakeya–Obreschkoff (HKO) interlacing theorem to combine
`(z+α+ell-1)·p(z)` with `z·p(z+1)`.

**Difficulty:** ★★★★★. Requires HKO interlacing theorem (not in Mathlib)
and a delicate continuity / limit argument for multiplicities. **Partial
work:** `Schur.lean` has the `ell = 0` and `ell = 1` cases proven axiom-free.

**Downstream consumers:** `single_product_kernel`, `pochhammer_kernel_ladder`,
`pochhammer_kernel_ladder_strict_shift`, `original_kernel_palindromic`, and
(transitively) `determinant_main_preserves_strict_proved`.

### 3.3 `gamma_representation` (Basic.lean:264)

```
∀ (n m ε : ℕ) (hε : ε = 0 ∨ ε = 1) (hn : n = 2m + ε) (Q : ℝ[X]),
  PalindromicOfDegree n Q → HasOnlyRealNegativeZeros Q →
  ∃ γ : ℕ → ℝ,
    IsGammaExpansion n m Q γ ∧
    HasOnlyRealNonposZeros (gammaPolynomial m γ)
```

**Classical name:** γ-positivity for real-rooted palindromic polynomials
(Lemma 3 in the paper). Specifically: not just that `γⱼ ≥ 0` (which would
be the standard γ-positivity), but that the entire γ-polynomial has real
non-positive zeros.

**Paper's proof (Lemma 3):** Uses reciprocal-pair factorization of
palindromic real-rooted Q, then the substitution `(x+ρ)(x+ρ⁻¹) = (1+x)² + λx`
to derive `Γ(t) = C·∏(1 + λᵢt)`.

**Difficulty:** ★★★☆☆. The paper's proof is fairly self-contained and
constructive; would require building the palindromic-factorization
infrastructure (extracting reciprocal pairs) and the basis-change argument.
Estimated ~300 lines.

**Downstream consumers:** `single_product_kernel`,
`pochhammer_kernel_ladder*`, `original_kernel_palindromic`, and
(transitively) `determinant_main_preserves_strict_proved`.

### 3.4 `determinant_main_preserves_strict` (Basic.lean:1708)

```
∀ (n : ℕ) (f : ℕ → ℝ), 2 ≤ n →
  HasDegree (ordinaryGen n f) n →
  HasOnlyRealNegativeZeros (ordinaryGen n f) →
  HasOnlyRealNegativeZeros (determinantPolynomial n f)
```

**Classical name:** Theorem 1 of the paper.

**Paper's proof:** Reduces to `pochhammer_kernel_ladder` (s=1, μ=0) via
Hadamard closure construction of the palindromic `Q_f = convolutionPoly`.
Then excludes 0 from the zero set via `P_n(0) = n!·(f(1)f(n-1) − f(0)f(n)) > 0`.

**Difficulty:** ★★★☆☆ — **but mostly bookkeeping**, as the paper supplies
the full proof using the other 3 axioms. See §6 for the partial
formalization (`Determinant.lean`).

**Downstream consumers:** `main_theorem` (in `Basic.lean`).

### 3.5 `centered_classification_axiom` (Basic.lean:1715)

```
∀ (a c : ℝ), a² ≠ c² →
  (UniversallyAdmissibleCentered a c ↔
    ({a², c²} : Set ℝ) = ({0, 1} : Set ℝ))
```

**Classical name:** Theorem 2 of the paper. Inside the centered
two-product family, only `{a², c²} = {0, 1}` is universally admissible.

**Paper's proof:** Uses degree-4 and degree-6 limiting γ-polynomials to
force `u + v = 1` then `u = 0`, then checks the converse via
Corollary "original-kernel-pal".

**Difficulty:** ★★★☆☆. The forward direction is a concrete computation
on two specific γ-polynomials; the converse follows from the corollary
(which depends on `gamma_representation`).

**Downstream consumers:** Only `centered_balanced_classification`
(wrapper). **Cosmetic** — no other theorems depend on it.

---

## 4. Theorem dependency graph

```
┌──────────────────────────────────────────────────────────────────────────┐
│                         AXIOMS (5 project-specific)                      │
├──────────────────────────────────────────────────────────────────────────┤
│ ① hadamard_closure_for_negative_rooted                                   │
│ ② schur_preserves_nonpos                                                 │
│ ③ gamma_representation                                                   │
│ ④ determinant_main_preserves_strict                                      │
│ ⑤ centered_classification_axiom                                          │
└──────────────────────────────────────────────────────────────────────────┘
        │              │            │             │              │
        ▼              ▼            ▼             ▼              ▼
  Hadamard_closure_… schur_transform_… gamma_repr_…  ──┐  centered_balanced_…
        │              │            │                  │
        │              │            │  (wrappers)      │  ── main_theorem
        │              │            │                  │     (depends only on ④)
        ▼              ▼            ▼                  │
    (leaf,           pochhammer_kernel_ladder          │
     no users        ├── pochhammer_kernel_ladder_strict_shift
     downstream)     ├── pochhammer_kernel_ladder_formula
                     ├── single_product_kernel
                     └── original_kernel_palindromic
                                  │
                                  │  (paper's strategy)
                                  ▼
              determinant_main_preserves_strict_proved
                       (Determinant.lean — skeleton, 4 sorrys)
```

**Critical-path axioms** (most downstream consumers):
- `schur_preserves_nonpos` and `gamma_representation`: feed 4 paper theorems each.
- `determinant_main_preserves_strict`: feeds `main_theorem`.

**Leaf axioms** (no downstream consumers beyond their immediate wrapper):
- `hadamard_closure_for_negative_rooted`
- `centered_classification_axiom`

---

## 5. Partial-discharge progress: `Schur.lean`

**Status:** Compiles axiom-free. 0 `sorry`s. Discharges `ell = 0, 1` cases only.

| Theorem | Status |
|---|---|
| `coeff_nonneg_of_hasOnlyRealNonposZeros` | ✅ Proved (induction on natDegree + root extraction) |
| `coeff_mul_coeff_nonneg` | ✅ Proved |
| `hasOnlyRealNonposZeros_C` | ✅ Proved |
| `hasOnlyRealNonposZeros_neg` | ✅ Proved |
| `exists_real_nonpos_root` | ✅ Proved (uses `Complex.exists_root`) |
| `exists_quotient_of_root` | ✅ Proved (uses `dvd_iff_isRoot`) |
| `schurTransform_zero` (closed form ell=0) | ✅ Proved |
| `schurTransform_one` (closed form ell=1) | ✅ Proved |
| `schur_preserves_nonpos_zero` | ✅ Proved (constant case is trivial) |
| `schur_preserves_nonpos_one` | ✅ Proved (linear case via sign analysis) |

**Gap to full discharge of `schur_preserves_nonpos`:** Requires
HKO interlacing theorem — research-level Mathlib infrastructure
(estimated multi-month project).

---

## 6. Partial-discharge progress: `Determinant.lean`

**Status:** Compiles. 4 `sorry`s remain (all isolated and named).

### Axiom-free results in this file

| Theorem | What it proves |
|---|---|
| `pochhammer_zero/one/negone_eval_neg_nat` | Pochhammer vanishing at small negative integers |
| `determinantKernel_eval_neg_universal` | `K_{n,k}(-m) = 0` for `2m+1 ≤ n`, **any k** |
| `determinantPolynomial_eval_neg_universal` | Hence `P_n(-m) = 0` (universal zeros) |
| `determinantPolynomial_two` | Closed form for n=2 (a constant) |
| `determinantPolynomial_three` | Closed form for n=3 (linear, root at -1) |
| `determinantKernel_four_zero..four` | All 5 K_{4,k} in factored form |
| `determinantPolynomial_four` | Closed form for n=4 |
| `determinant_preserves_strict_two` | Full n=2 preservation |
| `determinant_preserves_strict_three` | Full n=3 preservation |
| `convolutionPoly_palindromic` | Q_f is palindromic |
| `convolutionPoly_coeff` | Coefficient formula |
| `convolutionPoly_eval_zero` | `Q_f(0) = f(0)·f(n)` |
| `determinantPolynomial_eq_rungOperator_convolutionPoly` | Connection to rungOperator |
| `determinantPolynomial_eval_zero` | `P_n(0) = n!·(f(1)f(n-1) − f(0)f(n))` |
| `hasOnlyRealNegativeZeros_C` | Constants are trivially OK |
| `hasOnlyRealNegativeZeros_C_mul_X_add_C` | `c·(X+r)` for r > 0 |
| `hasOnlyRealNegativeZeros_mul` | Product preserves the predicate |
| `hasOnlyRealNegativeZeros_linear_pos` | Linear `aX + b` for a, b > 0 |

### Structural skeleton of the main theorem

`determinant_main_preserves_strict_proved` is in place. Its proof body
contains no `sorry`; it threads through these named sub-lemmas:

```
determinant_main_preserves_strict_proved
   ├─ convolutionPoly_palindromic                   ✅ proved
   ├─ convolutionPoly_hasOnlyRealNegativeZeros     ❌ SORRY (§6.1)
   ├─ pochhammer_kernel_ladder                      ✅ proved (Basic.lean, uses ②③)
   ├─ determinantPolynomial_eq_rungOperator…        ✅ proved
   ├─ determinantPolynomial_eval_zero               ✅ proved
   └─ cauchy_schwarz_f1_fn1_gt_f0_fn               ❌ SORRY (§6.4)
```

When the 4 sub-sorrys close, `determinant_main_preserves_strict_proved`
becomes axiom-free modulo `[hadamard_closure_for_negative_rooted,
gamma_representation, schur_preserves_nonpos]`, eliminating axiom ④ and
**reducing the project's axiom count from 5 to 4**.

---

## 7. Remaining `sorry`s — full inventory

### §6.1 `convolutionPoly_hasOnlyRealNegativeZeros` (Determinant.lean:497)

```
∀ (n : ℕ) (f : ℕ → ℝ),
  HasDegree (ordinaryGen n f) n →
  HasOnlyRealNegativeZeros (ordinaryGen n f) →
  HasOnlyRealNegativeZeros (convolutionPoly n f)
```

**Difficulty:** ★★★☆☆ — mechanical Lean engineering, no missing math.

**Proof plan:**
1. WLOG `0 < f n` (by negating `f` if needed; `convolutionPoly` invariant).
2. Show `ordinaryGen n (k ↦ f(n-k))` (the reversal `F_rev`) has
   only real negative zeros via the identity `F_rev(z) = z^n F(1/z)`.
3. Show `(1+X)^n` has only real negative zeros (root at -1 with mult n).
4. Apply `hadamard_closure_for_negative_rooted` axiom to `F`, `F_rev` →
   intermediate has only real non-positive zeros.
5. Apply axiom again to (intermediate, `(1+X)^n`) → has only real
   non-positive zeros.
6. Identify with `convolutionPoly n f` via coefficient calculation.
7. Compute `convolutionPoly(0) = f(0)·f(n) > 0` to exclude 0.

**Estimated effort:** ~200 lines. Author attempted this; reverted due
to small Lean tactic errors in the reversal identity proof and the
WLOG case split. Specific issues encountered: wrong lemma names
(`inv_neg_of_neg`), `linear_combination` mismatches over ℂ, `where`-clause
nesting awkwardness for the helper that assumes `0 < f n`.

### §6.2 `newton_inequality_n4_e2sq_gt_e4` (Determinant.lean:371)

```
∀ (f : ℕ → ℝ),
  HasDegree (ordinaryGen 4 f) 4 →
  HasOnlyRealNegativeZeros (ordinaryGen 4 f) →
  f 2 ^ 2 > f 0 * f 4
```

**Classical content:** Newton inequality `e_2² > e_4` for 4 positive
reals (special case of Newton–Maclaurin).

**Difficulty:** ★★★☆☆.

**Proof plan:**
1. Extract 4 positive root magnitudes `α_1, …, α_4` via Vieta/splits.
2. Express `f(k) = f(4)·e_{4-k}(α)` (elementary symmetric).
3. Prove `e_2(α)² ≥ 6·e_4(α) > e_4(α)` for positive multiset of size 4
   by direct expansion: `e_2²` contains the term `r_i r_j · r_k r_l`
   for disjoint pairs `{i,j}, {k,l}` — there are 3 such pairs, each
   counted twice in the square, giving `6 e_4` plus nonneg cross terms.

**Estimated effort:** ~150 lines. Subsumed by §6.4 (n=4 special case).

### §6.3 `newton_inequality_n4_e1e3_gt_e4` (Determinant.lean:380)

```
∀ (f : ℕ → ℝ),
  HasDegree (ordinaryGen 4 f) 4 →
  HasOnlyRealNegativeZeros (ordinaryGen 4 f) →
  f 1 * f 3 > f 0 * f 4
```

This is exactly the `n = 4` case of §6.4. Once §6.4 is closed, this
is one-line: `cauchy_schwarz_f1_fn1_gt_f0_fn 4 f (by norm_num) hdeg hroot`.

**Difficulty:** ★☆☆☆☆ once §6.4 is done. (Currently ★★★☆☆ standalone.)

### §6.4 `cauchy_schwarz_f1_fn1_gt_f0_fn` (Determinant.lean:637)

```
∀ (n : ℕ) (f : ℕ → ℝ), 2 ≤ n →
  HasDegree (ordinaryGen n f) n →
  HasOnlyRealNegativeZeros (ordinaryGen n f) →
  f 1 * f (n - 1) > f 0 * f n
```

**Classical content:** Cauchy–Schwarz / AM–HM for positive root magnitudes:
`(Σ αᵢ)(Σ 1/αᵢ) ≥ n²`, which translates via Vieta to `e_1·e_{n-1} ≥ n²·e_n`.

**Difficulty:** ★★★★☆ — the hardest of the 4 sorrys.

**Proof plan:**
1. Use `Polynomial.coeff_eq_esymm_roots_of_splits` (Mathlib has this).
2. Show `(ordinaryGen n f).Splits (RingHom.id ℝ)` from
   `HasOnlyRealNegativeZeros` + `HasDegree`.
3. Get multiset `M` of roots; each `r ∈ M` is `< 0`.
4. Express `f(k) = f(n)·(-1)^(n-k)·M.esymm (n-k)`.
5. Set `α = M.map Neg.neg` (positive multiset of size n).
6. Reduce to `α.esymm 1 · α.esymm (n-1) > α.esymm n`.
7. Algebraic core: `α.esymm 1 · α.esymm (n-1) ≥ n·α.esymm n` by
   expanding and identifying `n` copies of `α.esymm n` plus nonneg cross
   terms (the paper's argument).

**Estimated effort:** ~250 lines. Requires Mathlib's
`Multiset.esymm` and `Polynomial.Splits`/`Polynomial.roots`
infrastructure, plus careful manipulation.

---

## 8. Difficulty summary table

| Axiom / Sorry | Classical name | Difficulty | Discharge route |
|---|---|---|---|
| `hadamard_closure_for_negative_rooted` | Schur–Hadamard 1914 | ★★★★★ | Pólya-frequency theory (months) |
| `schur_preserves_nonpos` | Schur–Maló | ★★★★★ | HKO theorem + interlacing (months) |
| `gamma_representation` | γ-positivity (Lemma 3) | ★★★☆☆ | Paper's reciprocal-pair argument (~300 ln) |
| `determinant_main_preserves_strict` | Theorem 1 | ★★★☆☆ | **Already partially formalized** — close 4 sorrys (§7) |
| `centered_classification_axiom` | Theorem 2 | ★★★☆☆ | Concrete γ-polynomial check (~200 ln) |
| Sorry §6.1 (convolutionPoly_…) | — | ★★★☆☆ | Lean engineering (~200 ln) |
| Sorry §6.2 (newton_e2sq_gt_e4) | Newton ineq | ★★★☆☆ | Vieta + AM-GM (~150 ln) |
| Sorry §6.3 (newton_e1e3_gt_e4) | n=4 cauchy_schwarz | ★☆☆☆☆ | Once §6.4 done |
| Sorry §6.4 (cauchy_schwarz_…) | AM-HM on roots | ★★★★☆ | Splits + Multiset.esymm (~250 ln) |

---

## 9. Path of least resistance to most axiom reduction

Ordered by impact ÷ effort:

1. **Close all 4 sorrys in `Determinant.lean`** (§6.1–§6.4):
   - Eliminates axiom ④ `determinant_main_preserves_strict`.
   - **5 axioms → 4 axioms** for the whole project.
   - Total ~650 lines. All mechanical, no missing classical mathematics.
   - High-value first target.

2. **Formalize `gamma_representation` (axiom ③)** from the paper's
   Lemma 3:
   - Eliminates axiom ③.
   - **4 → 3 axioms.**
   - Frees `single_product_kernel`, `pochhammer_kernel_ladder*`,
     `original_kernel_palindromic`, plus the result from step 1.
   - ~300 lines, self-contained reciprocal-pair argument.

3. **Formalize `centered_classification_axiom` (axiom ⑤)**:
   - Eliminates axiom ⑤.
   - **3 → 2 axioms.**
   - Cosmetic (no downstream consumers beyond `centered_balanced_classification`).
   - ~200 lines.

4. **Formalize `schur_preserves_nonpos` and
   `hadamard_closure_for_negative_rooted` (axioms ① and ②)**:
   - Both require building large Mathlib infrastructure
     (Pólya–Schur, HKO theorem, multiplier sequences).
   - **Multi-month project** for each.
   - Best deferred to when (or if) Mathlib gets the relevant theory.

---

## 10. Build verification

```
$ lake build
✔ [8251/8252] Built GammaPochhammer (4.7s)
Build completed successfully (8252 jobs).
```

```
$ #print axioms main_theorem
[propext, Classical.choice, determinant_main_preserves_strict, Quot.sound]
```

```
$ #print axioms determinant_main_preserves_strict_proved
[propext, sorryAx, Classical.choice,
 gamma_representation, schur_preserves_nonpos, Quot.sound]
```

The second print confirms the discharge route: once the 4 sorrys close,
`determinant_main_preserves_strict_proved` becomes axiom-free modulo
`[hadamard_closure_for_negative_rooted, gamma_representation,
schur_preserves_nonpos]`, and `main_theorem` can be rewired to use it
instead of axiom ④.
