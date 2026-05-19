import GammaPochhammer.Basic

/-!
# Schur–Maló preservation theorem — partial formalization

This module attempts to discharge the axiom
`GammaPochhammer.schur_preserves_nonpos` in `Basic.lean`, which asserts that
the Schur-type linear transform
  `schurTransform ell α B = ∑_{r=0..ell} B.coeff r · (X)_r · (X+r+α)_{ell-r}`
preserves the property of having only real non-positive zeros, for `α > 0`.

This is essentially the **Schur–Maló theorem**, a Pólya–Schur preservation
result for finite linear operators on polynomials of bounded degree. The
proof in the literature uses either the Borcea–Brändén characterization
(stable polynomial symbols), Hermite–Kakeya–Obreschkoff interlacing, or
Laguerre–Pólya multiplier-sequence theory — none of which currently exist
in Mathlib (v4.29.1).

## What this file contains (proven from scratch)

* `coeff_nonneg_of_hasOnlyRealNonposZeros` — if `p ∈ ℝ[X]` has only real
  non-positive zeros and `0 ≤ leadingCoeff p`, then every coefficient is
  non-negative. Proof: induction on `natDegree p`, factoring out a real
  non-positive root at each step. **Useful in isolation** for other parts
  of the development; depends only on standard Mathlib polynomial
  machinery and `Complex.exists_root`.

* `coeff_mul_coeff_nonneg` — the corollary that any two coefficients of
  such a polynomial have non-negative product (i.e. share a sign).

* `schur_preserves_nonpos_zero` — the `ell = 0` case (transform is a
  constant, trivially non-pos-rooted).

* `schur_preserves_nonpos_one` — the `ell = 1` case (transform is linear
  in `X`; the unique root is `-α b_0 / (b_0 + b_1)`, whose non-positivity
  follows from `coeff_mul_coeff_nonneg` applied to `b_0` and `b_1`).

## What remains (not in this file)

For `ell ≥ 2`, the full theorem requires substantial new Mathlib
infrastructure. Sketch of one viable path:

1. **Interlacing lemma**: for `α > 0` and `D` with only real non-pos
   zeros, the polynomials `schurTransform ell α D` (degree `ell`) and
   `schurTransform (ell-1) (α+1) D` (degree `ell-1`) weakly interlace —
   their real roots alternate on the negative axis (with possible
   equalities).

2. **Hermite–Kakeya–Obreschkoff (HKO) theorem**: if `p` (degree `n+1`)
   and `q` (degree `n`) have weakly interlacing real roots, then every
   real linear combination `a·p + b·q` has only real roots.

3. **Sign-tracking lemma**: under (1) and (2), the specific linear
   combination `(1+s)·T_ell^α(D) - α·T_{ell-1}^{α+1}(D)` (which equals
   `T_ell^α((X+C s)·D)` for `s ≥ 0`) has only real **non-positive** roots.

4. **Outer induction on `natDegree B`**: factor `B = (X+C s)·D` and apply
   the IH plus the combined (1)+(2)+(3).

Each of (1)–(3) is itself a non-trivial classical theorem. (2) is the
Hermite–Kakeya–Obreschkoff theorem; it does not currently exist in
Mathlib in any form, and a clean formalization is its own project.

## Recursion identities (provable but not used here)

The following structural identities hold and are individually
formalizable:

* `ψ_{r+1}^{(ell)}(z) = z · ψ_r^{(ell-1)}(z+1)` (ladder identity).
* `T_ell^α((X+C s)·D) = (1+s)·T_ell^α(D) - α·T_{ell-1}^{α+1}(D)` (the
  recursion that drives the induction sketched above).
* `T_{ell+1}^α(B) = (X + C(ell+α))·T_ell^α(B) + B.coeff(ell+1)·(X)_{ell+1}`
  (recursion in `ell`).

These are not formalized below because, without the HKO theorem, they
cannot be used to discharge the main axiom.
-/

noncomputable section

open BigOperators Polynomial

namespace GammaPochhammer

/-! ## Basic root-predicate lemmas -/

theorem hasOnlyRealNonposZeros_C (c : ℝ) :
    HasOnlyRealNonposZeros (C c) := by
  by_cases hc : c = 0
  · left
    simp [hc]
  · right
    intro z hz
    have : (toComplex (C c)).eval z = (c : ℂ) := by
      simp [toComplex]
    rw [this] at hz
    exact absurd (by exact_mod_cast hz) hc

theorem toComplex_eval_real (p : ℝ[X]) (r : ℝ) :
    (toComplex p).eval (r : ℂ) = ((p.eval r : ℝ) : ℂ) := by
  have hcast : ((r : ℝ) : ℂ) = (algebraMap ℝ ℂ) r := rfl
  rw [hcast]
  unfold toComplex
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  rfl

theorem isRoot_toComplex_iff_real (p : ℝ[X]) (r : ℝ) :
    (toComplex p).eval (r : ℂ) = 0 ↔ p.eval r = 0 := by
  rw [toComplex_eval_real]
  exact_mod_cast Iff.rfl

theorem toComplex_eq_zero_iff (p : ℝ[X]) : toComplex p = 0 ↔ p = 0 := by
  unfold toComplex
  exact Polynomial.map_eq_zero_iff
    (RingHom.injective (algebraMap ℝ ℂ))

theorem natDegree_toComplex (p : ℝ[X]) :
    (toComplex p).natDegree = p.natDegree := by
  unfold toComplex
  exact Polynomial.natDegree_map_eq_of_injective
    (RingHom.injective (algebraMap ℝ ℂ)) p

/-! ## Existence of a real non-positive root -/

theorem exists_real_nonpos_root (p : ℝ[X]) (h : HasOnlyRealNonposZeros p)
    (hdeg : 1 ≤ p.natDegree) :
    ∃ r : ℝ, r ≤ 0 ∧ p.eval r = 0 := by
  have hp_ne : p ≠ 0 := by
    intro hp0
    rw [hp0] at hdeg
    simp at hdeg
  have hpc_ne : toComplex p ≠ 0 :=
    fun h => hp_ne ((toComplex_eq_zero_iff p).mp h)
  have hpc_natDeg : 1 ≤ (toComplex p).natDegree := by
    rw [natDegree_toComplex]; exact hdeg
  have hpc_deg : 0 < (toComplex p).degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp (by omega)
  obtain ⟨z, hz⟩ := Complex.exists_root hpc_deg
  rcases h with h0 | hreal
  · exact absurd h0 hp_ne
  obtain ⟨r, hr_le, hr_eq⟩ := hreal z hz
  refine ⟨r, hr_le, ?_⟩
  rw [hr_eq] at hz
  exact (isRoot_toComplex_iff_real p r).mp hz

/-! ## Factoring out a root -/

theorem exists_quotient_of_root {p : ℝ[X]} {r : ℝ} (hr : p.eval r = 0) :
    ∃ q : ℝ[X], p = (X - C r) * q := by
  rcases (dvd_iff_isRoot (p := p) (a := r)).mpr hr with ⟨q, hq⟩
  exact ⟨q, hq⟩

theorem natDegree_quotient_of_root {p q : ℝ[X]} {r : ℝ} (hp : p ≠ 0)
    (hpq : p = (X - C r) * q) :
    q.natDegree + 1 = p.natDegree := by
  have hqne : q ≠ 0 := by
    intro hq0
    rw [hq0, mul_zero] at hpq
    exact hp hpq
  have hXminne : (X - C r : ℝ[X]) ≠ 0 := X_sub_C_ne_zero r
  rw [hpq, natDegree_mul hXminne hqne, natDegree_X_sub_C, add_comm]

theorem hasOnlyRealNonposZeros_quotient {p q : ℝ[X]} {r : ℝ}
    (hp : HasOnlyRealNonposZeros p) (hpq : p = (X - C r) * q) :
    HasOnlyRealNonposZeros q := by
  by_cases hq0 : q = 0
  · left; exact hq0
  rcases hp with hp0 | hp
  · rw [hp0] at hpq
    have hXne : (X - C r : ℝ[X]) ≠ 0 := X_sub_C_ne_zero r
    have hq_eq : q = 0 := by
      rcases mul_eq_zero.mp hpq.symm with h | h
      · exact absurd h hXne
      · exact h
    exact absurd hq_eq hq0
  right
  intro z hz
  have hpz : (toComplex p).eval z = 0 := by
    rw [hpq]
    have hmul : toComplex ((X - C r) * q) = toComplex (X - C r) * toComplex q := by
      simp [toComplex, Polynomial.map_mul]
    rw [hmul, eval_mul, hz, mul_zero]
  exact hp z hpz

/-! ## Leading-coefficient preservation -/

theorem leadingCoeff_quotient_of_root {p q : ℝ[X]} {r : ℝ}
    (hp_ne : p ≠ 0) (hpq : p = (X - C r) * q) :
    q.leadingCoeff = p.leadingCoeff := by
  have hqne : q ≠ 0 := by
    intro hq0
    rw [hq0, mul_zero] at hpq
    exact hp_ne hpq
  have heq : p.leadingCoeff = (X - C r).leadingCoeff * q.leadingCoeff := by
    rw [hpq, Polynomial.leadingCoeff_mul]
  rw [Polynomial.leadingCoeff_X_sub_C] at heq
  linarith

/-! ## Coefficient sign lemma -/

/-- A polynomial with only real non-positive zeros and non-negative leading
coefficient has all coefficients non-negative. -/
theorem coeff_nonneg_of_hasOnlyRealNonposZeros
    (p : ℝ[X]) (hp : HasOnlyRealNonposZeros p)
    (hlc : 0 ≤ p.leadingCoeff) :
    ∀ k, 0 ≤ p.coeff k := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    by_cases hn0 : n = 0
    · -- Constant case.
      subst hn0
      have hpC : p = C (p.coeff 0) := by
        apply Polynomial.eq_C_of_natDegree_eq_zero hn
      intro k
      by_cases hk : k = 0
      · subst hk
        have : p.leadingCoeff = p.coeff 0 := by
          rw [Polynomial.leadingCoeff, hn]
        linarith
      · rw [hpC]
        simp [Polynomial.coeff_C, hk]
    -- natDegree p = n ≥ 1: factor out a real non-pos root.
    have hdeg : 1 ≤ p.natDegree := by omega
    obtain ⟨r, hr_le, hr_root⟩ := exists_real_nonpos_root p hp hdeg
    obtain ⟨q, hpq⟩ := exists_quotient_of_root hr_root
    have hp_ne : p ≠ 0 := by
      intro hp0
      rw [hp0] at hdeg
      simp at hdeg
    have hqdeg : q.natDegree + 1 = p.natDegree :=
      natDegree_quotient_of_root hp_ne hpq
    have hq_lt : q.natDegree < n := by omega
    have hq_nonpos : HasOnlyRealNonposZeros q :=
      hasOnlyRealNonposZeros_quotient hp hpq
    have hq_lc : q.leadingCoeff = p.leadingCoeff :=
      leadingCoeff_quotient_of_root hp_ne hpq
    have hq_lc_nonneg : 0 ≤ q.leadingCoeff := by rw [hq_lc]; exact hlc
    have ih_q : ∀ j, 0 ≤ q.coeff j :=
      ih q.natDegree hq_lt q hq_nonpos hq_lc_nonneg rfl
    intro k
    -- p.coeff k expansion: (X - C r) * q expanded
    have hexpand : p = X * q - C r * q := by
      rw [hpq]; ring
    have hr_nonneg : 0 ≤ -r := by linarith
    rcases k with _ | k
    · -- k = 0: p.coeff 0 = -r * q.coeff 0.
      have h1 : (X * q).coeff 0 = 0 := by
        simp
      have h2 : (C r * q).coeff 0 = r * q.coeff 0 := by
        rw [Polynomial.coeff_C_mul]
      have hp_c0 : p.coeff 0 = - (r * q.coeff 0) := by
        rw [hexpand, Polynomial.coeff_sub, h1, h2]; ring
      rw [hp_c0]
      have := mul_nonneg hr_nonneg (ih_q 0)
      linarith
    · -- k = k+1: p.coeff (k+1) = q.coeff k - r * q.coeff (k+1).
      have h1 : (X * q).coeff (k + 1) = q.coeff k :=
        Polynomial.coeff_X_mul q k
      have h2 : (C r * q).coeff (k + 1) = r * q.coeff (k + 1) := by
        rw [Polynomial.coeff_C_mul]
      have hp_csucc : p.coeff (k + 1) = q.coeff k - r * q.coeff (k + 1) := by
        rw [hexpand, Polynomial.coeff_sub, h1, h2]
      rw [hp_csucc]
      have h3 : 0 ≤ q.coeff k := ih_q k
      have h4 : 0 ≤ -r * q.coeff (k + 1) :=
        mul_nonneg hr_nonneg (ih_q _)
      linarith

/-- Negating a polynomial preserves `HasOnlyRealNonposZeros`. -/
theorem hasOnlyRealNonposZeros_neg {p : ℝ[X]} (hp : HasOnlyRealNonposZeros p) :
    HasOnlyRealNonposZeros (-p) := by
  rcases hp with h0 | hp
  · left; rw [h0]; ring
  right
  intro z hz
  apply hp
  have hneg : (toComplex (-p)).eval z = -(toComplex p).eval z := by
    simp [toComplex, Polynomial.map_neg]
  rw [hneg, neg_eq_zero] at hz
  exact hz

/-- Any two coefficients of a polynomial with only real non-positive zeros have
non-negative product. -/
theorem coeff_mul_coeff_nonneg
    (p : ℝ[X]) (hp : HasOnlyRealNonposZeros p) (i j : ℕ) :
    0 ≤ p.coeff i * p.coeff j := by
  by_cases hlc : 0 ≤ p.leadingCoeff
  · have hall := coeff_nonneg_of_hasOnlyRealNonposZeros p hp hlc
    exact mul_nonneg (hall i) (hall j)
  · have hlc : p.leadingCoeff < 0 := not_le.mp hlc
    have hp_neg : HasOnlyRealNonposZeros (-p) := hasOnlyRealNonposZeros_neg hp
    have hlc_neg : 0 ≤ (-p).leadingCoeff := by
      rw [Polynomial.leadingCoeff_neg]
      linarith
    have hall := coeff_nonneg_of_hasOnlyRealNonposZeros (-p) hp_neg hlc_neg
    have hi : 0 ≤ (-p).coeff i := hall i
    have hj : 0 ≤ (-p).coeff j := hall j
    rw [Polynomial.coeff_neg] at hi hj
    nlinarith

/-! ## Small cases of the Schur–Maló preservation theorem -/

/-- For `ell = 0`, `schurTransform` is the constant polynomial `C (B.coeff 0)`. -/
theorem schurTransform_zero (α : ℝ) (B : ℝ[X]) :
    schurTransform 0 α B = C (B.coeff 0) := by
  simp [schurTransform, pochhammer]

/-- The Schur–Maló theorem for `ell = 0`: trivial. -/
theorem schur_preserves_nonpos_zero (α : ℝ) (_hα : 0 < α) (B : ℝ[X])
    (_hB : HasOnlyRealNonposZeros B) :
    HasOnlyRealNonposZeros (schurTransform 0 α B) := by
  rw [schurTransform_zero]
  exact hasOnlyRealNonposZeros_C _

/-- For `ell = 1`, `schurTransform` is the linear polynomial
`(B.coeff 0 + B.coeff 1) X + α B.coeff 0`. -/
theorem schurTransform_one (α : ℝ) (B : ℝ[X]) :
    schurTransform 1 α B =
      C (B.coeff 0 + B.coeff 1) * X + C (α * B.coeff 0) := by
  simp [schurTransform, pochhammer, Finset.sum_range_succ]
  ring

/-- The Schur–Maló theorem for `ell = 1`. -/
theorem schur_preserves_nonpos_one (α : ℝ) (hα : 0 < α) (B : ℝ[X])
    (hB : HasOnlyRealNonposZeros B) :
    HasOnlyRealNonposZeros (schurTransform 1 α B) := by
  rw [schurTransform_one]
  set b0 := B.coeff 0
  set b1 := B.coeff 1
  set s : ℝ := b0 + b1 with hs_def
  set t : ℝ := α * b0 with ht_def
  -- The polynomial we work with: P(X) = C s * X + C t.
  set P : ℝ[X] := C s * X + C t with hP_def
  -- Useful: b0 b1 ≥ 0 from coefficient sign lemma.
  have hbb : 0 ≤ b0 * b1 := coeff_mul_coeff_nonneg B hB 0 1
  have hb0_sq : 0 ≤ b0 * b0 := mul_self_nonneg b0
  have hb0_times_s : 0 ≤ b0 * s := by
    show 0 ≤ b0 * (b0 + b1)
    nlinarith
  -- The evaluation formula for toComplex P.
  have hPeval : ∀ z : ℂ, (toComplex P).eval z =
      (s : ℂ) * z + (t : ℂ) := by
    intro z
    simp [hP_def, toComplex, Polynomial.map_add, Polynomial.map_mul,
          Polynomial.map_C, Polynomial.map_X]
  -- P = 0 case.
  by_cases hP0 : P = 0
  · left; exact hP0
  right
  intro z hz
  rw [hPeval] at hz
  -- hz : (s : ℂ) * z + (t : ℂ) = 0
  by_cases hs0 : s = 0
  · -- s = 0 forces t = 0 via hz.
    have hsC : (s : ℂ) = 0 := by exact_mod_cast hs0
    rw [hsC, zero_mul, zero_add] at hz
    have ht0 : t = 0 := by exact_mod_cast hz
    -- t = α b0 = 0 and α > 0 forces b0 = 0, then b1 = 0, so P = 0, contradiction.
    have hα_ne : α ≠ 0 := ne_of_gt hα
    have hb0_eq : b0 = 0 := by
      rcases mul_eq_zero.mp ht0 with h | h
      · exact absurd h hα_ne
      · exact h
    have hb1_eq : b1 = 0 := by
      have : s = b0 + b1 := rfl
      rw [hb0_eq] at this
      linarith [hs0, this]
    have hP_zero : P = 0 := by
      show C s * X + C t = 0
      rw [hs0, ht0]
      simp
    exact absurd hP_zero hP0
  · -- s ≠ 0: solve z = -t/s.
    have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
    -- From hz: (s : ℂ) * z = -(t : ℂ).
    have hz_mul : (s : ℂ) * z = -(t : ℂ) := by linear_combination hz
    have hz_eq : z = -(t : ℂ) / (s : ℂ) := by
      rw [eq_div_iff hsC, mul_comm]
      exact hz_mul
    -- Define the real candidate root.
    set r : ℝ := -t / s with hr_def
    refine ⟨r, ?_, ?_⟩
    · -- r ≤ 0.
      -- r = -t/s = -α b0/(b0+b1). Sign analysis using 0 ≤ b0 (b0+b1) = b0 * s.
      rcases lt_or_gt_of_ne hs0 with hs_neg | hs_pos
      · -- s < 0.
        have hb0_le : b0 ≤ 0 := by
          by_contra h
          have hpos : 0 < b0 := not_le.mp h
          have : b0 * s < 0 := mul_neg_of_pos_of_neg hpos hs_neg
          linarith
        have ht_le : t ≤ 0 := by
          rw [ht_def]
          exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hα) hb0_le
        have h_neg_t_nonneg : 0 ≤ -t := by linarith
        rw [hr_def]
        exact div_nonpos_of_nonneg_of_nonpos h_neg_t_nonneg (le_of_lt hs_neg)
      · -- s > 0.
        have hb0_nonneg : 0 ≤ b0 := by
          by_contra h
          have hneg : b0 < 0 := not_le.mp h
          have : b0 * s < 0 := mul_neg_of_neg_of_pos hneg hs_pos
          linarith
        have ht_nonneg : 0 ≤ t := by
          rw [ht_def]
          exact mul_nonneg (le_of_lt hα) hb0_nonneg
        have h_neg_t_nonpos : -t ≤ 0 := by linarith
        rw [hr_def]
        exact div_nonpos_of_nonpos_of_nonneg h_neg_t_nonpos (le_of_lt hs_pos)
    · -- z = (r : ℂ).
      rw [hz_eq, hr_def]
      push_cast
      ring

end GammaPochhammer
