import GammaPochhammer.GammaRep

/-!
# Proof of `centered_classification_axiom` (Theorem 3 of the paper)

This module proves the statement currently axiomatized as
`GammaPochhammer.centered_classification_axiom` in `Basic.lean`.  The proof
follows the paper's argument for **Theorem 3** in §3:

* **Sufficiency.** If `{a², c²} = {0, 1}`, then either `(a, c)` is `(0, ±1)` or
  `(±1, 0)`.  In each case the centered operator on a palindromic input
  coincides up to a sign with the determinant kernel `(z)_k(z)_{n-k} -
  (z+1)_k(z-1)_{n-k}`, which is the `s=1`, `μ=0` rung kernel; admissibility
  follows from `original_kernel_palindromic`.

* **Necessity.** Assume `UniversallyAdmissibleCentered a c` and `a² ≠ c²`.
  WLOG `0 ≤ a² < c²`; write `u = a²`, `v = c²`, `δ = v - u > 0`,
  `σ = u + v`.  By testing on `Q_λ = (λ(1+X)² + X)²` (the
  `γ-polynomial Γ(t) = (t + λ)²`-image) for two explicit `λ > 0` values, we
  force `σ = 1`.  Then by testing on `Q_ε = (ε(1+X)² + X)³` for a small
  `ε > 0` (chosen depending on `u`) and applying IVT between `z = 0`
  (negative value) and `z = 1` (positive value), we force `u = 0`.
-/

noncomputable section

open BigOperators Polynomial

namespace GammaPochhammer

/-! ## A specialization of Vandermonde for the centered kernel

The centered kernel involves two products of ascending Pochhammer symbols
shifted by `±a`.  Acting on `gammaBasis n j`, Vandermonde collapses the
inner `k`-sum to a clean factored form (using `ascPochhammer_vandermonde`
exported from `Basic.lean`).
-/

/-- Pointwise evaluation of a centered single-product sum on `gammaBasis n j`. -/
private lemma centered_single_eval (n j : ℕ) (h2j : 2 * j ≤ n) (α z : ℝ) :
    (∑ k ∈ Finset.range (n + 1),
        (gammaBasis n j).coeff k *
          ((ascPochhammer ℝ k).eval (z + α) *
            (ascPochhammer ℝ (n - k)).eval (z - α))) =
      (ascPochhammer ℝ j).eval (z + α) *
        (ascPochhammer ℝ j).eval (z - α) *
        (ascPochhammer ℝ (n - 2 * j)).eval (2 * z + 2 * j) := by
  -- Plug coeff_gammaBasis.
  have h_coeff : ∀ k ∈ Finset.range (n + 1),
      (gammaBasis n j).coeff k *
          ((ascPochhammer ℝ k).eval (z + α) *
            (ascPochhammer ℝ (n - k)).eval (z - α)) =
        (if j ≤ k then ((n - 2 * j).choose (k - j) : ℝ) else 0) *
          ((ascPochhammer ℝ k).eval (z + α) *
            (ascPochhammer ℝ (n - k)).eval (z - α)) := by
    intros k _; rw [coeff_gammaBasis]
  rw [Finset.sum_congr rfl h_coeff]
  have h_if : ∀ k ∈ Finset.range (n + 1),
      (if j ≤ k then ((n - 2 * j).choose (k - j) : ℝ) else 0) *
          ((ascPochhammer ℝ k).eval (z + α) *
            (ascPochhammer ℝ (n - k)).eval (z - α)) =
        if j ≤ k then
          ((n - 2 * j).choose (k - j) : ℝ) *
            ((ascPochhammer ℝ k).eval (z + α) *
              (ascPochhammer ℝ (n - k)).eval (z - α))
        else 0 := by
    intros _ _; split_ifs <;> ring
  rw [Finset.sum_congr rfl h_if]
  rw [← Finset.sum_filter]
  rw [show Finset.filter (fun k => j ≤ k) (Finset.range (n + 1)) =
          Finset.Ico j (n + 1) from by
      ext k; simp [Finset.mem_range, Finset.mem_Ico, Finset.mem_filter]; omega]
  rw [Finset.sum_Ico_eq_sum_range]
  have hℓ : ∀ ℓ ∈ Finset.range (n + 1 - j),
      ((n - 2 * j).choose (j + ℓ - j) : ℝ) *
        ((ascPochhammer ℝ (j + ℓ)).eval (z + α) *
          (ascPochhammer ℝ (n - (j + ℓ))).eval (z - α)) =
      ((n - 2 * j).choose ℓ : ℝ) *
        ((ascPochhammer ℝ (j + ℓ)).eval (z + α) *
          (ascPochhammer ℝ (n - (j + ℓ))).eval (z - α)) := by
    intros ℓ _; rw [show j + ℓ - j = ℓ from by omega]
  rw [Finset.sum_congr rfl hℓ]
  -- Truncate to ℓ ∈ range (n - 2j + 1).
  rw [show ∑ ℓ ∈ Finset.range (n + 1 - j),
          ((n - 2 * j).choose ℓ : ℝ) *
            ((ascPochhammer ℝ (j + ℓ)).eval (z + α) *
              (ascPochhammer ℝ (n - (j + ℓ))).eval (z - α)) =
        ∑ ℓ ∈ Finset.range (n - 2 * j + 1),
          ((n - 2 * j).choose ℓ : ℝ) *
            ((ascPochhammer ℝ (j + ℓ)).eval (z + α) *
              (ascPochhammer ℝ (n - (j + ℓ))).eval (z - α)) from by
    rw [show Finset.range (n + 1 - j) =
            Finset.range (n - 2 * j + 1) ∪
              Finset.Ico (n - 2 * j + 1) (n + 1 - j) from by
          ext x
          simp [Finset.mem_range, Finset.mem_Ico, Finset.mem_union]
          omega]
    rw [Finset.sum_union (by
      rw [Finset.disjoint_left]
      intros x hx hx'
      rw [Finset.mem_range] at hx
      rw [Finset.mem_Ico] at hx'
      omega)]
    rw [show ∑ ℓ ∈ Finset.Ico (n - 2 * j + 1) (n + 1 - j),
            ((n - 2 * j).choose ℓ : ℝ) *
              ((ascPochhammer ℝ (j + ℓ)).eval (z + α) *
                (ascPochhammer ℝ (n - (j + ℓ))).eval (z - α)) = 0 from by
      apply Finset.sum_eq_zero
      intros ℓ hℓ
      rw [Finset.mem_Ico] at hℓ
      have hC0 : (n - 2 * j).choose ℓ = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [show ((n - 2 * j).choose ℓ : ℝ) = 0 from by exact_mod_cast hC0]
      ring]
    rw [add_zero]]
  -- Split each ascPochhammer using ascPochhammer_mul.
  have hsplit : ∀ ℓ ∈ Finset.range (n - 2 * j + 1),
      ((n - 2 * j).choose ℓ : ℝ) *
        ((ascPochhammer ℝ (j + ℓ)).eval (z + α) *
          (ascPochhammer ℝ (n - (j + ℓ))).eval (z - α)) =
      (ascPochhammer ℝ j).eval (z + α) *
          (ascPochhammer ℝ j).eval (z - α) *
          (((n - 2 * j).choose ℓ : ℝ) *
            ((ascPochhammer ℝ ℓ).eval (z + α + j) *
              (ascPochhammer ℝ (n - 2 * j - ℓ)).eval (z - α + j))) := by
    intros ℓ hℓ
    rw [Finset.mem_range] at hℓ
    have hℓle : ℓ ≤ n - 2 * j := Nat.lt_succ_iff.mp hℓ
    have h1 : (ascPochhammer ℝ (j + ℓ)).eval (z + α) =
        (ascPochhammer ℝ j).eval (z + α) *
          (ascPochhammer ℝ ℓ).eval (z + α + ↑j) := by
      have hmul := ascPochhammer_mul (S := ℝ) j ℓ
      have := congrArg (fun p => (p : ℝ[X]).eval (z + α)) hmul.symm
      simp only [eval_mul, eval_comp, eval_add, eval_X, eval_natCast] at this
      exact this
    have h2 : (ascPochhammer ℝ (n - (j + ℓ))).eval (z - α) =
        (ascPochhammer ℝ j).eval (z - α) *
          (ascPochhammer ℝ (n - 2 * j - ℓ)).eval (z - α + ↑j) := by
      have hcomp : n - (j + ℓ) = j + (n - 2 * j - ℓ) := by omega
      rw [hcomp]
      have hmul := ascPochhammer_mul (S := ℝ) j (n - 2 * j - ℓ)
      have := congrArg (fun p => (p : ℝ[X]).eval (z - α)) hmul.symm
      simp only [eval_mul, eval_comp, eval_add, eval_X, eval_natCast] at this
      exact this
    rw [h1, h2]
    ring
  rw [Finset.sum_congr rfl hsplit]
  rw [← Finset.mul_sum]
  -- Apply Vandermonde.
  have hvm : ∑ ℓ ∈ Finset.range (n - 2 * j + 1),
      ((n - 2 * j).choose ℓ : ℝ) *
        ((ascPochhammer ℝ ℓ).eval (z + α + ↑j) *
          (ascPochhammer ℝ (n - 2 * j - ℓ)).eval (z - α + ↑j)) =
      (ascPochhammer ℝ (n - 2 * j)).eval (2 * z + 2 * j) := by
    -- Reuse the existing vandermonde lemma (it lives in Basic; replicate here).
    have hvand := ascPochhammer_vandermonde (z + α + (j : ℝ)) (z - α + (j : ℝ)) (n - 2 * j)
    rw [show (z + α + (j : ℝ)) + (z - α + (j : ℝ)) = 2 * z + 2 * (j : ℝ) from by ring]
      at hvand
    rw [show (2 * z + 2 * (j : ℝ)) = 2 * z + 2 * (j : ℕ) from by norm_cast] at hvand
    exact hvand
  rw [hvm]

/-! ## Action of the centered operator on a single γ-basis vector

We package the centered single-sum lemma into a polynomial identity, then
take the difference of two such evaluations (`α = a` and `α = c`) to obtain
the centered-operator action.
-/

/-- The polynomial `(z+α)_j · (z-α)_j` (a degree-`2j` polynomial in `z`). -/
private def centeredFactor (α : ℝ) (j : ℕ) : ℝ[X] :=
  pochhammer α j * pochhammer (-α) j

private lemma centeredFactor_eval (α z : ℝ) (j : ℕ) :
    (centeredFactor α j).eval z =
      (ascPochhammer ℝ j).eval (z + α) * (ascPochhammer ℝ j).eval (z - α) := by
  unfold centeredFactor
  rw [eval_mul, pochhammer_eval, pochhammer_eval]
  ring_nf

/-- The centered operator acting on `gammaBasis n j`: it factors as the
*centered difference* `(centeredFactor a j - centeredFactor c j)` times the
linear Pochhammer block `(2z + 2j)_{n-2j}`. -/
private theorem centered_action_on_gammaBasis
    (n j : ℕ) (h2j : 2 * j ≤ n) (a c : ℝ) :
    centeredOperator n a c (gammaBasis n j) =
      (centeredFactor a j - centeredFactor c j) *
        linearPochhammer 2 (2 * j) (n - 2 * j) := by
  apply Polynomial.funext
  intro z
  -- Evaluate the centered operator at `z`.
  rw [centeredOperator]
  rw [eval_finset_sum]
  have h_each : ∀ k ∈ Finset.range (n + 1),
      (C (Polynomial.coeff (gammaBasis n j) k) * centeredKernel n k a c).eval z =
        (gammaBasis n j).coeff k *
          ((ascPochhammer ℝ k).eval (z + a) *
            (ascPochhammer ℝ (n - k)).eval (z - a)) -
        (gammaBasis n j).coeff k *
          ((ascPochhammer ℝ k).eval (z + c) *
            (ascPochhammer ℝ (n - k)).eval (z - c)) := by
    intros k _
    rw [centeredKernel, eval_mul, eval_C, eval_sub, eval_mul, eval_mul,
        pochhammer_eval, pochhammer_eval, pochhammer_eval, pochhammer_eval]
    rw [show z + (-a) = z - a from by ring]
    rw [show z + (-c) = z - c from by ring]
    ring
  rw [Finset.sum_congr rfl h_each]
  rw [Finset.sum_sub_distrib]
  -- Apply `centered_single_eval` twice (for α = a, α = c).
  rw [centered_single_eval n j h2j a z]
  rw [centered_single_eval n j h2j c z]
  -- Now the RHS evaluation.
  rw [eval_mul, eval_sub, centeredFactor_eval, centeredFactor_eval]
  rw [linearPochhammer_eval]
  ring

/-! ## Palindromic-input symmetries for the centered operator

Two non-trivial identities on palindromic `Q`:

* `centeredOperator n a c Q = centeredOperator n (-a) (-c) Q` (via the
  `k ↔ n - k` reindexing).
* `centeredOperator n a c Q = - centeredOperator n c a Q` (sign flip).

These let us reduce the four sufficiency cases for `(a, c)` to a single one.
-/

/-- Sign-flip symmetry of `centeredKernel`. -/
private lemma centeredKernel_swap (n k : ℕ) (a c : ℝ) :
    centeredKernel n k c a = - centeredKernel n k a c := by
  unfold centeredKernel; ring

/-- On palindromic input, swapping `a ↔ c` negates the centered operator. -/
private lemma centeredOperator_swap_neg (n : ℕ) (a c : ℝ) (Q : ℝ[X]) :
    centeredOperator n c a Q = - centeredOperator n a c Q := by
  unfold centeredOperator
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intros k _
  rw [centeredKernel_swap]
  ring

/-- Reindexing identity: `centeredKernel n (n-k) a c = centeredKernel n k (-a) (-c)`. -/
private lemma centeredKernel_reindex (n k : ℕ) (hk : k ≤ n) (a c : ℝ) :
    centeredKernel n (n - k) a c = centeredKernel n k (-a) (-c) := by
  unfold centeredKernel
  have hnk : n - (n - k) = k := by omega
  rw [hnk]
  rw [show (-(-a)) = a from by ring, show (-(-c)) = c from by ring]
  ring

/-- On palindromic input of degree `n`, the centered operator with `(a, c)`
equals the centered operator with `(-a, -c)`. -/
private lemma centeredOperator_neg_neg_of_palindromic
    {n : ℕ} {Q : ℝ[X]} (hpal : PalindromicOfDegree n Q) (a c : ℝ) :
    centeredOperator n (-a) (-c) Q = centeredOperator n a c Q := by
  unfold centeredOperator
  obtain ⟨_, hsym⟩ := hpal
  rw [sum_range_reflect_succ n
        (fun k => C (Q.coeff k) * centeredKernel n k (-a) (-c))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hk_le : k ≤ n := by omega
  -- Goal: C (Q.coeff (n - k)) * centeredKernel n (n - k) (-a) (-c)
  --     = C (Q.coeff k) * centeredKernel n k a c
  rw [centeredKernel_reindex n k hk_le (-a) (-c)]
  rw [show (-(-a) : ℝ) = a from by ring, show (-(-c) : ℝ) = c from by ring]
  congr 1
  congr 1
  exact (hsym k hk_le).symm

/-! ## Sufficiency direction

If `{a², c²} = {0, 1}`, then `(a, c)` is `(0, ±1)` or `(±1, 0)` (six cases
once signs are accounted for).  Each reduces to `original_kernel_palindromic`
via the symmetries above.
-/

/-- Sign-flip preserves `HasOnlyRealNonposZeros`. -/
private lemma hasOnlyRealNonposZeros_neg (p : ℝ[X]) :
    HasOnlyRealNonposZeros (-p) ↔ HasOnlyRealNonposZeros p := by
  have hmap : toComplex (-p) = - toComplex p := by
    simp [toComplex, Polynomial.map_neg]
  constructor <;> intro h
  · rcases h with hp_zero | hp
    · left
      have : p = - (-p) := by ring
      rw [this, hp_zero]; simp
    · right
      intro z hz
      have hz' : (toComplex (-p)).eval z = 0 := by
        rw [hmap, eval_neg, hz]; ring
      exact hp z hz'
  · rcases h with hp_zero | hp
    · left; rw [hp_zero]; simp
    · right
      intro z hz
      have hz' : (toComplex p).eval z = 0 := by
        rw [hmap, eval_neg, neg_eq_zero] at hz
        exact hz
      exact hp z hz'

/-- The base case: `(a, c) = (0, 1)` is universally admissible on palindromic
inputs.  This follows from `original_kernel_palindromic` (for `n ≥ 2`) plus
direct computation in the trivial degenerate cases `n = 0, 1`. -/
private theorem centered_admissible_zero_one : UniversallyAdmissibleCentered 0 1 := by
  intro n Q hpal hroot
  rw [centeredOperator_zero_one]
  -- Now we need: HasOnlyRealNonposZeros (rungOperator n 1 0 Q).
  -- For n ≥ 2 use the ladder; for n < 2 compute that the operator is zero.
  by_cases hn2 : 2 ≤ n
  · -- n ≥ 2 case.
    obtain ⟨m, ε, hε, hn_eq, hm⟩ :
        ∃ m ε : ℕ, (ε = 0 ∨ ε = 1) ∧ n = 2 * m + ε ∧ 1 ≤ m := by
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
      · refine ⟨k, 0, Or.inl rfl, by omega, ?_⟩; omega
      · refine ⟨k, 1, Or.inr rfl, by omega, ?_⟩; omega
    exact original_kernel_palindromic n m ε Q hε hn_eq hm hpal hroot
  · -- n < 2: the operator is identically 0 on palindromic input.
    have hn_lt : n < 2 := Nat.lt_of_not_le hn2
    interval_cases n
    · -- n = 0: degree-0 palindrome; rungOperator 0 1 0 Q reduces via
      --   centeredOperator_zero_one and a direct kernel computation.
      left
      unfold rungOperator
      rw [show Finset.range (0 + 1) = {0} from rfl, Finset.sum_singleton]
      have h_kern : rungKernel 0 0 1 0 = 0 := by
        unfold rungKernel
        rw [show Finset.range (1 + 1) = {0, 1} from rfl, Finset.sum_insert (by simp),
          Finset.sum_singleton]
        simp [lambda, pochhammer]
      rw [h_kern]; ring
    · -- n = 1: palindromic gives Q.coeff 0 = Q.coeff 1; operator collapses to 0.
      obtain ⟨_, hsym⟩ := hpal
      have hc01 : Q.coeff 0 = Q.coeff 1 := by
        have h := hsym 0 (by omega); simpa using h
      left
      unfold rungOperator
      rw [show Finset.range (1 + 1) = {0, 1} from rfl, Finset.sum_insert (by simp),
        Finset.sum_singleton]
      -- Compute rungKernel 1 0 1 0 and rungKernel 1 1 1 0.
      have h_k0 : rungKernel 1 0 1 0 = 1 := by
        unfold rungKernel pochhammer
        rw [show Finset.range (1 + 1) = {0, 1} from rfl, Finset.sum_insert (by simp),
          Finset.sum_singleton]
        simp [lambda]
      have h_k1 : rungKernel 1 1 1 0 = -1 := by
        unfold rungKernel pochhammer
        rw [show Finset.range (1 + 1) = {0, 1} from rfl, Finset.sum_insert (by simp),
          Finset.sum_singleton]
        simp [lambda]
      rw [h_k0, h_k1]
      rw [hc01]; ring

/-- Sufficiency: if `{a², c²} = {0, 1}`, the centered operator is universally
admissible on palindromic, negative-rooted inputs. -/
private theorem centered_admissible_of_set_eq_zero_one
    (a c : ℝ) (hset : ({a ^ 2, c ^ 2} : Set ℝ) = ({0, 1} : Set ℝ)) :
    UniversallyAdmissibleCentered a c := by
  -- From the set equality, `(a², c²)` is `(0, 1)` or `(1, 0)`.
  have ha2c2 : a ^ 2 = 0 ∧ c ^ 2 = 1 ∨ a ^ 2 = 1 ∧ c ^ 2 = 0 := by
    have h_a_mem : (a ^ 2 : ℝ) ∈ ({0, 1} : Set ℝ) := by
      rw [← hset]; simp
    have h_c_mem : (c ^ 2 : ℝ) ∈ ({0, 1} : Set ℝ) := by
      rw [← hset]; simp
    have h_one_mem : (1 : ℝ) ∈ ({a ^ 2, c ^ 2} : Set ℝ) := by rw [hset]; simp
    have h_zero_mem : (0 : ℝ) ∈ ({a ^ 2, c ^ 2} : Set ℝ) := by rw [hset]; simp
    have h_a : a ^ 2 = 0 ∨ a ^ 2 = 1 := by
      rcases h_a_mem with h | h
      · exact Or.inl h
      · exact Or.inr (Set.mem_singleton_iff.mp h)
    have h_c : c ^ 2 = 0 ∨ c ^ 2 = 1 := by
      rcases h_c_mem with h | h
      · exact Or.inl h
      · exact Or.inr (Set.mem_singleton_iff.mp h)
    rcases h_a with ha | ha <;> rcases h_c with hc | hc
    · -- both 0: need 1 ∈ {0, 0}.
      exfalso
      rcases h_one_mem with h | h
      · rw [ha] at h; exact zero_ne_one h.symm
      · rw [hc] at h
        exact zero_ne_one (Set.mem_singleton_iff.mp h).symm
    · exact Or.inl ⟨ha, hc⟩
    · exact Or.inr ⟨ha, hc⟩
    · -- both 1: need 0 ∈ {1, 1}.
      exfalso
      rcases h_zero_mem with h | h
      · rw [ha] at h; exact zero_ne_one h
      · rw [hc] at h
        exact zero_ne_one (Set.mem_singleton_iff.mp h)
  -- From `x² = 0` get `x = 0`; from `x² = 1` get `x = 1 ∨ x = -1`.
  have hsq_to_val : ∀ (x : ℝ), x ^ 2 = 0 → x = 0 := by
    intro x hx
    have : x * x = 0 := by rw [← sq]; exact hx
    exact mul_self_eq_zero.mp this
  have hsq_to_pmone : ∀ (x : ℝ), x ^ 2 = 1 → x = 1 ∨ x = -1 := by
    intro x hx
    have hf : (x - 1) * (x + 1) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp hf with h | h
    · left; linarith
    · right; linarith
  intro n Q hpal hroot
  -- Reduce all four cases for `(a, c)` to `(0, 1)`.
  -- Step (i): `centeredOperator n a c Q = ± centeredOperator n 0 1 Q` after the
  -- `(-a, -c)` reduction on palindromic input.
  have hbase : HasOnlyRealNonposZeros (centeredOperator n 0 1 Q) :=
    centered_admissible_zero_one n Q hpal hroot
  rcases ha2c2 with ⟨ha2, hc2⟩ | ⟨ha2, hc2⟩
  · -- a² = 0, c² = 1.
    have ha_zero : a = 0 := hsq_to_val a ha2
    rcases hsq_to_pmone c hc2 with hc_one | hc_neg
    · -- (a, c) = (0, 1): direct.
      subst ha_zero; subst hc_one
      exact hbase
    · -- (a, c) = (0, -1): reduce via `centeredOperator_neg_neg_of_palindromic`.
      subst ha_zero; subst hc_neg
      have h_eq : centeredOperator n 0 (-1) Q = centeredOperator n 0 1 Q := by
        have h := centeredOperator_neg_neg_of_palindromic hpal 0 1
        simpa using h
      rw [h_eq]; exact hbase
  · -- a² = 1, c² = 0.
    have hc_zero : c = 0 := hsq_to_val c hc2
    rcases hsq_to_pmone a ha2 with ha_one | ha_neg
    · -- (a, c) = (1, 0): sign-flip via swap.
      subst hc_zero; subst ha_one
      have h_swap : centeredOperator n 1 0 Q = - centeredOperator n 0 1 Q :=
        centeredOperator_swap_neg n 0 1 Q
      rw [h_swap]
      exact (hasOnlyRealNonposZeros_neg _).mpr hbase
    · -- (a, c) = (-1, 0): combine swap with `(-a, -c)` reduction.
      subst hc_zero; subst ha_neg
      have h_swap : centeredOperator n (-1) 0 Q = - centeredOperator n 0 (-1) Q :=
        centeredOperator_swap_neg n 0 (-1) Q
      have h_red : centeredOperator n 0 (-1) Q = centeredOperator n 0 1 Q := by
        have h := centeredOperator_neg_neg_of_palindromic hpal 0 1
        simpa using h
      rw [h_swap, h_red]
      exact (hasOnlyRealNonposZeros_neg _).mpr hbase

/-! ## Test polynomials for necessity

We build the polynomial family `quadFactor λ = λ X² + (2λ+1) X + λ` and its
powers.  For `λ > 0`, `quadFactor λ` is palindromic of degree 2 with two real
negative roots.  Its squares (degree 4) and cubes (degree 6) provide our
`Q_λ` and `Q_ε` test polynomials.
-/

/-- `quadFactor λ = λ X² + (2λ + 1) X + λ`. -/
private def quadFactor (lam : ℝ) : ℝ[X] :=
  C lam * X ^ 2 + C (2 * lam + 1) * X + C lam

/-- For `λ > 0`, `quadFactor λ` has natDegree 2. -/
private lemma quadFactor_natDegree {lam : ℝ} (hlam : 0 < lam) :
    (quadFactor lam).natDegree = 2 := by
  unfold quadFactor
  -- Apply compute_degree! to the polynomial.
  compute_degree!
  exact ne_of_gt hlam

/-- The coefficients of `quadFactor λ`. -/
private lemma quadFactor_coeff (lam : ℝ) (k : ℕ) (hk : k ≤ 2) :
    (quadFactor lam).coeff k =
      if k = 0 then lam else if k = 1 then 2 * lam + 1 else lam := by
  unfold quadFactor
  rw [Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul, Polynomial.coeff_X,
      Polynomial.coeff_C]
  interval_cases k <;> simp

/-- `quadFactor λ` is palindromic of degree 2. -/
private lemma quadFactor_palindromic {lam : ℝ} (hlam : 0 < lam) :
    PalindromicOfDegree 2 (quadFactor lam) := by
  refine ⟨by rw [quadFactor_natDegree hlam], ?_⟩
  intro k hk
  rw [quadFactor_coeff lam k hk, quadFactor_coeff lam (2 - k) (by omega)]
  interval_cases k <;> rfl

private lemma quadFactor_ne_zero {lam : ℝ} (hlam : 0 < lam) :
    quadFactor lam ≠ 0 := by
  intro h
  have : (quadFactor lam).natDegree = 0 := by rw [h]; simp
  rw [quadFactor_natDegree hlam] at this
  omega

/-- The discriminant `(2λ+1)² - 4λ² = 4λ + 1` of `quadFactor λ`. -/
private lemma quadFactor_discrim (lam : ℝ) :
    (2 * lam + 1) ^ 2 - 4 * lam ^ 2 = 4 * lam + 1 := by ring

/-- Auxiliary: `√(4λ+1) < 2λ + 1` for `λ > 0`. -/
private lemma sqrt_lt_two_lam_plus_one {lam : ℝ} (hlam : 0 < lam) :
    Real.sqrt (4 * lam + 1) < 2 * lam + 1 := by
  have h_4l_pos : 0 < 4 * lam + 1 := by linarith
  have h_2l_pos : 0 < 2 * lam + 1 := by linarith
  rw [show (2 * lam + 1 : ℝ) = Real.sqrt ((2 * lam + 1) ^ 2) from
    (Real.sqrt_sq h_2l_pos.le).symm]
  apply Real.sqrt_lt_sqrt h_4l_pos.le
  rw [show (2 * lam + 1 : ℝ) ^ 2 = (4 * lam + 1) + 4 * lam ^ 2 from by ring]
  nlinarith [sq_nonneg lam]

/-- For `λ > 0`, `quadFactor λ` has only real negative zeros. -/
private lemma quadFactor_hasOnlyRealNegativeZeros {lam : ℝ} (hlam : 0 < lam) :
    HasOnlyRealNegativeZeros (quadFactor lam) := by
  -- Factor as `C lam * (X + C u) * (X + C v)` with `u, v > 0`.
  set s := Real.sqrt (4 * lam + 1)
  have h_4l_pos : 0 < 4 * lam + 1 := by linarith
  have hs_pos : 0 < s := Real.sqrt_pos.mpr h_4l_pos
  have hs_lt : s < 2 * lam + 1 := sqrt_lt_two_lam_plus_one hlam
  have hs_sq : s ^ 2 = 4 * lam + 1 := Real.sq_sqrt h_4l_pos.le
  set u := (2 * lam + 1 - s) / (2 * lam) with hu_def
  set v := (2 * lam + 1 + s) / (2 * lam) with hv_def
  have hu_pos : 0 < u := by
    apply div_pos
    · linarith
    · linarith
  have hv_pos : 0 < v := by
    apply div_pos
    · linarith
    · linarith
  -- Verify factorization: λ(X + u)(X + v) = quadFactor λ.
  have h_uv : u + v = (2 * lam + 1) / lam := by
    rw [hu_def, hv_def]; field_simp; ring
  have h_uv_prod : u * v = 1 := by
    rw [hu_def, hv_def]
    have hne : (2 * lam : ℝ) ≠ 0 := by linarith
    field_simp
    rw [show (2 * lam + 1 - s) * (2 * lam + 1 + s) =
        (2 * lam + 1) ^ 2 - s ^ 2 from by ring]
    rw [hs_sq]
    ring
  have h_factor : quadFactor lam = C lam * ((X + C u) * (X + C v)) := by
    unfold quadFactor
    have hne_lam : lam ≠ 0 := ne_of_gt hlam
    rw [show (X + C u) * (X + C v) =
        X ^ 2 + C (u + v) * X + C (u * v) from by
      rw [Polynomial.C_add, Polynomial.C_mul]; ring]
    rw [h_uv, h_uv_prod]
    rw [show (2 * lam + 1 : ℝ) / lam = (2 * lam + 1) * (1 / lam) from by ring]
    rw [Polynomial.C_mul]
    rw [show C (2 * lam + 1) * C (1 / lam) * X = C (2 * lam + 1) * (C (1 / lam) * X)
        from by ring]
    rw [show (C lam : ℝ[X]) * (X ^ 2 + C (2 * lam + 1) * (C (1 / lam) * X) + C 1) =
        C lam * X ^ 2 + (C lam * C (2 * lam + 1) * C (1 / lam)) * X + C lam * C 1
        from by ring]
    rw [show (C lam : ℝ[X]) * C (2 * lam + 1) * C (1 / lam) = C (2 * lam + 1)
        from by
      rw [← Polynomial.C_mul, ← Polynomial.C_mul]
      congr 1
      field_simp]
    rw [show (C lam : ℝ[X]) * C 1 = C lam from by rw [← Polynomial.C_mul]; ring_nf]
  rw [h_factor]
  apply const_mul_preserves_negative
  apply mul_preserves_negative
  · -- X + C u has root -u < 0.
    have := pochhammer_negative (a := u) 1 hu_pos
    unfold pochhammer at this
    rw [show ∏ i ∈ Finset.range 1, (X + C (u + (i : ℝ))) = X + C u from by
      rw [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]; simp] at this
    exact this
  · -- X + C v has root -v < 0.
    have := pochhammer_negative (a := v) 1 hv_pos
    unfold pochhammer at this
    rw [show ∏ i ∈ Finset.range 1, (X + C (v + (i : ℝ))) = X + C v from by
      rw [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]; simp] at this
    exact this

/-- For `λ > 0`, powers of `quadFactor λ` have only real negative zeros. -/
private lemma quadFactor_pow_hasOnlyRealNegativeZeros
    {lam : ℝ} (hlam : 0 < lam) (k : ℕ) :
    HasOnlyRealNegativeZeros ((quadFactor lam) ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero]
    right
    intro z hz
    exfalso
    have h1 : toComplex (1 : ℝ[X]) = (1 : ℂ[X]) := by
      unfold toComplex; rw [Polynomial.map_one]
    rw [h1, Polynomial.eval_one] at hz
    exact one_ne_zero hz
  | succ k ih =>
    rw [pow_succ]
    exact mul_preserves_negative _ _ ih (quadFactor_hasOnlyRealNegativeZeros hlam)

/-- For `λ > 0`, `(quadFactor λ)^k` is palindromic of degree `2k`. -/
private lemma quadFactor_pow_palindromic
    {lam : ℝ} (hlam : 0 < lam) (k : ℕ) :
    PalindromicOfDegree (2 * k) ((quadFactor lam) ^ k) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp
    · intro j hj; interval_cases j; rfl
  | succ k ih =>
    rw [pow_succ, show 2 * (k + 1) = 2 * k + 2 from by ring]
    exact ih.mul (quadFactor_palindromic hlam)

/-! ## n = 4 test polynomial and image computation -/

/-- `Q_n4 λ := (quadFactor λ)^2`.  We show this equals the γ-sum
`λ²·gammaBasis 4 0 + 2λ·gammaBasis 4 1 + gammaBasis 4 2`. -/
private def Q_n4 (lam : ℝ) : ℝ[X] := (quadFactor lam) ^ 2

/-- Alternative form of `quadFactor λ` as `C λ * (1+X)² + X`. -/
private lemma quadFactor_alt (lam : ℝ) :
    quadFactor lam = C lam * (1 + X) ^ 2 + X := by
  apply Polynomial.funext
  intro z
  unfold quadFactor
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_one]
  ring

private lemma Q_n4_eq_gammaSum (lam : ℝ) :
    Q_n4 lam =
      C (lam ^ 2) * gammaBasis 4 0 + C (2 * lam) * gammaBasis 4 1 +
        C 1 * gammaBasis 4 2 := by
  apply Polynomial.funext
  intro z
  unfold Q_n4 gammaBasis
  rw [show (4 - 2 * 0 : ℕ) = 4 from rfl,
      show (4 - 2 * 1 : ℕ) = 2 from rfl,
      show (4 - 2 * 2 : ℕ) = 0 from rfl]
  rw [quadFactor_alt]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_one]
  ring

private lemma Q_n4_palindromic {lam : ℝ} (hlam : 0 < lam) :
    PalindromicOfDegree 4 (Q_n4 lam) := by
  have h := quadFactor_pow_palindromic hlam 2
  rw [show (2 * 2 : ℕ) = 4 from rfl] at h
  exact h

private lemma Q_n4_hasOnlyRealNegativeZeros {lam : ℝ} (hlam : 0 < lam) :
    HasOnlyRealNegativeZeros (Q_n4 lam) :=
  quadFactor_pow_hasOnlyRealNegativeZeros hlam 2

/-! ### Linearity of the centered operator -/

private lemma centeredOperator_add (n : ℕ) (a c : ℝ) (P Q : ℝ[X]) :
    centeredOperator n a c (P + Q) =
      centeredOperator n a c P + centeredOperator n a c Q := by
  unfold centeredOperator
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros k _
  rw [Polynomial.coeff_add, Polynomial.C_add, add_mul]

private lemma centeredOperator_C_mul (n : ℕ) (a c b : ℝ) (P : ℝ[X]) :
    centeredOperator n a c (C b * P) = C b * centeredOperator n a c P := by
  unfold centeredOperator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros k _
  rw [Polynomial.coeff_C_mul]
  rw [show C (b * P.coeff k) = C b * C (P.coeff k) from by
    rw [Polynomial.C_mul]]
  ring

/-! ### Small-degree ascPochhammer evaluations (used by both `Q_n4` and `Q_n6`) -/

private lemma ascP0_eval (x : ℝ) : (ascPochhammer ℝ 0).eval x = 1 := by simp

private lemma ascP1_eval (x : ℝ) : (ascPochhammer ℝ 1).eval x = x := by
  rw [ascPochhammer_one]; simp

private lemma ascP2_eval (x : ℝ) : (ascPochhammer ℝ 2).eval x = x * (x + 1) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, ascPochhammer_succ_right]
  simp [ascPochhammer_one]

private lemma ascP3_eval (x : ℝ) :
    (ascPochhammer ℝ 3).eval x = x * (x + 1) * (x + 2) := by
  rw [show (3 : ℕ) = 1 + 1 + 1 from rfl]
  repeat rw [ascPochhammer_succ_right]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_natCast]
  rw [show ascPochhammer ℝ 0 = 1 from rfl]
  simp

private lemma ascP4_eval (x : ℝ) :
    (ascPochhammer ℝ 4).eval x = x * (x + 1) * (x + 2) * (x + 3) := by
  rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl]
  repeat rw [ascPochhammer_succ_right]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_natCast]
  rw [show ascPochhammer ℝ 0 = 1 from rfl]
  simp

private lemma ascP6_eval (x : ℝ) :
    (ascPochhammer ℝ 6).eval x = x * (x + 1) * (x + 2) * (x + 3) * (x + 4) * (x + 5) := by
  rw [show (6 : ℕ) = 1 + 1 + 1 + 1 + 1 + 1 from rfl]
  repeat rw [ascPochhammer_succ_right]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_natCast]
  rw [show ascPochhammer ℝ 0 = 1 from rfl]
  simp

/-! ### Image of `Q_n4 λ` under the centered operator

Combining linearity with `centered_action_on_gammaBasis` gives an explicit
closed form for the image, evaluated at any `z`.
-/

/-- Closed-form evaluation of the centered operator on `Q_n4 λ`. -/
private lemma centeredOperator_Q_n4_eval (a c lam z : ℝ) :
    (centeredOperator 4 a c (Q_n4 lam)).eval z =
      (c ^ 2 - a ^ 2) *
        (2 * lam * (2 * z + 2) * (2 * z + 3) + 2 * z ^ 2 + 2 * z + 1 -
          (a ^ 2 + c ^ 2)) := by
  -- Expand via γ-decomposition and the action lemma.
  rw [Q_n4_eq_gammaSum]
  rw [centeredOperator_add, centeredOperator_add, centeredOperator_C_mul,
      centeredOperator_C_mul, centeredOperator_C_mul]
  rw [centered_action_on_gammaBasis 4 0 (by omega) a c,
      centered_action_on_gammaBasis 4 1 (by omega) a c,
      centered_action_on_gammaBasis 4 2 (by omega) a c]
  -- Evaluate the resulting polynomial at z by simp + pochhammer/ascP unfolds.
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub]
  unfold centeredFactor
  simp only [Polynomial.eval_mul, pochhammer_eval, linearPochhammer_eval]
  have hAP0 := ascP0_eval
  have hAP1 := ascP1_eval
  have hAP2 := ascP2_eval
  have hAP4 := ascP4_eval
  simp_rw [hAP0, hAP1, hAP2, hAP4]
  ring

/-! ### Helper: real / complex eval bridge -/

/-- If `P` has only real nonpositive zeros and `r > 0` is real, then `P.eval r ≠ 0`. -/
private lemma eval_pos_ne_zero {P : ℝ[X]} {r : ℝ}
    (hP : HasOnlyRealNonposZeros P) (hP_ne : P ≠ 0) (hr : 0 < r) :
    P.eval r ≠ 0 := by
  intro h_eval
  rcases hP with h | h
  · exact hP_ne h
  · have h_complex : (toComplex P).eval (r : ℂ) = 0 :=
      (isRoot_toComplex_iff_real P r).mpr h_eval
    obtain ⟨s, hs, hrs⟩ := h _ h_complex
    have hrs' : (r : ℂ) = (s : ℂ) := hrs
    have : r = s := by exact_mod_cast hrs'
    linarith

/-! ### σ = 1: the n = 4 necessity step -/

/-- For `u = a²`, `v = c²`, `δ = v - u > 0`, and `σ = u + v`, the evaluation
of `centeredOperator 4 a c (Q_n4 λ)` at `z` simplifies. -/
private lemma centeredOperator_Q_n4_eval_at_zero (a c lam : ℝ) :
    (centeredOperator 4 a c (Q_n4 lam)).eval 0 =
      (c ^ 2 - a ^ 2) * (12 * lam + 1 - (a ^ 2 + c ^ 2)) := by
  rw [centeredOperator_Q_n4_eval]
  ring

private lemma centeredOperator_Q_n4_eval_at_one (a c lam : ℝ) :
    (centeredOperator 4 a c (Q_n4 lam)).eval 1 =
      (c ^ 2 - a ^ 2) * (40 * lam + 5 - (a ^ 2 + c ^ 2)) := by
  rw [centeredOperator_Q_n4_eval]
  ring

/-- If `a² < c²` and `σ = a² + c² > 1`, choosing `λ_0 = (σ - 1)/24 > 0` gives
`P.eval 0 < 0` and `P.eval 1 > 0`; by IVT, `P` has a positive real root,
contradicting admissibility. -/
private lemma sigma_le_one_of_admissible (a c : ℝ) (huv : a ^ 2 < c ^ 2)
    (hadmit : UniversallyAdmissibleCentered a c) :
    a ^ 2 + c ^ 2 ≤ 1 := by
  by_contra hgt
  have hgt : 1 < a ^ 2 + c ^ 2 := lt_of_not_ge hgt
  -- σ > 1
  set lam := (a ^ 2 + c ^ 2 - 1) / 24 with hlam_def
  have hlam_pos : 0 < lam := by
    rw [hlam_def]; apply div_pos <;> linarith
  -- Show Q_n4 lam is in the class.
  have hQ_pal : PalindromicOfDegree 4 (Q_n4 lam) := Q_n4_palindromic hlam_pos
  have hQ_root : HasOnlyRealNegativeZeros (Q_n4 lam) :=
    Q_n4_hasOnlyRealNegativeZeros hlam_pos
  set P := centeredOperator 4 a c (Q_n4 lam)
  -- By admissibility, P has only real nonpositive zeros.
  have hP_nonpos : HasOnlyRealNonposZeros P := hadmit 4 (Q_n4 lam) hQ_pal hQ_root
  -- Evaluate P at 0 and 1.
  have h_delta_pos : 0 < c ^ 2 - a ^ 2 := by linarith
  have h_eval_0 : P.eval 0 = (c ^ 2 - a ^ 2) * (12 * lam + 1 - (a ^ 2 + c ^ 2)) :=
    centeredOperator_Q_n4_eval_at_zero a c lam
  have h_eval_1 : P.eval 1 = (c ^ 2 - a ^ 2) * (40 * lam + 5 - (a ^ 2 + c ^ 2)) :=
    centeredOperator_Q_n4_eval_at_one a c lam
  -- Compute the inner brackets.
  have h_lam_val : 12 * lam + 1 - (a ^ 2 + c ^ 2) = (1 - (a ^ 2 + c ^ 2)) / 2 := by
    rw [hlam_def]; ring
  have h_lam_val_1 : 40 * lam + 5 - (a ^ 2 + c ^ 2) = (10 + 2 * (a ^ 2 + c ^ 2)) / 3 := by
    rw [hlam_def]; ring
  have h_eval_0_neg : P.eval 0 < 0 := by
    rw [h_eval_0, h_lam_val]
    have : (1 - (a ^ 2 + c ^ 2)) / 2 < 0 := by linarith
    have hprod : (c ^ 2 - a ^ 2) * ((1 - (a ^ 2 + c ^ 2)) / 2) < 0 :=
      mul_neg_of_pos_of_neg h_delta_pos this
    exact hprod
  have h_eval_1_pos : P.eval 1 > 0 := by
    rw [h_eval_1, h_lam_val_1]
    have h_inner : (10 + 2 * (a ^ 2 + c ^ 2)) / 3 > 0 := by
      have h1 : (a ^ 2 + c ^ 2) ≥ 0 := by positivity
      linarith
    exact mul_pos h_delta_pos h_inner
  -- Apply IVT to find a real root in (0, 1).
  have hcont : ContinuousOn (fun z => P.eval z) (Set.Icc 0 1) :=
    (P.continuous).continuousOn
  have hivt : (0 : ℝ) ∈ Set.Ioo (P.eval 0) (P.eval 1) := by
    rw [Set.mem_Ioo]
    exact ⟨h_eval_0_neg, h_eval_1_pos⟩
  obtain ⟨r, hr_mem, hr_eval⟩ :=
    intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1) hcont hivt
  rw [Set.mem_Ioo] at hr_mem
  -- r > 0 contradicts admissibility.
  have hP_ne : P ≠ 0 := by
    intro h_zero
    rw [h_zero] at h_eval_1_pos
    simp at h_eval_1_pos
  exact eval_pos_ne_zero hP_nonpos hP_ne hr_mem.1 hr_eval

/-- If `a² < c²` and admissibility holds, then `σ = a² + c² ≥ 1` via the test
`λ = 1/2` (corresponding to `τ = 1`).  At `τ = 1`, the resulting polynomial in
`z` has discriminant `24(σ - 1) < 0` for `σ < 1`, giving complex non-real roots
which contradict admissibility. -/
private lemma sigma_ge_one_of_admissible (a c : ℝ) (huv : a ^ 2 < c ^ 2)
    (hadmit : UniversallyAdmissibleCentered a c) :
    1 ≤ a ^ 2 + c ^ 2 := by
  by_contra hlt
  have hlt : a ^ 2 + c ^ 2 < 1 := lt_of_not_ge hlt
  -- σ < 1
  set lam : ℝ := 1 / 2 with hlam_def
  have hlam_pos : 0 < lam := by rw [hlam_def]; norm_num
  have hQ_pal : PalindromicOfDegree 4 (Q_n4 lam) := Q_n4_palindromic hlam_pos
  have hQ_root : HasOnlyRealNegativeZeros (Q_n4 lam) :=
    Q_n4_hasOnlyRealNegativeZeros hlam_pos
  set P := centeredOperator 4 a c (Q_n4 lam)
  have hP_nonpos : HasOnlyRealNonposZeros P := hadmit 4 (Q_n4 lam) hQ_pal hQ_root
  -- At λ = 1/2, P.eval z = (c² - a²) * (6 z² + 12 z + 7 - σ).
  -- The inner factor has positive minimum (at z = -1) of value 1 - σ > 0,
  -- so the inner factor is positive on ℝ, hence P is positive on ℝ.
  have h_delta_pos : 0 < c ^ 2 - a ^ 2 := by linarith
  have h_eval : ∀ z : ℝ,
      P.eval z = (c ^ 2 - a ^ 2) * (6 * z ^ 2 + 12 * z + 7 - (a ^ 2 + c ^ 2)) := by
    intro z
    rw [centeredOperator_Q_n4_eval]
    rw [hlam_def]; ring
  -- For all real z, the inner factor is positive.
  have h_inner_pos : ∀ z : ℝ,
      0 < 6 * z ^ 2 + 12 * z + 7 - (a ^ 2 + c ^ 2) := by
    intro z
    have h_complete : 6 * z ^ 2 + 12 * z + 7 - (a ^ 2 + c ^ 2) =
        6 * (z + 1) ^ 2 + (1 - (a ^ 2 + c ^ 2)) := by ring
    rw [h_complete]
    have h1 : 0 ≤ 6 * (z + 1) ^ 2 := by positivity
    have h2 : 0 < 1 - (a ^ 2 + c ^ 2) := by linarith
    linarith
  have hP_pos : ∀ z : ℝ, 0 < P.eval z := by
    intro z
    rw [h_eval z]
    exact mul_pos h_delta_pos (h_inner_pos z)
  -- P has no real roots. But P has degree 2 (leading coeff = (c²-a²)·6 > 0).
  have hP_ne : P ≠ 0 := by
    intro h
    have := hP_pos 0
    rw [h] at this
    simp at this
  -- Complex root by FTA: degree (toComplex P) ≥ 1.
  have hPC_ne : toComplex P ≠ 0 := by
    intro h
    apply hP_ne
    unfold toComplex at h
    exact (Polynomial.map_eq_zero_iff (algebraMap ℝ ℂ).injective).mp h
  -- Show natDegree P = 2 via centeredOperator_Q_n4_eval.
  -- (Actually we don't need exact degree; just degree ≥ 1.)
  have hP_deg_pos : 0 < (toComplex P).degree := by
    -- The leading coefficient of P (in z²) is (c²-a²)·6 > 0, hence natDegree ≥ 2.
    have hLC_ne : P.coeff 2 ≠ 0 := by
      -- P.coeff 2 = (c² - a²) · 6 (the coefficient of z²).
      have h_poly_eq : P = C (c ^ 2 - a ^ 2) *
          (C 6 * X ^ 2 + C 12 * X + C (7 - (a ^ 2 + c ^ 2))) := by
        apply Polynomial.funext
        intro z
        rw [h_eval z]
        simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X]
        ring
      rw [h_poly_eq]
      have h_coeff2_calc :
          (C (c ^ 2 - a ^ 2) *
            (C 6 * X ^ 2 + C 12 * X + C (7 - (a ^ 2 + c ^ 2)))).coeff 2 =
          (c ^ 2 - a ^ 2) * 6 := by
        rw [Polynomial.coeff_C_mul]
        rw [Polynomial.coeff_add, Polynomial.coeff_add]
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X]
        rw [Polynomial.coeff_C]
        simp
      rw [h_coeff2_calc]
      have : (c ^ 2 - a ^ 2) * 6 ≠ 0 := by
        have : 0 < (c ^ 2 - a ^ 2) * 6 := by
          apply mul_pos h_delta_pos
          norm_num
        linarith
      exact this
    have hnd : 2 ≤ P.natDegree := Polynomial.le_natDegree_of_ne_zero hLC_ne
    have hPC_nd : 2 ≤ (toComplex P).natDegree := by
      unfold toComplex
      rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]
      exact hnd
    have hPC_nd_pos : 0 < (toComplex P).natDegree := by omega
    exact Polynomial.natDegree_pos_iff_degree_pos.mp hPC_nd_pos
  obtain ⟨z₀, hz₀⟩ := Complex.exists_root hP_deg_pos
  -- z₀ is a complex root of P.  Since P > 0 on ℝ, z₀ is not real.
  rcases hP_nonpos with h | h
  · exact hP_ne h
  · obtain ⟨r, hr_le, hrz⟩ := h z₀ hz₀
    -- r ≤ 0; in particular r is real and P.eval r = 0.
    have h_complex : (toComplex P).eval (r : ℂ) = 0 := by
      rw [← hrz]; exact hz₀
    have h_real_eval : P.eval r = 0 :=
      (isRoot_toComplex_iff_real P r).mp h_complex
    have := hP_pos r
    linarith

/-- The combined `σ = 1` conclusion. -/
private lemma sigma_eq_one_of_admissible (a c : ℝ) (huv : a ^ 2 < c ^ 2)
    (hadmit : UniversallyAdmissibleCentered a c) :
    a ^ 2 + c ^ 2 = 1 := by
  have h1 := sigma_le_one_of_admissible a c huv hadmit
  have h2 := sigma_ge_one_of_admissible a c huv hadmit
  linarith

/-! ## n = 6 test polynomial and image computation

We use `Q_n6 ε := (quadFactor ε)^3`, corresponding to `Γ(t) = (t + ε)^3`.
-/

private def Q_n6 (eps : ℝ) : ℝ[X] := (quadFactor eps) ^ 3

private lemma Q_n6_eq_gammaSum (eps : ℝ) :
    Q_n6 eps =
      C (eps ^ 3) * gammaBasis 6 0 + C (3 * eps ^ 2) * gammaBasis 6 1 +
        C (3 * eps) * gammaBasis 6 2 + C 1 * gammaBasis 6 3 := by
  apply Polynomial.funext
  intro z
  unfold Q_n6 gammaBasis
  rw [show (6 - 2 * 0 : ℕ) = 6 from rfl,
      show (6 - 2 * 1 : ℕ) = 4 from rfl,
      show (6 - 2 * 2 : ℕ) = 2 from rfl,
      show (6 - 2 * 3 : ℕ) = 0 from rfl]
  rw [quadFactor_alt]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_one]
  ring

private lemma Q_n6_palindromic {eps : ℝ} (heps : 0 < eps) :
    PalindromicOfDegree 6 (Q_n6 eps) := by
  have h := quadFactor_pow_palindromic heps 3
  rw [show (2 * 3 : ℕ) = 6 from rfl] at h
  exact h

private lemma Q_n6_hasOnlyRealNegativeZeros {eps : ℝ} (heps : 0 < eps) :
    HasOnlyRealNegativeZeros (Q_n6 eps) :=
  quadFactor_pow_hasOnlyRealNegativeZeros heps 3

/-- Closed-form evaluation of `centeredOperator 6 a c (Q_n6 ε)` at `z`,
expressed as a sum of three blocks plus the `j = 3` difference. -/
private lemma centeredOperator_Q_n6_eval (a c eps z : ℝ) :
    (centeredOperator 6 a c (Q_n6 eps)).eval z =
      3 * eps ^ 2 *
        ((c ^ 2 - a ^ 2) * (2 * z + 2) * (2 * z + 3) * (2 * z + 4) * (2 * z + 5)) +
      3 * eps *
        ((c ^ 2 - a ^ 2) * (z ^ 2 + (z + 1) ^ 2 - (a ^ 2 + c ^ 2)) *
          ((2 * z + 4) * (2 * z + 5))) +
      ((z ^ 2 - a ^ 2) * ((z + 1) ^ 2 - a ^ 2) * ((z + 2) ^ 2 - a ^ 2) -
        (z ^ 2 - c ^ 2) * ((z + 1) ^ 2 - c ^ 2) * ((z + 2) ^ 2 - c ^ 2)) := by
  rw [Q_n6_eq_gammaSum]
  rw [centeredOperator_add, centeredOperator_add, centeredOperator_add,
      centeredOperator_C_mul, centeredOperator_C_mul, centeredOperator_C_mul,
      centeredOperator_C_mul]
  rw [centered_action_on_gammaBasis 6 0 (by omega) a c,
      centered_action_on_gammaBasis 6 1 (by omega) a c,
      centered_action_on_gammaBasis 6 2 (by omega) a c,
      centered_action_on_gammaBasis 6 3 (by omega) a c]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub]
  unfold centeredFactor
  simp only [Polynomial.eval_mul, pochhammer_eval, linearPochhammer_eval]
  have hAP0 := ascP0_eval
  have hAP1 := ascP1_eval
  have hAP2 := ascP2_eval
  have hAP3 := ascP3_eval
  have hAP4 := ascP4_eval
  have hAP6 := ascP6_eval
  simp_rw [hAP0, hAP1, hAP2, hAP3, hAP4, hAP6]
  ring

/-! ### u = 0: the n = 6 necessity step

Combining `σ = 1` (already established) with admissibility on `Q_n6 ε` for
a suitably small `ε > 0` forces `a² = 0`.  We pick `ε = u(1-u)/100` (rational
in `u, v`) so the IVT argument goes through without any square roots.
-/

/-- With `σ = u + v = 1`, the evaluation of `centeredOperator 6 a c (Q_n6 ε)`
at `z = 0`. -/
private lemma centeredOperator_Q_n6_eval_at_zero_sigma_one (a c eps : ℝ)
    (hsigma : a ^ 2 + c ^ 2 = 1) :
    (centeredOperator 6 a c (Q_n6 eps)).eval 0 =
      360 * eps ^ 2 * (c ^ 2 - a ^ 2) +
        a ^ 2 * (1 - a ^ 2) * (2 * a ^ 2 - 1) := by
  rw [centeredOperator_Q_n6_eval]
  have hv : c ^ 2 = 1 - a ^ 2 := by linarith
  rw [hv]
  ring

private lemma centeredOperator_Q_n6_eval_at_one_sigma_one (a c eps : ℝ)
    (hsigma : a ^ 2 + c ^ 2 = 1) :
    (centeredOperator 6 a c (Q_n6 eps)).eval 1 =
      2520 * eps ^ 2 * (c ^ 2 - a ^ 2) +
        504 * eps * (c ^ 2 - a ^ 2) +
        (36 - 73 * a ^ 2 + 3 * a ^ 4 - 2 * a ^ 6) := by
  rw [centeredOperator_Q_n6_eval]
  have hv : c ^ 2 = 1 - a ^ 2 := by linarith
  rw [hv]
  ring

/-- With `σ = 1` and admissibility, `a² = 0`. -/
private lemma u_eq_zero_of_admissible (a c : ℝ) (huv : a ^ 2 < c ^ 2)
    (hsigma : a ^ 2 + c ^ 2 = 1)
    (hadmit : UniversallyAdmissibleCentered a c) :
    a ^ 2 = 0 := by
  -- Assume for contradiction `a² > 0`, so `0 < a² < 1/2` (using σ = 1).
  by_contra hne
  have ha_sq_pos : 0 < a ^ 2 := lt_of_le_of_ne (sq_nonneg a) (Ne.symm hne)
  have ha_sq_lt_half : a ^ 2 < 1 / 2 := by
    have h := huv; linarith
  have ha_sq_lt_one : a ^ 2 < 1 := by linarith
  have h_va : c ^ 2 - a ^ 2 = 1 - 2 * a ^ 2 := by linarith
  have h_va_pos : 0 < c ^ 2 - a ^ 2 := by linarith
  -- Choose eps = a² * (1 - a²) / 100 > 0.
  set eps : ℝ := a ^ 2 * (1 - a ^ 2) / 100 with heps_def
  have heps_pos : 0 < eps := by
    rw [heps_def]
    apply div_pos
    · apply mul_pos ha_sq_pos; linarith
    · norm_num
  have hQ_pal : PalindromicOfDegree 6 (Q_n6 eps) := Q_n6_palindromic heps_pos
  have hQ_root : HasOnlyRealNegativeZeros (Q_n6 eps) :=
    Q_n6_hasOnlyRealNegativeZeros heps_pos
  set P := centeredOperator 6 a c (Q_n6 eps)
  have hP_nonpos : HasOnlyRealNonposZeros P := hadmit 6 (Q_n6 eps) hQ_pal hQ_root
  -- eval at 0: should be negative.
  have h_eval_0 : P.eval 0 = 360 * eps ^ 2 * (c ^ 2 - a ^ 2) +
      a ^ 2 * (1 - a ^ 2) * (2 * a ^ 2 - 1) :=
    centeredOperator_Q_n6_eval_at_zero_sigma_one a c eps hsigma
  have h_eval_0_neg : P.eval 0 < 0 := by
    rw [h_eval_0]
    -- With eps = u(1-u)/100, eps² = u²(1-u)²/10000, 360eps² = 9u²(1-u)²/250.
    have h_eps_sq : 360 * eps ^ 2 = 9 * a ^ 4 * (1 - a ^ 2) ^ 2 / 250 := by
      rw [heps_def]; ring
    rw [h_eps_sq, h_va]
    -- Goal: 9 u² (1-u)² / 250 · (1 - 2u) + u(1-u)(2u - 1) < 0.
    -- Factor out u(1-u)(1-2u) > 0.
    have h_factor :
        9 * a ^ 4 * (1 - a ^ 2) ^ 2 / 250 * (1 - 2 * a ^ 2) +
          a ^ 2 * (1 - a ^ 2) * (2 * a ^ 2 - 1) =
        a ^ 2 * (1 - a ^ 2) * (1 - 2 * a ^ 2) *
          (9 * a ^ 2 * (1 - a ^ 2) / 250 - 1) := by ring
    rw [h_factor]
    -- Show: positive * negative = negative.
    have h_pos : 0 < a ^ 2 * (1 - a ^ 2) * (1 - 2 * a ^ 2) := by
      have h1 : 0 < a ^ 2 := ha_sq_pos
      have h2 : 0 < 1 - a ^ 2 := by linarith
      have h3 : 0 < 1 - 2 * a ^ 2 := by linarith
      positivity
    have h_neg : 9 * a ^ 2 * (1 - a ^ 2) / 250 - 1 < 0 := by
      -- 9 u (1-u) ≤ 9 / 4 < 250 / 4, so 9u(1-u)/250 ≤ 9/1000 < 1.
      have h_ul : a ^ 2 * (1 - a ^ 2) ≤ 1 / 4 := by
        have h_sq : (a ^ 2 - 1 / 2) ^ 2 ≥ 0 := sq_nonneg _
        nlinarith
      have h_lt : 9 * a ^ 2 * (1 - a ^ 2) ≤ 9 / 4 := by nlinarith
      linarith
    have := mul_neg_of_pos_of_neg h_pos h_neg
    exact this
  -- eval at 1: should be positive.
  have h_eval_1 : P.eval 1 = 2520 * eps ^ 2 * (c ^ 2 - a ^ 2) +
      504 * eps * (c ^ 2 - a ^ 2) +
      (36 - 73 * a ^ 2 + 3 * a ^ 4 - 2 * a ^ 6) :=
    centeredOperator_Q_n6_eval_at_one_sigma_one a c eps hsigma
  have h_eval_1_pos : P.eval 1 > 0 := by
    rw [h_eval_1]
    -- All three terms are positive (with 0 < a² < 1/2).
    have h_t1 : 0 < 2520 * eps ^ 2 * (c ^ 2 - a ^ 2) := by
      refine mul_pos (mul_pos ?_ ?_) ?_
      · norm_num
      · exact sq_pos_of_pos heps_pos
      · exact h_va_pos
    have h_t2 : 0 < 504 * eps * (c ^ 2 - a ^ 2) := by
      refine mul_pos (mul_pos ?_ ?_) ?_
      · norm_num
      · exact heps_pos
      · exact h_va_pos
    have h_t3 : 0 < 36 - 73 * a ^ 2 + 3 * a ^ 4 - 2 * a ^ 6 := by
      -- Factor: 36 - 73u + 3u² - 2u³ = -2(u - 1/2)(u² - u + 36) with u = a².
      have h_factor :
          36 - 73 * a ^ 2 + 3 * a ^ 4 - 2 * a ^ 6 =
          -2 * (a ^ 2 - 1 / 2) * ((a ^ 2) ^ 2 - a ^ 2 + 36) := by ring
      rw [h_factor]
      have hu : a ^ 2 - 1 / 2 < 0 := by linarith
      have hq : 0 < (a ^ 2) ^ 2 - a ^ 2 + 36 := by
        have : 0 ≤ (a ^ 2 - 1 / 2) ^ 2 := sq_nonneg _
        nlinarith
      nlinarith
    linarith
  -- IVT applied to P on [0, 1].
  have hcont : ContinuousOn (fun z => P.eval z) (Set.Icc 0 1) :=
    (P.continuous).continuousOn
  have hivt : (0 : ℝ) ∈ Set.Ioo (P.eval 0) (P.eval 1) := by
    rw [Set.mem_Ioo]; exact ⟨h_eval_0_neg, h_eval_1_pos⟩
  obtain ⟨r, hr_mem, hr_eval⟩ :=
    intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1) hcont hivt
  rw [Set.mem_Ioo] at hr_mem
  have hP_ne : P ≠ 0 := by
    intro h_zero
    rw [h_zero] at h_eval_1_pos
    simp at h_eval_1_pos
  exact eval_pos_ne_zero hP_nonpos hP_ne hr_mem.1 hr_eval

/-! ## Main theorem -/

/-- `UniversallyAdmissibleCentered` is symmetric in `(a, c)`. -/
private lemma universallyAdmissible_swap (a c : ℝ) :
    UniversallyAdmissibleCentered a c ↔ UniversallyAdmissibleCentered c a := by
  constructor <;> intro h n Q hpal hroot
  · have h_swap : centeredOperator n c a Q = - centeredOperator n a c Q :=
      centeredOperator_swap_neg n a c Q
    rw [h_swap]
    exact (hasOnlyRealNonposZeros_neg _).mpr (h n Q hpal hroot)
  · have h_swap : centeredOperator n a c Q = - centeredOperator n c a Q :=
      centeredOperator_swap_neg n c a Q
    rw [h_swap]
    exact (hasOnlyRealNonposZeros_neg _).mpr (h n Q hpal hroot)

/-- **Theorem 3 of the paper** — classification of universally-admissible
centered balanced two-product kernels. -/
theorem centered_balanced_classification (a c : ℝ) (h : a ^ 2 ≠ c ^ 2) :
    UniversallyAdmissibleCentered a c ↔
      ({a ^ 2, c ^ 2} : Set ℝ) = ({0, 1} : Set ℝ) := by
  constructor
  · -- Necessity.
    intro hadmit
    -- WLOG `a² < c²`.
    rcases lt_or_gt_of_ne h with huv | huv
    · -- a² < c² (direct).
      have hsigma : a ^ 2 + c ^ 2 = 1 := sigma_eq_one_of_admissible a c huv hadmit
      have hu : a ^ 2 = 0 := u_eq_zero_of_admissible a c huv hsigma hadmit
      have hv : c ^ 2 = 1 := by linarith
      -- Conclude {a², c²} = {0, 1}.
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (rfl | rfl)
        · left; exact hu
        · right; exact hv
      · rintro (rfl | rfl)
        · left; exact hu.symm
        · right; exact hv.symm
    · -- c² < a²: swap via symmetry.
      have hadmit' : UniversallyAdmissibleCentered c a :=
        (universallyAdmissible_swap a c).mp hadmit
      have huv' : c ^ 2 < a ^ 2 := huv
      have hsigma : c ^ 2 + a ^ 2 = 1 := sigma_eq_one_of_admissible c a huv' hadmit'
      have hu : c ^ 2 = 0 := u_eq_zero_of_admissible c a huv' hsigma hadmit'
      have hv : a ^ 2 = 1 := by linarith
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (rfl | rfl)
        · right; exact hv
        · left; exact hu
      · rintro (rfl | rfl)
        · right; exact hu.symm
        · left; exact hv.symm
  · -- Sufficiency.
    exact centered_admissible_of_set_eq_zero_one a c

end GammaPochhammer
