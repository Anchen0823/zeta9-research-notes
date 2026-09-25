/-
Abstract formalization layer of "Research Notes on ζ(9)" (v0.1, Zenodo DOI 10.5281/zenodo.22951155).

Eight self-contained theorems: irrationality criteria from small integer linear forms,
moment-matching quadrature exactness, sign-forcing nonvanishing, Taylor-kernel positivity,
and supporting positivity inequalities. None of the statements mentions ζ(9) or any other
specific number; they are the abstract layer distilled from the research note.

Provenance: the statements and proofs mirror the items of the public prove2.me mission
"Formalize the abstract layer of *Research Notes on ζ(9)* (v0.1)" under the namespace
`Zeta9Note`. They compile against Lean 4 (v4.33.1) and Mathlib (revision 0df444a3).

No claim is made here about the irrationality of ζ(9) itself.
-/

import Mathlib

open Polynomial

namespace Zeta9Note

/-! ### Moment-matching quadrature -/

/-- A linear functional on real polynomials that matches the first five moments of a
weighted five-point sum is exact on all polynomials of degree at most 4. -/
theorem quadrature_exact_of_moments
    (L : Polynomial ℝ →ₗ[ℝ] ℝ) (y w : Fin 5 → ℝ)
    (hmom : ∀ m : ℕ, m ≤ 4 →
      L ((Polynomial.X : Polynomial ℝ) ^ m) = ∑ j : Fin 5, w j * (y j) ^ m) :
    ∀ p : Polynomial ℝ, p.natDegree ≤ 4 →
      L p = ∑ j : Fin 5, w j * p.eval (y j) := by
  intro p hp
  have h5 : p.natDegree < 5 := by omega
  have hL : L p = ∑ i ∈ Finset.range 5, p.coeff i * L (X ^ i) := by
    conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow' p h5]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Polynomial.smul_eq_C_mul, map_smul]
    rfl
  rw [hL]
  have hR : ∑ j : Fin 5, w j * p.eval (y j) = ∑ i ∈ Finset.range 5, p.coeff i * L (X ^ i) := by
    calc ∑ j : Fin 5, w j * p.eval (y j)
        = ∑ j : Fin 5, ∑ i ∈ Finset.range 5, w j * (p.coeff i * (y j) ^ i) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Polynomial.eval_eq_sum_range' h5, Finset.mul_sum]
      _ = ∑ i ∈ Finset.range 5, ∑ j : Fin 5, w j * (p.coeff i * (y j) ^ i) := by
          rw [Finset.sum_comm]
      _ = ∑ i ∈ Finset.range 5, p.coeff i * ∑ j : Fin 5, w j * (y j) ^ i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ i ∈ Finset.range 5, p.coeff i * L (X ^ i) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [hmom i (by have := Finset.mem_range.mp hi; omega)]
  exact hR.symm

/-! ### Weighted-average and mediant inequalities -/

/-- A non-degenerate weighted average of five values with positive weights lies strictly
between the minimum and the maximum of those values. -/
theorem min_lt_weighted_average_lt_max
    (w r : Fin 5 → ℝ) (hw : ∀ j : Fin 5, 0 < w j)
    (hsum : ∑ j : Fin 5, w j = 1)
    (hnd : ∃ j j' : Fin 5, r j ≠ r j') :
    (∃ j : Fin 5, r j < ∑ i : Fin 5, w i * r i) ∧
      (∃ j : Fin 5, (∑ i : Fin 5, w i * r i) < r j) := by
  classical
  obtain ⟨j₁, j₂, hne⟩ := hnd
  have key_lower : ∀ c : ℝ, (∀ i : Fin 5, c ≤ r i) →
      (∑ i : Fin 5, w i * r i = c) → False := by
    intro c hc hval
    have hzero : ∑ i : Fin 5, w i * (r i - c) = 0 := by
      have hsplit : ∑ i : Fin 5, w i * (r i - c)
          = (∑ i : Fin 5, w i * r i) - (∑ i : Fin 5, w i * c) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hsplit, hval, ← Finset.sum_mul, hsum, one_mul, sub_self]
    have hall : ∀ i : Fin 5, r i = c := by
      intro i
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => mul_nonneg (le_of_lt (hw i)) (sub_nonneg.mpr (hc i)))).mp hzero i
        (Finset.mem_univ i)
      exact sub_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hw i)))
    exact hne (by rw [hall j₁, hall j₂])
  have key_upper : ∀ c : ℝ, (∀ i : Fin 5, r i ≤ c) →
      (∑ i : Fin 5, w i * r i = c) → False := by
    intro c hc hval
    have hzero : ∑ i : Fin 5, w i * (c - r i) = 0 := by
      have hsplit : ∑ i : Fin 5, w i * (c - r i)
          = (∑ i : Fin 5, w i * c) - (∑ i : Fin 5, w i * r i) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hsplit, ← Finset.sum_mul, hsum, one_mul, hval, sub_self]
    have hall : ∀ i : Fin 5, r i = c := by
      intro i
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => mul_nonneg (le_of_lt (hw i)) (sub_nonneg.mpr (hc i)))).mp hzero i
        (Finset.mem_univ i)
      exact (sub_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hw i)))).symm
    exact hne (by rw [hall j₁, hall j₂])
  constructor
  · by_contra h
    exact key_lower (∑ i : Fin 5, w i * r i)
      (fun i => not_lt.mp fun hi => h ⟨i, hi⟩) rfl
  · by_contra h
    exact key_upper (∑ i : Fin 5, w i * r i)
      (fun i => not_lt.mp fun hi => h ⟨i, hi⟩) rfl

/-- The mediant of five fractions with positive numerators-weighting and positive
denominators lies strictly between the minimum and the maximum of the fractions,
whenever the fractions are not all equal. -/
theorem mediant_strictly_between_min_and_max
    (w a b : Fin 5 → ℝ)
    (hw : ∀ j : Fin 5, 0 < w j)
    (hb : ∀ j : Fin 5, 0 < b j)
    (hnd : ∃ j j' : Fin 5, a j / b j ≠ a j' / b j') :
    (∃ j : Fin 5,
        a j / b j < (∑ i : Fin 5, w i * a i) / (∑ i : Fin 5, w i * b i)) ∧
      (∃ j : Fin 5,
        (∑ i : Fin 5, w i * a i) / (∑ i : Fin 5, w i * b i) < a j / b j) := by
  classical
  set B : ℝ := ∑ i : Fin 5, w i * b i with hB
  have hBpos : 0 < B := by
    rw [hB]
    exact Finset.sum_pos' (fun i _ => mul_nonneg (le_of_lt (hw i)) (le_of_lt (hb i)))
      ⟨0, Finset.mem_univ 0, mul_pos (hw 0) (hb 0)⟩
  set v : Fin 5 → ℝ := fun j => w j * b j / B with hv
  have hvpos : ∀ j : Fin 5, 0 < v j := fun j => div_pos (mul_pos (hw j) (hb j)) hBpos
  have hvsum : ∑ j : Fin 5, v j = 1 := by
    have h1 : ∑ j : Fin 5, v j = B / B := by
      simp only [hv, div_eq_mul_inv, ← Finset.sum_mul, ← hB]
    rw [h1, div_self (ne_of_gt hBpos)]
  have hmediant : (∑ i : Fin 5, w i * a i) / B = ∑ j : Fin 5, v j * (a j / b j) := by
    have hterm : ∀ j : Fin 5, v j * (a j / b j) = (w j * a j) / B := by
      intro j
      have hBne : B ≠ 0 := ne_of_gt hBpos
      have hbj : b j ≠ 0 := ne_of_gt (hb j)
      simp only [hv]
      field_simp
      try ring
    have hsum : ∑ j : Fin 5, (w j * a j) / B = (∑ j : Fin 5, w j * a j) / B := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
    have h1 : ∑ j : Fin 5, v j * (a j / b j) = (∑ j : Fin 5, w j * a j) / B :=
      (Finset.sum_congr rfl fun j _ => hterm j).trans hsum
    exact h1.symm
  obtain ⟨hs1, hs2⟩ :=
    Zeta9Note.min_lt_weighted_average_lt_max v (fun j => a j / b j) hvpos hvsum hnd
  constructor
  · obtain ⟨j, hj⟩ := hs1
    exact ⟨j, by rw [hmediant]; exact hj⟩
  · obtain ⟨j, hj⟩ := hs2
    exact ⟨j, by rw [hmediant]; exact hj⟩

/-! ### Positivity -/

/-- An entry-wise strictly positive 5×5 real matrix maps every nonzero nonnegative
vector to a strictly positive vector. -/
theorem positive_matrix_maps_nonneg_to_pos
    (M : Matrix (Fin 5) (Fin 5) ℝ) (hM : ∀ i j : Fin 5, 0 < M i j)
    (v : Fin 5 → ℝ) (hv : v ≠ 0) (hvnn : ∀ i : Fin 5, 0 ≤ v i) :
    ∀ i : Fin 5, 0 < M.mulVec v i := by
  have hsome : ∃ j : Fin 5, 0 < v j := by
    by_contra h
    have hle : ∀ j : Fin 5, v j ≤ 0 := fun j => not_lt.mp fun hj => h ⟨j, hj⟩
    exact hv (funext fun j => le_antisymm (hle j) (hvnn j))
  obtain ⟨j₀, hj₀⟩ := hsome
  intro i
  rw [Matrix.mulVec_apply]
  exact Finset.sum_pos' (fun j _ => mul_nonneg (le_of_lt (hM i j)) (hvnn j))
    ⟨j₀, Finset.mem_univ j₀, mul_pos (hM i j₀) hj₀⟩

/-- If a real polynomial has nonnegative Taylor coefficients at a lower bound `u₀` of a
sequence, and a positive summable weighting with at least one positive sample, then the
weighted sample sum is strictly positive. -/
theorem taylor_sign_implies_kernel_sum_pos
    (R u : ℕ → ℝ) (p : Polynomial ℝ) (u₀ : ℝ)
    (hR : ∀ k : ℕ, 0 < R k)
    (hu : ∀ k : ℕ, u₀ ≤ u k)
    (hcoeff : ∀ i : ℕ, 0 ≤ (Polynomial.taylor u₀ p).coeff i)
    (hsummable : Summable (fun k : ℕ => R k * p.eval (u k)))
    (hnonzero : ∃ k : ℕ, 0 < p.eval (u k)) :
    0 < ∑' k : ℕ, R k * p.eval (u k) := by
  have hte : ∀ k : ℕ, p.eval (u k) = (Polynomial.taylor u₀ p).eval (u k - u₀) := by
    intro k
    rw [Polynomial.taylor_eval]
    congr 1
    ring
  have hterm : ∀ k : ℕ, 0 ≤ R k * p.eval (u k) := by
    intro k
    have hsk : 0 ≤ u k - u₀ := sub_nonneg.mpr (hu k)
    have htn : 0 ≤ (Polynomial.taylor u₀ p).eval (u k - u₀) := by
      rw [Polynomial.eval_eq_sum_range]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hcoeff i) (pow_nonneg hsk i)
    rw [hte k]
    exact mul_nonneg (le_of_lt (hR k)) htn
  obtain ⟨k₀, hk₀⟩ := hnonzero
  have hstrict : (fun _ : ℕ => (0 : ℝ)) k₀ < (fun k : ℕ => R k * p.eval (u k)) k₀ :=
    mul_pos (hR k₀) hk₀
  have hlt := Summable.tsum_lt_tsum_of_nonneg
    (f := fun _ : ℕ => (0 : ℝ)) (g := fun k : ℕ => R k * p.eval (u k))
    (fun _ => le_refl 0) hterm hstrict hsummable
  simpa using hlt

/-! ### Nonvanishing from sign conditions -/

/-- If a moment-matched five-point quadrature with positive weights and distinct nodes is
applied to a nonzero polynomial of degree at most 4 whose values at all five nodes share a
sign, then the functional value is nonzero. -/
theorem five_sample_sign_forces_nonzero
    (L : Polynomial ℝ →ₗ[ℝ] ℝ) (y w : Fin 5 → ℝ)
    (hy : Function.Injective y)
    (hw : ∀ j : Fin 5, 0 < w j)
    (hmom : ∀ m : ℕ, m ≤ 4 →
      L ((Polynomial.X : Polynomial ℝ) ^ m) = ∑ j : Fin 5, w j * (y j) ^ m)
    (p : Polynomial ℝ) (hpdeg : p.natDegree ≤ 4) (hp : p ≠ 0)
    (hsign : (∀ j : Fin 5, 0 ≤ p.eval (y j)) ∨ (∀ j : Fin 5, p.eval (y j) ≤ 0)) :
    L p ≠ 0 := by
  have hexp : L p = ∑ j : Fin 5, w j * p.eval (y j) :=
    Zeta9Note.quadrature_exact_of_moments L y w hmom p hpdeg
  intro hLp
  have hsumzero : ∑ j : Fin 5, w j * p.eval (y j) = 0 := by
    rw [← hexp, hLp]
  have hroot : ∀ j : Fin 5, p.eval (y j) = 0 := by
    intro j
    have hterm : w j * p.eval (y j) = 0 := by
      rcases hsign with hsign | hsign
      · exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => mul_nonneg (le_of_lt (hw i)) (hsign i))).mp hsumzero j (Finset.mem_univ j)
      · have hnegsum : ∑ i : Fin 5, -(w i * p.eval (y i)) = 0 := by
          rw [Finset.sum_neg_distrib, hsumzero, neg_zero]
        have hnn : ∀ i ∈ (Finset.univ : Finset (Fin 5)), 0 ≤ -(w i * p.eval (y i)) :=
          fun i _ => neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hw i)) (hsign i))
        have hzi := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hnegsum j (Finset.mem_univ j)
        exact neg_eq_zero.mp hzi
    exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hw j))
  exact hp (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hy hroot
    (by simpa using Nat.lt_succ_of_le hpdeg))

/-! ### Irrationality criteria from small integer linear forms -/

/-- If nonzero integer linear forms `b + a·x` of arbitrarily small absolute value exist,
then `x` is irrational. -/
theorem irrational_of_small_nonzero_integer_forms (x : ℝ)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ b a : ℤ,
        (b : ℝ) + (a : ℝ) * x ≠ 0 ∧
        |(b : ℝ) + (a : ℝ) * x| < ε) :
    Irrational x := by
  apply (irrational_iff_ne_rational x).2
  intro p q hq hx
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hqabs : 0 < |(q : ℝ)| := abs_pos.mpr hqR
  have heps : 0 < (1 : ℝ) / |(q : ℝ)| := one_div_pos.mpr hqabs
  obtain ⟨b, a, hne, hsmall⟩ := h _ heps
  rw [hx] at hsmall hne
  have hform : (b : ℝ) + (a : ℝ) * ((p : ℝ) / (q : ℝ)) =
      ((b * q + a * p : ℤ) : ℝ) / (q : ℝ) := by
    push_cast
    field_simp
  rw [hform, abs_div] at hsmall
  have hreal : |((b * q + a * p : ℤ) : ℝ)| < 1 :=
    (div_lt_div_iff_of_pos_right hqabs).mp hsmall
  have hint : |b * q + a * p| < (1 : ℤ) := by exact_mod_cast hreal
  have hzero : b * q + a * p = 0 := Int.abs_lt_one_iff.mp hint
  have hvan : (b : ℝ) + (a : ℝ) * ((p : ℝ) / (q : ℝ)) = 0 := by
    rw [hform, hzero]
    simp
  exact hne hvan

/-- If two integer linear forms `bᵢ + aᵢ·x` with independent coefficient vectors
(cross determinant nonzero) and arbitrarily small absolute values exist, then `x` is
irrational. -/
theorem irrational_of_two_small_integer_forms (x : ℝ)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ b₁ a₁ b₂ a₂ : ℤ,
        b₁ * a₂ ≠ b₂ * a₁ ∧
        |(b₁ : ℝ) + (a₁ : ℝ) * x| < ε ∧
        |(b₂ : ℝ) + (a₂ : ℝ) * x| < ε) :
    Irrational x := by
  apply (irrational_iff_ne_rational x).2
  intro a b hb hx
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hbabs : 0 < |(b : ℝ)| := abs_pos.mpr hbR
  have heps : 0 < (1 : ℝ) / |(b : ℝ)| := one_div_pos.mpr hbabs
  obtain ⟨b₁, a₁, b₂, a₂, hdet, hsmall₁, hsmall₂⟩ := h _ heps
  rw [hx] at hsmall₁ hsmall₂
  have small_form_zero (c d : ℤ)
      (hs : |(c : ℝ) + (d : ℝ) * ((a : ℝ) / (b : ℝ))| <
        (1 : ℝ) / |(b : ℝ)|) : c * b + d * a = 0 := by
    have hform : (c : ℝ) + (d : ℝ) * ((a : ℝ) / (b : ℝ)) =
        ((c * b + d * a : ℤ) : ℝ) / (b : ℝ) := by
      push_cast
      field_simp
    rw [hform, abs_div] at hs
    have hreal : |((c * b + d * a : ℤ) : ℝ)| < 1 :=
      (div_lt_div_iff_of_pos_right hbabs).mp hs
    have hint : |c * b + d * a| < (1 : ℤ) := by exact_mod_cast hreal
    exact Int.abs_lt_one_iff.mp hint
  have hk₁ : b₁ * b + a₁ * a = 0 := small_form_zero b₁ a₁ hsmall₁
  have hk₂ : b₂ * b + a₂ * a = 0 := small_form_zero b₂ a₂ hsmall₂
  have hcross : (b₁ * a₂ - b₂ * a₁) * b = 0 := by
    calc
      _ = (b₁ * b + a₁ * a) * a₂ - (b₂ * b + a₂ * a) * a₁ := by ring
      _ = 0 := by rw [hk₁, hk₂]; ring
  exact hdet (sub_eq_zero.mp ((mul_eq_zero.mp hcross).resolve_right hb))

end Zeta9Note
