import PEqualNP.Defs
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Algebra.Polynomial.Monomial

namespace GctFrontier.SparseBinomialSupport

open Polynomial Finset

private theorem variations_lt_support (p : ℝ[X]) (hp : p ≠ 0) :
    p.signVariations < p.support.card := by
  have hcard := Polynomial.card_support_eraseLead_add_one hp
  by_cases h : p.eraseLead = 0
  · have hmono := p.eraseLead_add_monomial_natDegree_leadingCoeff
    rw [h,zero_add] at hmono
    have hv : p.signVariations = 0 :=
      (congrArg Polynomial.signVariations hmono.symm).trans (Polynomial.signVariations_monomial ..)
    rw [hv]
    exact Finset.card_pos.mpr (Polynomial.support_nonempty.mpr hp)
  · have ih := variations_lt_support p.eraseLead h
    have hstep := p.signVariations_le_eraseLead_succ
    omega
termination_by p.support.card
decreasing_by exact Polynomial.eraseLead_support_card_lt hp

theorem positive_order_lt_support (p : ℝ[X]) (hp : p ≠ 0) (x : ℝ) (hx : 0 < x) :
    p.rootMultiplicity x < p.support.card := by
  classical
  have count := Multiset.count_le_card x (p.roots.filter (0 < ·))
  rw [Multiset.count_filter_of_pos hx, Polynomial.count_roots] at count
  have desc := p.roots_countP_pos_le_signVariations
  rw [Multiset.countP_eq_card_filter] at desc
  exact (count.trans desc).trans_lt (variations_lt_support p hp)

private theorem add_card (p q : ℝ[X]) :
    (p+q).support.card ≤ p.support.card+q.support.card :=
  (Finset.card_le_card (Polynomial.support_add ..)).trans (Finset.card_union_le _ _)

private theorem mono_card (n : ℕ) (c : ℝ) : (monomial n c).support.card ≤ 1 := by
  simpa using Finset.card_le_card (support_monomial_subset n c)

private theorem weighted_cube_card (p : ℝ[X]) (s : ℝ) (hs : p.support.card ≤ 2) :
    (C s*p^3).support.card ≤ if p.support.card ≤ 1 then 1 else 4 := by
  split_ifs with small
  · obtain ⟨a,u,rfl⟩ := Polynomial.card_support_le_one_iff_monomial.mp small
    rw [monomial_pow,C_mul_monomial]
    apply mono_card
  obtain ⟨T,ht,sz⟩ := Infinite.exists_superset_card_eq p.support 2 hs
  obtain ⟨a,b,hab,ht'⟩ := Finset.card_eq_two.mp sz
  have form : p = monomial a (p.coeff a) + monomial b (p.coeff b) := by
    calc
      p = ∑ i ∈ p.support, monomial i (p.coeff i) := p.as_sum_support
      _ = ∑ i ∈ T, monomial i (p.coeff i) := Finset.sum_subset ht (fun i _ hi => by
        simp [Polynomial.notMem_support_iff.mp hi])
      _ = _ := by rw [ht']; simp [hab]
  have expand (A B : ℝ[X]) : C s*(A+B)^3 =
      C s*A^3 + C (3*s)*(A^2*B) + C (3*s)*(A*B^2) + C s*B^3 := by
    rw [map_mul,map_ofNat]
    ring
  rw [form,expand]
  simp only [monomial_pow,monomial_mul_monomial,C_mul_monomial]
  grw [add_card,add_card,add_card,mono_card,mono_card,mono_card,mono_card]

theorem support_bound (s : Fin 3 → ℝ) (g : Fin 3 → ℝ[X]) (hg : ∀ i, (g i).support.card ≤ 2) :
    (∑ i, C (s i)*(g i)^3).support.card ≤
      ∑ i, (if (g i).support.card ≤ 1 then 1 else 4) := by
  simp only [Fin.sum_univ_three]
  grw [add_card, add_card, weighted_cube_card _ _ (hg 0),
    weighted_cube_card _ _ (hg 1), weighted_cube_card _ _ (hg 2)]

theorem order_bounds (s : Fin 3 → ℝ) (g : Fin 3 → ℝ[X]) (hg : ∀ i, (g i).support.card ≤ 2) :
    let f := ∑ i, C (s i)*(g i)^3
    f ≠ 0 → ∀ x : ℝ, 0 < x → f.rootMultiplicity x ≤ 11 ∧
      ((∃ i, (g i).support.card ≤ 1) → f.rootMultiplicity x ≤ 8) := by
  intro f hf x hx
  have h := (positive_order_lt_support f hf x hx).trans_le (support_bound s g hg)
  simp only [Fin.sum_univ_three] at h
  have bound (i : Fin 3) : (if (g i).support.card ≤ 1 then 1 else 4) ≤ 4 := by
    split <;> decide
  have b0 := bound 0
  have b1 := bound 1
  have b2 := bound 2
  constructor
  · omega
  · rintro ⟨i,hi⟩
    have one_small : (g 0).support.card ≤ 1 ∨ (g 1).support.card ≤ 1 ∨ (g 2).support.card ≤ 1 := by
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr (Or.inl hi)
      · exact Or.inr (Or.inr hi)
    rcases one_small with sm | sm | sm <;> rw [ite_eq_left sm] at h <;> omega

end GctFrontier.SparseBinomialSupport

theorem PEqualNP.Research.SparseBinomialSupport :
    (∀ (p : Polynomial ℝ), p ≠ 0 → ∀ x : ℝ, 0 < x → p.rootMultiplicity x < p.support.card) ∧
    (∀ (s : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ), (∀ i, (g i).support.card ≤ 2) →
      (∑ i, Polynomial.C (s i)*(g i)^3).support.card ≤
        ∑ i, (if (g i).support.card ≤ 1 then 1 else 4)) ∧
    (∀ (s : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ), (∀ i, (g i).support.card ≤ 2) →
      let f := ∑ i, Polynomial.C (s i)*(g i)^3
      f ≠ 0 → ∀ x : ℝ, 0 < x → f.rootMultiplicity x ≤ 11 ∧
        ((∃ i, (g i).support.card ≤ 1) → f.rootMultiplicity x ≤ 8)) :=
  ⟨GctFrontier.SparseBinomialSupport.positive_order_lt_support,
    GctFrontier.SparseBinomialSupport.support_bound, GctFrontier.SparseBinomialSupport.order_bounds⟩
