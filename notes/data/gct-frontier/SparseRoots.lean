import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace GctFrontier

open Polynomial

private theorem variations_lt_support (f : Polynomial ℝ) (hf : f ≠ 0) :
    f.signVariations < f.support.card := by
  have hcard := Polynomial.card_support_eraseLead_add_one hf
  by_cases h : f.eraseLead = 0
  · have hmono := f.eraseLead_add_monomial_natDegree_leadingCoeff
    rw [h, zero_add] at hmono
    rw [← hmono, Polynomial.signVariations_monomial]
    simpa [hmono] using Finset.card_pos.mpr (Polynomial.support_nonempty.mpr hf)
  · have ih := variations_lt_support f.eraseLead h
    have hstep := f.signVariations_le_eraseLead_succ
    omega
termination_by f.support.card
decreasing_by exact Polynomial.eraseLead_support_card_lt hf

/-- A bound on the union of the two product supports also covers cancellations. -/
theorem roots_of_support_union (p q r s : Polynomial ℝ) (n : ℕ)
    (hu : ((p*q).support ∪ (r*s).support).card ≤ n + 1) :
    ((p*q-r*s).roots.toFinset.filter (fun x : ℝ => 0 < x)).card ≤ n := by
  classical
  let f := p*q-r*s
  change (f.roots.toFinset.filter (fun x : ℝ => 0 < x)).card ≤ n
  by_cases hz : f = 0
  · simp [hz]
  have hs : f.support ⊆ (p*q).support ∪ (r*s).support := by
    intro i hi
    by_contra hout
    simp only [Finset.mem_union, not_or, Polynomial.mem_support_iff, not_not] at hout
    exact (Polynomial.mem_support_iff.mp hi) (by simp [f, hout])
  have hcard := (Finset.card_le_card hs).trans hu
  have hv := variations_lt_support f hz
  have hd := f.roots_countP_pos_le_signVariations
  rw [Multiset.countP_eq_card_filter] at hd
  rw [← Multiset.toFinset_filter]
  have hdistinct := Multiset.toFinset_card_le (f.roots.filter (0 < ·))
  omega

theorem four_sparse_baseline (p q r s : Polynomial ℝ)
    (hp : p.support.card ≤ 4) (hq : q.support.card ≤ 4)
    (hr : r.support.card ≤ 4) (hs : s.support.card ≤ 4) :
    ((p*q-r*s).roots.toFinset.filter (fun x : ℝ => 0 < x)).card ≤ 31 := by
  apply roots_of_support_union
  have h₁ := (Polynomial.card_support_mul_le (p := p) (q := q)).trans (Nat.mul_le_mul hp hq)
  have h₂ := (Polynomial.card_support_mul_le (p := r) (q := s)).trans (Nat.mul_le_mul hr hs)
  have hu := Finset.card_union_le (p*q).support (r*s).support
  omega

-- A scaled x^d times the product of three factors x^2 + 2^a.
private noncomputable def block (d a b c : ℕ) (scale : ℝ) : Polynomial ℝ :=
  monomial d (scale * 2^(a+b+c)) +
  monomial (d+2) (scale * (2^(a+b) + 2^(a+c) + 2^(b+c))) +
  monomial (d+4) (scale * (2^a + 2^b + 2^c)) +
  monomial (d+6) scale

private theorem block_sparse (d a b c : ℕ) (scale : ℝ) :
    (block d a b c scale).support.card ≤ 4 := by
  have addBound (f g : Polynomial ℝ) :
      (f+g).support.card ≤ f.support.card + g.support.card :=
    (Finset.card_le_card (Polynomial.support_add ..)).trans (Finset.card_union_le _ _)
  have singleBound (i : ℕ) (v : ℝ) : (monomial i v).support.card ≤ 1 := by
    simpa using Finset.card_le_card (support_monomial_subset i v)
  unfold block
  grw [addBound, addBound, addBound, singleBound, singleBound, singleBound, singleBound]

private noncomputable def witness : Polynomial ℝ :=
  block 0 4 12 20 (2^25) * block 0 28 36 44 1 -
  block 1 8 16 24 1 * block 0 32 40 48 1

private theorem crossing (k : Fin 13) :
    witness.eval (4^(k : ℕ)) * witness.eval (4^((k : ℕ)+1)) < 0 := by
  fin_cases k <;> norm_num [witness, block, eval_monomial, eval_add, eval_sub, eval_mul]

/-- An attained lower bound in exactly the four-factor class of L-gct-272. -/
theorem thirteen_positive_roots : ∃ p q r s : Polynomial ℝ,
    (p.support.card ≤ 4 ∧ q.support.card ≤ 4 ∧ r.support.card ≤ 4 ∧ s.support.card ≤ 4) ∧
    13 ≤ ((p*q-r*s).roots.toFinset.filter (fun x : ℝ => 0 < x)).card := by
  classical
  refine ⟨_, _, _, _, ⟨block_sparse 0 4 12 20 (2^25), block_sparse 0 28 36 44 1,
    block_sparse 1 8 16 24 1, block_sparse 0 32 40 48 1⟩, ?_⟩
  change 13 ≤ (witness.roots.toFinset.filter (fun x : ℝ => 0 < x)).card
  have hn : witness ≠ 0 := by
    intro h
    simpa [h] using crossing 0
  have inc : StrictMono (fun n : ℕ => (4 : ℝ)^n) := pow_right_strictMono₀ (by norm_num)
  have roots (k : Fin 13) : ∃ x ∈ Set.Ioo ((4:ℝ)^(k:ℕ)) (4^((k:ℕ)+1)), witness.eval x = 0 := by
    have h := (inc (Nat.lt_succ_self (k : ℕ))).le
    rcases mul_neg_iff.mp (crossing k) with hsign | hsign
    · exact intermediate_value_Ioo' h witness.continuous.continuousOn ⟨hsign.2, hsign.1⟩
    · exact intermediate_value_Ioo h witness.continuous.continuousOn ⟨hsign.1, hsign.2⟩
  choose root hloc hzero using roots
  have hmono : StrictMono root := by
    intro i j hij
    exact (hloc i).2.trans_le ((inc.monotone (show i.val + 1 ≤ j.val from hij)).trans (hloc j).1.le)
  have hcard := Finset.card_le_card_of_injOn root (s := Finset.univ)
    (t := witness.roots.toFinset.filter (fun x : ℝ => 0 < x))
    (fun i _ => Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hn).mpr (hzero i)),
      (pow_pos (by norm_num : (0:ℝ) < 4) _).trans (hloc i).1⟩) hmono.injective.injOn
  simpa using hcard

end GctFrontier
