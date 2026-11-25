import PEqualNP.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Taylor

/-! Exact positive-root multiplicities for sums of three cubes of sparse polynomials.
The carriers come from triples of exponent sets with equal low power sums. -/

namespace GctFrontier.SparseCubeWitnesses

open Polynomial Finset

private noncomputable def carrier {k : ℕ} (e : Fin k → ℕ) (c : Fin k → ℝ) : ℝ[X] :=
  ∑ i, monomial (e i) (c i)

private theorem sparse {k : ℕ} (e : Fin k → ℕ) (c : Fin k → ℝ) :
    (carrier e c).support.card ≤ k := by
  classical
  have hs : (carrier e c).support ⊆ univ.image e := by
    intro j hj
    by_contra he
    have hd : ∀ i, e i ≠ j := by simpa using he
    apply (mem_support_iff.mp hj)
    simp [carrier, coeff_monomial, hd]
  exact (card_le_card hs).trans (by simpa using (card_image_le (s := univ) (f := e)))

private def cubeCoeff {k : ℕ} (e : Fin k → ℕ) (c : Fin k → ℤ) (j : ℕ) : ℤ :=
  ∑ a, ∑ b, ∑ d, c a * c b * c d * (((e a + e b + e d).descFactorial j / j.factorial : ℕ) : ℤ)

private theorem taylor_cube {k : ℕ} (e : Fin k → ℕ) (c : Fin k → ℤ) (j : ℕ) :
    (taylor 1 ((carrier e (fun i => (c i : ℝ)))^3)).coeff j = (cubeCoeff e c j : ℝ) := by
  simp only [carrier, pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum,
    monomial_mul_monomial, map_sum, taylor_monomial, C_1, finsetSum_coeff, coeff_C_mul,
    coeff_X_add_one_pow, cubeCoeff, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
    ← Nat.choose_eq_descFactorial_div_factorial]
  simp only [add_comm, add_left_comm, mul_assoc, mul_comm]

private def totalCoeff {k : ℕ} (e : Fin 3 → Fin k → ℕ) (c : Fin 3 → Fin k → ℤ)
    (w : Fin 3 → ℤ) (j : ℕ) : ℤ := ∑ i, w i * cubeCoeff (e i) (c i) j

private theorem cube_root (a : ℝ) : ∃ t : ℝ, t^3 = a := by
  by_cases h : 0 ≤ a
  · exact ⟨a ^ (3 : ℝ)⁻¹, Real.rpow_inv_natCast_pow h (by decide : (3 : ℕ) ≠ 0)⟩
  · have hn : 0 ≤ -a := by linarith
    refine ⟨-((-a) ^ (3 : ℝ)⁻¹), ?_⟩
    have hv := Real.rpow_inv_natCast_pow hn (by decide : (3 : ℕ) ≠ 0)
    linear_combination -hv

/-- The examples use three ordinary real cubes, so all signs allowed by the desk can be +1. -/
def Witness (k m : ℕ) : Prop :=
  ∃ g : Fin 3 → ℝ[X], (∀ i, (g i).support.card ≤ k) ∧
    (∑ i, g i^3) ≠ 0 ∧ (∑ i, g i^3).rootMultiplicity 1 = m

private theorem certify {k m : ℕ} (e : Fin 3 → Fin k → ℕ) (c : Fin 3 → Fin k → ℤ)
    (w : Fin 3 → ℤ) (low : ∀ d : Fin m, totalCoeff e c w d = 0)
    (top : totalCoeff e c w m ≠ 0) : Witness k m := by
  choose t ht using fun i => cube_root (w i : ℝ)
  let p (i : Fin 3) := carrier (e i) (fun a => (c i a : ℝ))
  let g (i : Fin 3) := carrier (e i) (fun a => t i * (c i a : ℝ))
  have hg (i : Fin 3) : g i = C (t i) * p i := by simp [g,p,carrier,Finset.mul_sum,C_mul_monomial]
  let F := ∑ i, g i^3
  have hc (j : ℕ) : (taylor 1 F).coeff j = (totalCoeff e c w j : ℝ) := by
    simp only [F, hg, mul_pow, ← map_pow, ht, map_sum, taylor_mul, taylor_C, finsetSum_coeff,
      coeff_C_mul, p, taylor_cube, totalCoeff, Int.cast_sum, Int.cast_mul]
  have high : (taylor 1 F).coeff m ≠ 0 := by rw [hc]; exact_mod_cast top
  have nt : taylor 1 F ≠ 0 := fun he => high (by simp [he])
  have nf : F ≠ 0 := fun he => nt (by rw [he, map_zero])
  refine ⟨g, fun i => sparse _ _, nf, ?_⟩
  change F.rootMultiplicity 1 = m
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
  change (taylor 1 F).natTrailingDegree = m
  refine le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero high)
    (Polynomial.le_natTrailingDegree nt (fun d hd => ?_))
  rw [hc, low ⟨d,hd⟩]
  norm_num

theorem order_seven : Witness 2 7 := by
  apply certify ![![2,3],![1,4],![0,5]] ![![-1,1],![-1,1],![-1,1]]
    ![2250,-125,9] <;> decide

theorem order_twelve : Witness 3 12 := by
  apply certify ![![0,11,13],![1,8,15],![3,5,16]] ![![2,-13,11],![1,-2,1],![11,-13,2]]
    ![117649,-5848414,117649] <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem order_seventeen : Witness 4 17 := by
  apply certify ![![3,4,21,22],![1,7,18,24],![0,10,15,25]]
    ![![-17,19,-19,17],![-11,23,-23,11],![-1,5,-5,1]]
    ![143770214843750,-3014208984375,446497421087421] <;> decide

end GctFrontier.SparseCubeWitnesses

open GctFrontier.SparseCubeWitnesses in
theorem PEqualNP.Research.SparseCubeWitnesses : Witness 2 7 ∧ Witness 3 12 ∧ Witness 4 17 :=
  ⟨order_seven, order_twelve, order_seventeen⟩
