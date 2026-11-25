import Mathlib
import PEqualNP.Gct.Helpers.BorderMR

/-! Two-cut identities and a smooth-point border Hessian bound for the ten-row common-pencil problem. -/

set_option autoImplicit false

namespace GctFrontier.CommonPencil

open MvPolynomial Filter Topology

section Fold

variable {R ι : Type*} [CommRing R] [Fintype ι]

def contract (a : ι → R) (M : Matrix ι ι R) (b : ι → R) : R :=
  ∑ i, ∑ j, a i * M i j * b j

private theorem contract_smul_left (z : R) (a : ι → R) (M : Matrix ι ι R) (b : ι → R) :
    contract (z • a) M b = z * contract a M b := by
  simp [contract, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem contract_smul_right (z : R) (a : ι → R) (M : Matrix ι ι R) (b : ι → R) :
    contract a M (z • b) = z * contract a M b := by
  simp only [contract, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable [DecidableEq ι]

def foldedBlock (z : R) (K : Matrix ι ι R) : Matrix ι ι R := 1 - z • K

/-- After removing the unfused acyclic vertices, this is z times the folded cofactor. -/
def numerator (z d : R) (a b u v : ι → R) (K : Matrix ι ι R) : R :=
  z*d*(foldedBlock z K).det +
    contract (a + z • u) (foldedBlock z K).adjugate (b + z • v)

def leftRegular (z d : R) (b u v : ι → R) (K : Matrix ι ι R) : R :=
  d*(foldedBlock z K).det + contract u (foldedBlock z K).adjugate (b + z • v)

def rightRegular (z d : R) (a u v : ι → R) (K : Matrix ι ι R) : R :=
  d*(foldedBlock z K).det + contract (a + z • u) (foldedBlock z K).adjugate v

theorem left_factor (z d : R) (b u v : ι → R) (K : Matrix ι ι R) :
    numerator z d 0 b u v K = z * leftRegular z d b u v K := by
  simp only [numerator, leftRegular, zero_add, contract_smul_left]
  ring

theorem right_factor (z d : R) (a u v : ι → R) (K : Matrix ι ι R) :
    numerator z d a 0 u v K = z * rightRegular z d a u v K := by
  simp only [numerator, rightRegular, zero_add, contract_smul_right]
  ring

theorem special_fibres (d : R) (a b u v : ι → R) (K : Matrix ι ι R) :
    numerator 0 d a b u v K = contract a 1 b ∧
    leftRegular 0 d b u v K = d + contract u 1 b ∧
    rightRegular 0 d a u v K = d + contract a 1 v := by
  simp [numerator, leftRegular, rightRegular, foldedBlock]

/-- For the repeated column the selected middle transfer is zero. Exactly
    three powers of the parameter remain in the numerator. -/
theorem repeated_column_identity (z d : R) (a b u v : ι → R) :
    numerator z d a b u v 0 =
      contract a 1 b + z*(d + contract a 1 v + contract u 1 b) + z^2*contract u 1 v := by
  have hl (x y f : ι → R) : contract (x+y) 1 f = contract x 1 f + contract y 1 f := by
    simp [contract, add_mul, Finset.sum_add_distrib]
  have hr (x y f : ι → R) : contract x 1 (y+f) = contract x 1 y + contract x 1 f := by
    simp [contract, mul_add, Finset.sum_add_distrib]
  simp only [numerator,foldedBlock,smul_zero,sub_zero,Matrix.det_one,mul_one,Matrix.adjugate_one,
    hl,hr,contract_smul_left,contract_smul_right]
  ring

end Fold

private abbrev V := Fin 10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
theorem fold_counts :
    ((Finset.univ : Finset (Finset V)).filter (fun s => s.card = 3 ∧ (0:V) ∈ s)).card = 36 ∧
    ((Finset.univ : Finset (Finset V)).filter (fun s => s.card = 7 ∧ (0:V) ∉ s)).card = 36 ∧
    2^10 - 1 - 36 = (987 : ℕ) := by decide

/-- Every permutation of the three selected columns uses a forbidden entry when
    the corresponding three rows are zero in the distinguished column. -/
theorem zero_boundary {R : Type*} [CommRing R] (x : Matrix (Fin 3) V R) (c : V) (cols : Fin 3 → V)
    (hc : c ∈ Set.range cols) (hz : ∀ i, x i c = 0) :
    (Matrix.of (fun i j => x i (cols j))).permanent = 0 := by
  obtain ⟨j,hj⟩ := hc
  apply Finset.sum_eq_zero
  intro σ _
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj,hz])

open PEqualNP.Gct PEqualNP.Gct.Helpers PEqualNP.Gct.Helpers.BorderMR

/-- At a smooth zero with invertible Hessian the ordinary size bound also
    applies to arbitrary coefficientwise limits of affine pencils. -/
theorem smooth_hessian_border_bound {k n : ℕ} (p : MvPolynomial (Fin k) ℂ)
    (y : Fin k → ℂ) (hy : eval y p = 0) (i : Fin k) (hi : eval y (pderiv i p) ≠ 0)
    (hd : (hess p y).det ≠ 0) (h : HasBorderDetExpression p n) : k ≤ 2*n := by
  classical
  obtain ⟨q,hq,hlim⟩ := h
  have hf : {s : Fin k →₀ ℕ | s ≤ Finsupp.equivFunOnFinite.symm (fun _ => n)}.Finite :=
    Set.finite_Iic _
  have hqS (j : ℕ) (s : Fin k →₀ ℕ) (hs : s ∉ hf.toFinset) : (q j).coeff s = 0 := by
    by_contra hn
    apply hs
    rw [Set.Finite.mem_toFinset]
    have hdeg := (le_totalDegree (mem_support_iff.mpr hn)).trans (L003 _ ℂ (q j) n (hq j))
    intro a
    exact (Finsupp.le_degree a s).trans hdeg
  have hpS : ∀ s, s ∉ hf.toFinset → p.coeff s = 0 := fun s hs =>
    tendsto_nhds_unique (hlim s) (by simp [hqS _ s hs])
  obtain ⟨x,hx,hz⟩ := exists_roots _ q p hqS hpS hlim y hy i hi
  have hh : Tendsto (fun j => hess (q j) (x j)) atTop (𝓝 (hess p y)) := by
    refine tendsto_pi_nhds.mpr fun a => tendsto_pi_nhds.mpr fun b => ?_
    exact tendsto_eval_lin ((pderiv a).toLinearMap ∘ₗ (pderiv b).toLinearMap) _ q p
      hqS hpS hlim x y hx
  obtain ⟨j,hj,hjd⟩ := (hz.and (((continuous_id.matrix_det.tendsto _).comp hh).eventually_ne hd)).exists
  change (hess (q j) (x j)).det ≠ 0 at hjd
  have hr := rank_hess_detExpr_gen (q j) (x j) (hq j) hj
  rw [Matrix.rank_of_det_ne_zero hjd, Fintype.card_fin] at hr
  exact hr

end GctFrontier.CommonPencil
