import PEqualNP.Gct.Helpers.GrenetMatrix
import Mathlib

/-! Exact size-977 affine determinant representations for the three-entry
restrictions in the cubic-padding experiment. -/

namespace GctFrontier.PrunedPermanent

open MvPolynomial PEqualNP.Gct PEqualNP.Gct.Helpers.Grenet

private theorem path_zero {R : Type} [CommRing R] {m r : ℕ} (c : Fin m)
    (w : ℕ → Fin m → R) (hw : ∀ k < r, w k c = 0) :
    ∀ k (S : Finset (Fin m)), S.card = k → k ≤ r → c ∈ S → pathSum w k S = 0 := by
  intro k
  induction k with
  | zero =>
    intro S hS _ hc
    simp [Finset.card_eq_zero.mp hS] at hc
  | succ k ih =>
    intro S hS hk hc
    rw [pathSum_succ]
    apply Finset.sum_eq_zero
    intro j hj
    by_cases he : j = c
    · simp [he, hw k (by omega)]
    · rw [ih (S.erase j) (by rw [Finset.card_erase_of_mem hj, hS]; rfl) (by omega)
        (Finset.mem_erase.mpr ⟨Ne.symm he,hc⟩), zero_mul]

/-- Restricting the subset matrix to any family of states with zero omitted
    path sums preserves the source-to-sink adjugate entry. -/
private theorem compressed {σ : Type} {m N : ℕ} (w : ℕ → Fin m → MvPolynomial σ ℂ)
    (hw : ∀ k j, (w k j).totalDegree ≤ 1)
    (keep : Finset (Fin m) → Prop) [DecidablePred keep] (hempty : keep ∅)
    (hfull : keep Finset.univ) (hzero : ∀ S, ¬keep S → pathVec w S = 0)
    (hN : 0 < N) (hcard : Fintype.card {S // keep S} = N+1) :
    HasDetExpression (pathVec w Finset.univ) N := by
  classical
  let M : Matrix {S // keep S} {S // keep S} (MvPolynomial σ ℂ) :=
    (1 - stepMatrix w).submatrix Subtype.val Subtype.val
  let layer (S : {S // keep S}) := S.val.card
  have htri : M.BlockTriangular layer := by
    intro U V h
    have hlt : V.val.card < U.val.card := h
    have hne : U.val ≠ V.val := fun h => by simp [h] at hlt
    simp [M, Matrix.submatrix_apply, hne, stepMatrix_eq_zero w hlt.le]
  have hdet : M.det = 1 := by
    rw [htri.det]
    refine Finset.prod_eq_one fun a _ => ?_
    have he : M.toSquareBlock layer a = 1 := by
      ext ⟨U, hU⟩ ⟨V, hV⟩
      have hle : V.val.card ≤ U.val.card := by change layer V ≤ layer U; rw [hU,hV]
      by_cases huv : U = V
      · subst V
        simp [M, Matrix.toSquareBlock_def, Matrix.submatrix_apply, Matrix.one_apply,
          stepMatrix_eq_zero w hle]
      · have hval : U.val ≠ V.val := fun h => huv (Subtype.ext h)
        simp [M, Matrix.toSquareBlock_def, Matrix.submatrix_apply, Matrix.one_apply, huv, hval,
          stepMatrix_eq_zero w hle]
    rw [he, Matrix.det_one]
  let source : {S // keep S} := ⟨∅,hempty⟩
  let sink : {S // keep S} := ⟨Finset.univ,hfull⟩
  have hv : Matrix.vecMul (fun S : {S // keep S} => pathVec w S.val) M = Pi.single source 1 := by
    funext T
    let term (S : Finset (Fin m)) := pathVec w S * (1 - stepMatrix w) S T.val
    have hsplit := Fintype.sum_subtype_add_sum_subtype keep term
    have homit : ∑ S : {S // ¬keep S}, term S.val = 0 := by
      apply Finset.sum_eq_zero
      intro S _
      simp [term, hzero S.val S.property]
    rw [homit, add_zero] at hsplit
    calc
      _ = Matrix.vecMul (pathVec w) (1 - stepMatrix w) T.val := hsplit
      _ = _ := by
        rw [pathVec_vecMul]
        by_cases ht : T = source
        · subst T
          simp [source]
        · have hne : T.val ≠ ∅ := fun he => ht (Subtype.ext he)
          simp [hne, ht]
  have ha := congrArg (fun v => Matrix.vecMul v M.adjugate) hv
  simp only [Matrix.vecMul_vecMul, Matrix.mul_adjugate, hdet, one_smul,
    Matrix.vecMul_one, Matrix.single_one_vecMul] at ha
  have htarget : pathVec w Finset.univ = M.adjugate source sink := congrFun ha sink
  rw [htarget]
  apply hasDetExpression_adjugate hN hcard M _ source sink
  intro U V
  change ((1 - stepMatrix w) U.val V.val).totalDegree ≤ 1
  rw [Matrix.sub_apply]
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · rw [Matrix.one_apply]
    split_ifs <;> simp
  · apply totalDegree_finsetSum_le
    intro j _
    split_ifs
    · exact hw _ _
    · simp

private abbrev keepTen (S : Finset (Fin 10)) := 0 ∉ S ∨ 3 < S.card

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem count_kept : Fintype.card {S : Finset (Fin 10) // keepTen S} = 978 := by
  decide

private theorem first_three_zero {σ : Type} (B : Matrix (Fin 10) (Fin 10) (MvPolynomial σ ℂ))
    (hB : ∀ i j, (B i j).totalDegree ≤ 1) (hz : ∀ i : Fin 10, i.val < 3 → B i 0 = 0) :
    HasDetExpression B.permanent 977 := by
  let w (k : ℕ) (j : Fin 10) := if hk : k < 10 then B ⟨k,hk⟩ j else 0
  have hw (k j) : (w k j).totalDegree ≤ 1 := by
    unfold w
    split_ifs
    · exact hB _ _
    · simp
  have he : pathVec w Finset.univ = B.permanent := by
    have h := pathSum_eq_permanent w 10 id Function.injective_id
    rw [Finset.image_id] at h
    have hBof : (Matrix.of fun i j => B i j) = B := Matrix.ext fun _ _ => rfl
    simpa [pathVec, w, hBof] using h
  rw [← he]
  refine compressed w hw keepTen (by simp [keepTen]) (by simp [keepTen]) ?_ (by decide) count_kept
  intro S hs
  have hbad : (0 : Fin 10) ∈ S ∧ S.card ≤ 3 := by simpa [keepTen] using hs
  apply path_zero 0 w (r := 3) ?_ S.card S rfl hbad.2 hbad.1
  intro k hk
  have h10 : k < 10 := by omega
  simpa [w, h10] using hz ⟨k,h10⟩ hk

/-- The rows and columns may be permuted independently. Thus any three
    specified zeros in one column admit this exact size-977 expression. -/
theorem three_zeros_one_column {σ : Type} (B : Matrix (Fin 10) (Fin 10) (MvPolynomial σ ℂ))
    (hB : ∀ i j, (B i j).totalDegree ≤ 1) (rows cols : Equiv.Perm (Fin 10))
    (hz : ∀ i : Fin 10, i.val < 3 → B (rows i) (cols 0) = 0) :
    HasDetExpression B.permanent 977 := by
  let T := (B.submatrix rows id).submatrix id cols
  have he : T.permanent = B.permanent :=
    (Matrix.permanent_permute_rows cols (B.submatrix rows id)).trans
      (Matrix.permanent_permute_cols rows B)
  rw [← he]
  exact first_three_zero T (fun i j => hB (rows i) (cols j)) hz

end GctFrontier.PrunedPermanent
