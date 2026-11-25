import PEqualNP.Gct.Helpers.GrenetMatrix
import PEqualNP.Gct.L002
import PEqualNP.Gct.Helpers.BorderSubst
import Mathlib

/-! Pruning the subset program gives exact size-977 affine determinants on
three-entry restrictions and a degree-231 lower bound on equations separating
the ten-row permanent from size-1,001 affine determinants. -/

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
private theorem compressed {σ : Type} {m N : ℕ}
    (A : Matrix (Finset (Fin m)) (Finset (Fin m)) (MvPolynomial σ ℂ))
    (v : Finset (Fin m) → MvPolynomial σ ℂ)
    (hstep : ∀ {S T : Finset (Fin m)}, T.card ≤ S.card → A S T = 0)
    (hdeg : ∀ S T, ((1-A) S T).totalDegree ≤ 1)
    (hvec : Matrix.vecMul v (1-A) = Pi.single ∅ 1)
    (keep : Finset (Fin m) → Prop) [DecidablePred keep] (hempty : keep ∅)
    (hfull : keep Finset.univ) (hzero : ∀ S, ¬keep S → v S = 0)
    (hN : 0 < N) (hcard : Fintype.card {S // keep S} = N+1) :
    HasDetExpression (v Finset.univ) N := by
  classical
  let M : Matrix {S // keep S} {S // keep S} (MvPolynomial σ ℂ) :=
    (1 - A).submatrix Subtype.val Subtype.val
  let layer (S : {S // keep S}) := S.val.card
  have htri : M.BlockTriangular layer := by
    intro U V h
    have hlt : V.val.card < U.val.card := h
    have hne : U.val ≠ V.val := fun h => by simp [h] at hlt
    simp [M, Matrix.submatrix_apply, hne, hstep hlt.le]
  have hdet : M.det = 1 := by
    rw [htri.det]
    refine Finset.prod_eq_one fun a _ => ?_
    have he : M.toSquareBlock layer a = 1 := by
      ext ⟨U, hU⟩ ⟨V, hV⟩
      have hle : V.val.card ≤ U.val.card := by change layer V ≤ layer U; rw [hU,hV]
      by_cases huv : U = V
      · subst V
        simp [M, Matrix.toSquareBlock_def, Matrix.submatrix_apply, Matrix.one_apply,
          hstep hle]
      · have hval : U.val ≠ V.val := fun h => huv (Subtype.ext h)
        simp [M, Matrix.toSquareBlock_def, Matrix.submatrix_apply, Matrix.one_apply, huv, hval,
          hstep hle]
    rw [he, Matrix.det_one]
  let source : {S // keep S} := ⟨∅,hempty⟩
  let sink : {S // keep S} := ⟨Finset.univ,hfull⟩
  have hv : Matrix.vecMul (fun S : {S // keep S} => v S.val) M = Pi.single source 1 := by
    funext T
    let term (S : Finset (Fin m)) := v S * (1 - A) S T.val
    have hsplit := Fintype.sum_subtype_add_sum_subtype keep term
    have homit : ∑ S : {S // ¬keep S}, term S.val = 0 := by
      apply Finset.sum_eq_zero
      intro S _
      simp [term, hzero S.val S.property]
    rw [homit, add_zero] at hsplit
    calc
      _ = Matrix.vecMul v (1 - A) T.val := hsplit
      _ = _ := by
        rw [hvec]
        by_cases ht : T = source
        · subst T
          simp [source]
        · have hne : T.val ≠ ∅ := fun he => ht (Subtype.ext he)
          simp [hne, ht]
  have ha := congrArg (fun v => Matrix.vecMul v M.adjugate) hv
  simp only [Matrix.vecMul_vecMul, Matrix.mul_adjugate, hdet, one_smul,
    Matrix.vecMul_one, Matrix.single_one_vecMul] at ha
  have htarget : v Finset.univ = M.adjugate source sink := congrFun ha sink
  rw [htarget]
  apply hasDetExpression_adjugate hN hcard M _ source sink
  exact fun U V => hdeg U.val V.val

private theorem step_degree {σ : Type} {m : ℕ} (w : ℕ → Fin m → MvPolynomial σ ℂ)
    (hw : ∀ k j, (w k j).totalDegree ≤ 1) (U V : Finset (Fin m)) :
    ((1 - stepMatrix w) U V).totalDegree ≤ 1 := by
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
  refine compressed (stepMatrix w) (pathVec w) (stepMatrix_eq_zero w) (step_degree w hw)
    (pathVec_vecMul w) keepTen (by simp [keepTen]) (by simp [keepTen]) ?_ (by decide) count_kept
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

section Central

private abbrev State := Finset (Fin 10)
private abbrev CoeffRing := MvPolynomial (Fin 10 × Fin 10) ℂ
private noncomputable abbrev w := permWeight ℂ 10

def centralStates : Finset (Finset (Fin 10)) := Finset.univ.powersetCard 5

/-- Each path receives the scalar of its unique five-element state. -/
noncomputable def markedPath (z : State → ℂ) : ℕ → State → CoeffRing
  | 0, _ => 1
  | k+1, T => (if k+1 = 5 then C (z T) else 1) *
      ∑ j ∈ T, markedPath z k (T.erase j) * w k j

noncomputable def centralOutput (z : State → ℂ) : CoeffRing := markedPath z 10 Finset.univ

private theorem before_cut (z : State → ℂ) (k : ℕ) (hk : k < 5) (T : State) :
    markedPath z k T = pathSum w k T := by
  induction k generalizing T with
  | zero => rfl
  | succ k ih =>
    simp only [markedPath, ite_eq_right (show k+1 ≠ 5 by omega), one_mul, pathSum_succ]
    exact Finset.sum_congr rfl (fun j _ => by rw [ih (by omega)])

private theorem at_cut (z : State → ℂ) (T : State) :
    markedPath z 5 T = C (z T) * pathSum w 5 T := by
  change C (z T) * (∑ j ∈ T, markedPath z 4 (T.erase j) * w 4 j) = _
  rw [pathSum_succ]
  simp only [before_cut z 4 (by decide)]

theorem central_ones : centralOutput (fun _ => 1) = permPoly ℂ 10 := by
  have he (k : ℕ) (T : State) : markedPath (fun _ => 1) k T = pathSum w k T := by
    induction k generalizing T with
    | zero => rfl
    | succ k ih => simp [markedPath, pathSum_succ, ih]
  simpa [centralOutput,he,pathVec] using pathVec_permWeight_univ ℂ 10

private theorem after_cut (z : State → ℂ) (t : ℕ) (T : State) :
    markedPath z (5+(t+1)) T =
      ∑ j ∈ T, markedPath z (5+t) (T.erase j) * w (5+t) j := by
  change (if 5+t+1=5 then C (z T) else 1) * _ = _
  rw [ite_eq_right (show 5+t+1 ≠ 5 by omega), one_mul]
  rfl

set_option maxHeartbeats 1200000 in
/-- The polynomial output depends linearly on all central scalars jointly. -/
theorem central_expansion (z : State → ℂ) :
    centralOutput z = ∑ S ∈ centralStates, C (z S) * centralOutput (Pi.single S 1) := by
  classical
  have he (t : ℕ) (T : State) (hc : T.card = 5+t) :
      markedPath z (5+t) T =
        ∑ S ∈ centralStates, C (z S) * markedPath (Pi.single S 1) (5+t) T := by
    induction t generalizing T with
    | zero =>
      have hm : T ∈ centralStates := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,by omega⟩
      simp only [Nat.add_zero, at_cut]
      rw [Finset.sum_eq_single T]
      · simp
      · intro S _ hs
        simp [hs.symm]
      · simp [hm]
    | succ t ih =>
      simp only [after_cut, Finset.mul_sum]
      calc
        _ = ∑ j ∈ T, ∑ S ∈ centralStates,
              C (z S) * (markedPath (Pi.single S 1) (5+t) (T.erase j) * w (5+t) j) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hjc := Finset.card_erase_add_one hj
            rw [ih (T.erase j) (by omega), Finset.sum_mul]
            exact Finset.sum_congr rfl (fun _ _ => mul_assoc ..)
        _ = _ := Finset.sum_comm
  exact he 5 Finset.univ (by decide)

/-- At most 230 nonzero central scalars give a single exact size-1001 affine pencil. -/
theorem central_sparse_expression (z : State → ℂ)
    (hs : (centralStates.filter (fun S => z S ≠ 0)).card ≤ 230) :
    HasDetExpression (centralOutput z) 1001 := by
  classical
  let v (T : State) := markedPath z T.card T
  let g (T : State) : CoeffRing := if T.card = 5 then C (z T) else 1
  let A : Matrix State State CoeffRing := fun S T => stepMatrix w S T * g T
  have hstep {S T : State} (h : T.card ≤ S.card) : A S T = 0 := by simp [A,stepMatrix_eq_zero w h]
  have hdeg (S T : State) : ((1-A) S T).totalDegree ≤ 1 := by
    rw [Matrix.sub_apply]
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · rw [Matrix.one_apply]; split_ifs <;> simp
    · have hw : ((stepMatrix w) S T).totalDegree ≤ 1 := by
        apply totalDegree_finsetSum_le
        intro j _
        split_ifs
        · exact totalDegree_permWeight_le ℂ 10 _ _
        · simp
      exact (totalDegree_mul _ _).trans (by dsimp [g]; split_ifs <;> simpa using hw)
  have hvec : Matrix.vecMul v (1-A) = Pi.single ∅ 1 := by
    funext T
    rw [Matrix.vecMul_sub, Matrix.vecMul_one, Pi.sub_apply]
    have hv : Matrix.vecMul v A T = g T * ∑ j ∈ T, v (T.erase j) * w (T.erase j).card j := by
      simp only [Matrix.vecMul, dotProduct, A, ← mul_assoc, ← Finset.sum_mul]
      rw [mul_comm _ (g T)]
      congr 1
      simp only [stepMatrix, Finset.mul_sum, mul_ite, mul_zero]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun j _ => by rw [Finset.sum_ite_eq' Finset.univ]; simp)
    rw [hv]
    by_cases ht : T = ∅
    · subst T; simp [v,markedPath]
    · obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (fun h => ht (Finset.card_eq_zero.mp h))
      simp only [Pi.single_apply, ite_eq_right ht, sub_eq_zero]
      change markedPath z T.card T = _
      rw [hk, markedPath]
      dsimp [g]
      rw [hk]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have he : (T.erase j).card = k := by have := Finset.card_erase_add_one hj; omega
      simp [v,he]
  let other := (Finset.univ : Finset State) \ centralStates
  let active := centralStates.filter (fun S => z S ≠ 0)
  let kept := other ∪ active
  have ho : other.card = 772 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [centralStates, Finset.card_powersetCard, Fintype.card_finset]
    decide
  have hd : Disjoint other active := by
    apply Finset.disjoint_left.mpr
    intro S hS ha
    exact (Finset.mem_sdiff.mp hS).2 (Finset.mem_filter.mp ha).1
  have hkc : kept.card = 772 + active.card := by
    exact (Finset.card_union_of_disjoint hd).trans (by rw [ho])
  have hlow : 0 < kept.card - 1 := by omega
  have hhi : kept.card-1 ≤ 1001 := by change active.card ≤ 230 at hs; omega
  have hk (S : State) : S ∈ kept ↔ S.card ≠ 5 ∨ z S ≠ 0 := by
    simp only [kept,other,active,centralStates,Finset.mem_union,Finset.mem_sdiff,
      Finset.mem_univ, Finset.mem_filter,Finset.mem_powersetCard,Finset.subset_univ,true_and]
    by_cases h : S.card = 5 <;> simp [h]
  have hp : HasDetExpression (v Finset.univ) (kept.card-1) :=
    compressed A v hstep hdeg hvec (fun S => S ∈ kept)
      ((hk _).mpr (Or.inl (by simp))) ((hk _).mpr (Or.inl (by simp))) (by
        intro S hn
        obtain ⟨hc,hz⟩ : S.card = 5 ∧ z S = 0 := by simpa [hk,not_or] using hn
        simp [v,hc,at_cut,hz]) hlow (by simp only [Fintype.card_coe]; omega)
  change HasDetExpression (v Finset.univ) 1001
  have pad {d e : ℕ} (p : CoeffRing) (h : HasDetExpression p d) (hle : d ≤ e) :
      HasDetExpression p e := by
    induction hle with
    | refl => exact h
    | step _ ih => exact L002 _ ℂ _ _ ih
  exact pad _ hp hhi

end Central

section Sparse

variable {α : Type*} [DecidableEq α]

/-- Vanishing on every coordinate subspace of dimension r excludes every
    monomial involving at most r distinct variables, including arbitrary powers. -/
theorem coeff_zero_of_sparse_vanishing (p : MvPolynomial α ℂ) (r : ℕ)
    (h : ∀ (S : Finset α), S.card ≤ r → ∀ x : α → ℂ,
      (∀ i ∉ S, x i = 0) → eval x p = 0)
    (s : α →₀ ℕ) (hs : s.support.card ≤ r) : p.coeff s = 0 := by
  classical
  let S := s.support
  let f : ↥S → α := Subtype.val
  have hf : Function.Injective f := Subtype.val_injective
  have hm : (↑s.support : Set α) ⊆ Set.range f := fun i hi => ⟨⟨i,hi⟩,rfl⟩
  have hkill : killCompl (R := ℂ) hf p = 0 := by
    apply MvPolynomial.funext
    intro y
    let x : α → ℂ := fun i => if hi : i ∈ S then y ⟨i,hi⟩ else 0
    have he : (aeval y).comp (killCompl (R := ℂ) hf) = aeval x := by
      apply algHom_ext
      intro i
      by_cases hi : i ∈ S
      · let j : ↥S := ⟨i,hi⟩
        have hj : X i = rename f (X j : MvPolynomial ↥S ℂ) := by simp [f,j]
        rw [AlgHom.comp_apply, hj, killCompl_rename_app, aeval_X, rename_X, aeval_X]
        simp [x,f,j,hi]
      · have hn : i ∉ Set.range f := by
          rintro ⟨j,rfl⟩
          exact hi j.property
        rw [AlgHom.comp_apply, killCompl, aeval_X, dite_eq_right hn, map_zero, aeval_X]
        simp [x,hi]
    have hz := congrArg (fun g : MvPolynomial α ℂ →ₐ[ℂ] ℂ => g p) he
    change eval y (killCompl hf p) = eval x p at hz
    rw [hz, h S hs x (fun i hi => by simp [x,hi]), map_zero]
  have hc := congrArg (fun q : MvPolynomial ↥S ℂ => q.coeff (s.comapDomain f hf.injOn)) hkill
  simpa [coeff_killCompl, s.mapDomain_comapDomain f hf hm] using hc

theorem sparse_degree_barrier (p : MvPolynomial α ℂ) (r : ℕ)
    (h : ∀ (S : Finset α), S.card ≤ r → ∀ x : α → ℂ,
      (∀ i ∉ S, x i = 0) → eval x p = 0) (hne : p ≠ 0) : r < p.totalDegree := by
  classical
  obtain ⟨s,hs⟩ := Finset.nonempty_of_ne_empty (show p.support ≠ ∅ by simpa using hne)
  have hc := mem_support_iff.mp hs
  have hcount : r < s.support.card := by
    by_contra! hle
    exact hc (coeff_zero_of_sparse_vanishing p r h s hle)
  have hdegree : s.support.card ≤ s.degree := by
    rw [Finsupp.degree_apply]
    simpa using (Finset.sum_le_sum (s := s.support) (f := fun _ => 1)
      (g := fun i => s i) (fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)))
  exact hcount.trans_le (hdegree.trans (le_totalDegree hs))

theorem central_budget :
    Nat.choose 10 5 = 252 ∧ 2^10-1-Nat.choose 10 5+230 = 1001 := by decide

/-- Any polynomial equation on linear observations of the output (including
    coefficients of several restrictions) separating the ten-row permanent from
    all size-1001 affine determinants must have degree at least 231. -/
theorem separator_degree_231 {I : Type} (obs : I → CoeffRing →ₗ[ℂ] ℂ)
    (Φ : MvPolynomial I ℂ)
    (hvan : ∀ p : CoeffRing, HasDetExpression p 1001 → eval (fun i => obs i p) Φ = 0)
    (hsep : eval (fun i => obs i (permPoly ℂ 10)) Φ ≠ 0) : 231 ≤ Φ.totalDegree := by
  classical
  let lin (i : I) : MvPolynomial State ℂ :=
    ∑ S ∈ centralStates, C (obs i (centralOutput (Pi.single S 1))) * X S
  let q := bind₁ lin Φ
  have hl (i : I) : (lin i).totalDegree ≤ 1 := by
    apply totalDegree_finsetSum_le
    intro S _
    exact (totalDegree_mul _ _).trans (by simp)
  have he (z : State → ℂ) : eval z q = eval (fun i => obs i (centralOutput z)) Φ := by
    change eval₂Hom (RingHom.id ℂ) z (bind₁ lin Φ) = _
    rw [eval₂Hom_bind₁]
    congr 2
    funext i
    change eval z (lin i) = obs i (centralOutput z)
    rw [central_expansion z]
    simp only [lin, map_sum, map_mul, eval_C, eval_X]
    apply Finset.sum_congr rfl
    intro S _
    rw [← smul_eq_C_mul, map_smul]
    exact mul_comm _ _
  have hn : q ≠ 0 := by
    intro hq
    have h := he (fun _ => 1)
    rw [hq, map_zero, central_ones] at h
    exact hsep h.symm
  have hsmall (S : Finset State) (hs : S.card ≤ 230) (z : State → ℂ)
      (hz : ∀ i ∉ S, z i = 0) : eval z q = 0 := by
    rw [he]
    apply hvan _ (central_sparse_expression z ?_)
    apply (Finset.card_le_card ?_).trans hs
    intro T hT
    by_contra ht
    exact (Finset.mem_filter.mp hT).2 (hz T ht)
  exact (sparse_degree_barrier q 230 hsmall hn).trans_le
    (Helpers.totalDegree_bind₁_le_of_affine lin hl Φ)

end Sparse

end GctFrontier.PrunedPermanent
