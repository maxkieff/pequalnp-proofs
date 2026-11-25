import PEqualNP.Gct.Helpers.Extension.Gradient
import PEqualNP.Gct.Helpers.FermatFromKneser

/-! Differential equations for a linear space on a level set of the four-by-four permanent.
The support test in project discussion 9114 is due to PeaBrane. -/

/-! Integer certificates use row-major cell indices. Index 16 is the gradient border.
The second matrix is 8090940 times the inverse of the first. -/

namespace GctFrontier.HallData

open Matrix Finset

private def borderRows : Array (Array ℤ) := #[
  #[0, 0, 0, 0, 0, 5, 3, 3, 0, 3, 5, 3, 0, 3, 3, 5, 16],
  #[0, 0, 0, 0, 5, 0, 3, 3, 3, 0, 3, 2, 3, 0, 2, 3, 11],
  #[0, 0, 0, 0, 3, 3, 0, 2, 5, 3, 0, 3, 3, 2, 0, 3, 11],
  #[0, 0, 0, 0, 3, 3, 2, 0, 3, 2, 3, 0, 5, 3, 3, 0, 11],
  #[0, 5, 3, 3, 0, 0, 0, 0, 0, 3, 3, 2, 0, 3, 2, 3, 11],
  #[5, 0, 3, 3, 0, 0, 0, 0, 3, 0, 5, 3, 3, 0, 3, 5, 16],
  #[3, 3, 0, 2, 0, 0, 0, 0, 3, 5, 0, 3, 2, 3, 0, 3, 11],
  #[3, 3, 2, 0, 0, 0, 0, 0, 2, 3, 3, 0, 3, 5, 3, 0, 11],
  #[0, 3, 5, 3, 0, 3, 3, 2, 0, 0, 0, 0, 0, 2, 3, 3, 11],
  #[3, 0, 3, 2, 3, 0, 5, 3, 0, 0, 0, 0, 2, 0, 3, 3, 11],
  #[5, 3, 0, 3, 3, 5, 0, 3, 0, 0, 0, 0, 3, 3, 0, 5, 16],
  #[3, 2, 3, 0, 2, 3, 3, 0, 0, 0, 0, 0, 3, 3, 5, 0, 11],
  #[0, 3, 3, 5, 0, 3, 2, 3, 0, 2, 3, 3, 0, 0, 0, 0, 11],
  #[3, 0, 2, 3, 3, 0, 3, 5, 2, 0, 3, 3, 0, 0, 0, 0, 11],
  #[3, 2, 0, 3, 2, 3, 0, 3, 3, 3, 0, 5, 0, 0, 0, 0, 11],
  #[5, 3, 3, 0, 3, 5, 3, 0, 3, 3, 5, 0, 0, 0, 0, 0, 16],
  #[16, 11, 11, 11, 11, 16, 11, 11, 11, 11, 16, 11, 11, 11, 11, 16, 0]]

private def inverseRows : Array (Array ℤ) := #[
  #[15708, -375386, -375386, -375386, -375386, 213048, 216634, 216634, -375386, 216634, 213048, 216634, -375386, 216634, 216634, 213048, 62238],
  #[-375386, 2573507, -1289573, -1289573, -1104193, -375386, 917047, 917047, 917047, -1289573, 216634, 241307, 917047, -1289573, 241307, 216634, 31119],
  #[-375386, -1289573, 2573507, -1289573, 917047, 216634, -1289573, 241307, -1104193, 917047, -375386, 917047, 917047, 241307, -1289573, 216634, 31119],
  #[-375386, -1289573, -1289573, 2573507, 917047, 216634, 241307, -1289573, 917047, 241307, 216634, -1289573, -1104193, 917047, 917047, -375386, 31119],
  #[-375386, -1104193, 917047, 917047, 2573507, -375386, -1289573, -1289573, -1289573, 917047, 216634, 241307, -1289573, 917047, 241307, 216634, 31119],
  #[213048, -375386, 216634, 216634, -375386, 15708, -375386, -375386, 216634, -375386, 213048, 216634, 216634, -375386, 216634, 213048, 62238],
  #[216634, 917047, -1289573, 241307, -1289573, -375386, 2573507, -1289573, 917047, -1104193, -375386, 917047, 241307, 917047, -1289573, 216634, 31119],
  #[216634, 917047, 241307, -1289573, -1289573, -375386, -1289573, 2573507, 241307, 917047, 216634, -1289573, 917047, -1104193, 917047, -375386, 31119],
  #[-375386, 917047, -1104193, 917047, -1289573, 216634, 917047, 241307, 2573507, -1289573, -375386, -1289573, -1289573, 241307, 917047, 216634, 31119],
  #[216634, -1289573, 917047, 241307, 917047, -375386, -1104193, 917047, -1289573, 2573507, -375386, -1289573, 241307, -1289573, 917047, 216634, 31119],
  #[213048, 216634, -375386, 216634, 216634, 213048, -375386, 216634, -375386, -375386, 15708, -375386, 216634, 216634, -375386, 213048, 62238],
  #[216634, 241307, 917047, -1289573, 241307, 216634, 917047, -1289573, -1289573, -1289573, -375386, 2573507, 917047, 917047, -1104193, -375386, 31119],
  #[-375386, 917047, 917047, -1104193, -1289573, 216634, 241307, 917047, -1289573, 241307, 216634, 917047, 2573507, -1289573, -1289573, -375386, 31119],
  #[216634, -1289573, 241307, 917047, 917047, -375386, 917047, -1104193, 241307, -1289573, 216634, 917047, -1289573, 2573507, -1289573, -375386, 31119],
  #[216634, 241307, -1289573, 917047, 241307, 216634, -1289573, 917047, 917047, 917047, -375386, -1104193, -1289573, -1289573, 2573507, -375386, 31119],
  #[213048, 216634, 216634, -375386, 216634, 213048, 216634, -375386, 216634, 216634, 213048, -375386, -375386, -375386, -375386, 15708, 62238],
  #[62238, 31119, 31119, 31119, 31119, 62238, 31119, 31119, 31119, 31119, 62238, 31119, 31119, 31119, 31119, 62238, -93357]]


def border (i j : Fin 17) : ℤ := (borderRows.getD i.val #[]).getD j.val 0
def invScaled (i j : Fin 17) : ℤ := (inverseRows.getD i.val #[]).getD j.val 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem inverse_check : ∀ i j : Fin 17,
    (∑ k, invScaled i k * border k j) = if i = j then 8090940 else 0 := by decide

private def three (m : Matrix (Fin 4) (Fin 4) ℤ) (a b c : Fin 4) : ℤ :=
  m 1 a * m 2 b * m 3 c - m 1 a * m 2 c * m 3 b -
  m 1 b * m 2 a * m 3 c + m 1 b * m 2 c * m 3 a +
  m 1 c * m 2 a * m 3 b - m 1 c * m 2 b * m 3 a

def four (m : Matrix (Fin 4) (Fin 4) ℤ) : ℤ :=
  m 0 0 * three m 1 2 3 - m 0 1 * three m 0 2 3 +
  m 0 2 * three m 0 1 3 - m 0 3 * three m 0 1 2

theorem det_eq_four (m : Matrix (Fin 4) (Fin 4) ℤ) : m.det = four m := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply]
  norm_num [four, three, Fin.succAbove]
  ring

def principalMatrix (f : Fin 4 → Fin 16) : Matrix (Fin 4) (Fin 4) ℤ :=
  fun i j => invScaled (f i).castSucc (f j).castSucc

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
theorem four_check : ∀ a b c d : Fin 16, a < b → b < c → c < d →
    four (principalMatrix ![a,b,c,d]) ≠ 0 := by
  intro a
  fin_cases a <;> decide

end GctFrontier.HallData

namespace GctFrontier.HallSupport

open Finset PEqualNP.Gct.Extension
abbrev Cell := Fin 4 × Fin 4
abbrev Vec := Cell → ℂ
abbrev Slot := Option Cell
def aZ (p : Cell) : ℤ := if p.1 = p.2 then 2 else 1
def base (p : Cell) : ℂ := (aZ p : ℂ)
def Level (L : Submodule ℂ Vec) : Prop :=
  ∀ x ∈ L, MvPolynomial.eval (fun p => base p + x p) (PEqualNP.Gct.permPoly ℂ 4) = 65

def gradZ (p : Cell) : ℤ :=
  ∑ σ : Equiv.Perm (Fin 4), if σ p.2 = p.1 then ∏ k ∈ univ.erase p.2, aZ (σ k, k) else 0

def hessZ (p q : Cell) : ℤ :=
  ∑ σ : Equiv.Perm (Fin 4), if σ p.2 = p.1 then
    if σ q.2 = q.1 then if q.2 ∈ univ.erase p.2 then
      ∏ k ∈ (univ.erase p.2).erase q.2, aZ (σ k, k) else 0 else 0 else 0

private theorem first_at (L : Submodule ℂ Vec) (h : Level L) {x u : Vec} (hx : x ∈ L)
    (hu : u ∈ L) : D (fun p => base p + x p) u = 0 := by
  apply D_eq_zero _ _ 65
  intro s
  have he := h _ (L.add_mem hx (L.smul_mem s hu))
  rw [eval_perm] at he
  simpa [add_assoc] using he

private theorem grad_zero (L : Submodule ℂ Vec) (h : Level L) {u : Vec} (hu : u ∈ L) :
    (∑ p, (gradZ p : ℂ) * u p) = 0 := by
  have hd := first_at L h L.zero_mem hu
  simp only [Pi.zero_apply, add_zero, D] at hd
  rw [← hd]
  simp only [gradZ, Int.cast_sum, Int.cast_ite, Int.cast_prod, Int.cast_zero, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro σ _
  rw [Fintype.sum_prod_type_right]
  simp [base, mul_comm]

private theorem second_at (L : Submodule ℂ Vec) (h : Level L) {u v : Vec}
    (hu : u ∈ L) (hv : v ∈ L) :
    (∑ σ : Equiv.Perm (Fin 4), ∑ i, ∑ j ∈ univ.erase i,
      u (σ i,i) * v (σ j,j) * ∏ k ∈ (univ.erase i).erase j, base (σ k,k)) = 0 := by
  let f : Polynomial ℂ := ∑ σ : Equiv.Perm (Fin 4), ∑ i,
    Polynomial.C (u (σ i,i)) * ∏ j ∈ univ.erase i,
      (Polynomial.C (base (σ j,j)) + Polynomial.X * Polynomial.C (v (σ j,j)))
  have hf : f = 0 := by
    apply Polynomial.funext
    intro t
    rw [Polynomial.eval_zero]
    simp only [f, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_prod,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
    simpa only [D, Pi.smul_apply, smul_eq_mul] using
      first_at L h (x := t • v) (u := u) (L.smul_mem t hv) hu
  have hd : (Polynomial.derivative f).eval 0 = 0 := by simp [hf]
  rw [← hd]
  simp only [f, Polynomial.derivative_sum, Polynomial.derivative_mul,
    Polynomial.derivative_C, Polynomial.derivative_prod_finset, Polynomial.derivative_add,
    Polynomial.derivative_X, Polynomial.eval_finsetSum, Polynomial.eval_prod,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    zero_mul, zero_add, add_zero, one_mul, Finset.mul_sum, mul_assoc, mul_comm]

private theorem sum_omit (i : Fin 4) (f : Fin 4 → ℂ) :
    (∑ j, if j = i then 0 else f j) = ∑ j ∈ univ.erase i, f j := by
  have he : univ.erase i = univ.filter (· ≠ i) := by ext; simp
  rw [he, sum_filter]
  apply sum_congr rfl
  intro j _
  by_cases h : j = i <;> simp [h]

private theorem hess_zero (L : Submodule ℂ Vec) (h : Level L) {u v : Vec}
    (hu : u ∈ L) (hv : v ∈ L) : (∑ p, ∑ q, (hessZ p q : ℂ) * u p * v q) = 0 := by
  rw [← second_at L h hu hv]
  simp only [hessZ, Int.cast_sum, Int.cast_ite, Int.cast_prod, Int.cast_zero, sum_mul]
  conv_lhs => enter [2,p]; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro σ _
  rw [Fintype.sum_prod_type_right]
  simp only [ite_mul, zero_mul, sum_ite_irrel, sum_const_zero, Fintype.sum_ite_eq]
  apply sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type_right]
  rw [← sum_omit]
  simp [base, mul_comm, mul_left_comm, mul_assoc]

open Matrix Module PEqualNP.Gct.Helpers
open GctFrontier.HallData

private def code : Slot ≃ Fin 17 :=
  (Equiv.optionCongr finProdFinEquiv).trans (finSuccEquiv' (Fin.last 16)).symm

private def loc (k : Fin 16) : Slot := some (finProdFinEquiv.symm k)
private theorem code_loc : ∀ k : Fin 16, code (loc k) = k.castSucc := by decide

private def B : Matrix Slot Slot ℂ
  | none, none => 0
  | none, some p | some p, none => (gradZ p : ℂ)
  | some p, some q => (hessZ p q : ℂ)

private def Cmat : Matrix Slot Slot ℂ :=
  fun i j => (invScaled (code i) (code j) : ℂ)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem entries :
    (∀ p : Cell, border (code none) (code (some p)) = gradZ p) ∧
    (∀ p : Cell, border (code (some p)) (code none) = gradZ p) ∧
    (∀ p q : Cell, border (code (some p)) (code (some q)) = hessZ p q) := by decide

private theorem B_entry (i j : Slot) : B i j = (border (code i) (code j) : ℂ) := by
  cases i with
  | none =>
    cases j with
    | none => have h : border (code none) (code none) = 0 := by decide
              simp [B,h]
    | some p => rw [entries.1]; rfl
  | some p =>
    cases j with
    | none => rw [entries.2.1]; rfl
    | some q => rw [entries.2.2]; rfl

private theorem CB : (Cmat : Matrix Slot Slot ℂ) * B = (8090940 : ℂ) • (1 : Matrix Slot Slot ℂ) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Cmat, B_entry, ← Int.cast_mul, ← Int.cast_sum]
  rw [code.sum_comp (fun k => invScaled (code i) k * border k (code j)), inverse_check]
  by_cases h : i = j <;> simp [h]

private def embed (L : Submodule ℂ Vec) : L × ℂ →ₗ[ℂ] (Slot → ℂ) where
  toFun z := fun s => match s with | none => z.2 | some p => z.1.val p
  map_add' _ _ := by funext s; cases s <;> rfl
  map_smul' _ _ := by funext s; cases s <;> rfl

private theorem embed_inj (L : Submodule ℂ Vec) : Function.Injective (embed L) := by
  intro a b h
  exact Prod.ext (Subtype.ext (funext fun p => congrFun h (some p))) (congrFun h none)

private theorem b_perp (L : Submodule ℂ Vec) (h : Level L) (u v : L × ℂ) :
    (∑ s, (B *ᵥ embed L u) s * embed L v s) = 0 := by
  rw [Fintype.sum_option]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_option, B, embed, LinearMap.coe_mk,
    AddHom.coe_mk, zero_mul, zero_add, add_mul, sum_add_distrib, grad_zero L h u.1.property]
  have hg := grad_zero L h v.1.property
  have hh := hess_zero L h v.1.property u.1.property
  calc
    _ = u.2 * (∑ p, (gradZ p : ℂ) * v.1.val p) +
          (∑ p, ∑ q, (hessZ p q : ℂ) * v.1.val p * u.1.val q) := by
      simp only [mul_sum, mul_left_comm, mul_comm, mul_assoc]
    _ = 0 := by rw [hg,hh]; ring

private def spike (f : Fin 4 → Fin 16) : Matrix Slot (Fin 4) ℂ :=
  fun s i => if loc (f i) = s then 1 else 0

private theorem c_spike (f : Fin 4 → Fin 16) (s : Slot) (i : Fin 4) :
    ((Cmat : Matrix Slot Slot ℂ) * spike f) s i = Cmat s (loc (f i)) := by
  simp [Matrix.mul_apply, spike, mul_ite]

private def small (f : Fin 4 → Fin 16) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => Cmat (loc (f i)) (loc (f j))

private theorem minor_nonsingular (f : Fin 4 → Fin 16) (hf : StrictMono f) :
    (principalMatrix f).det ≠ 0 := by
  have he : ![f 0, f 1, f 2, f 3] = f := by funext i; fin_cases i <;> rfl
  have h := four_check (f 0) (f 1) (f 2) (f 3) (hf (by decide)) (hf (by decide)) (hf (by decide))
  rw [he] at h
  rw [det_eq_four]
  exact h

private theorem small_det (f : Fin 4 → Fin 16) (hf : StrictMono f) : (small f).det ≠ 0 := by
  have e : small f = (principalMatrix f).map (fun x => (x : ℂ)) := by
    ext i j
    simp only [small, Cmat, code_loc, Matrix.map_apply, principalMatrix]
  rw [e, ← Int.cast_det]
  exact_mod_cast minor_nonsingular f hf

/-- Transport the augmented level space through the bordered Hessian, then
adjoin four independent coordinate covectors at the specified holes. -/
private def joined (L : Submodule ℂ Vec) (f : Fin 4 → Fin 16) :
    (L × ℂ) × (Fin 4 → ℂ) →ₗ[ℂ] (Slot → ℂ) :=
  (B.mulVecLin.comp (embed L)).coprod (spike f).mulVecLin

private theorem joined_inj (L : Submodule ℂ Vec) (f : Fin 4 → Fin 16) (hf : StrictMono f)
    (hz : ∀ i (x : L), x.val (finProdFinEquiv.symm (f i)) = 0) :
    Function.Injective (joined L f) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨v,z⟩ he
  change B *ᵥ embed L v + spike f *ᵥ z = 0 at he
  have hc := congrArg (fun w => (Cmat : Matrix Slot Slot ℂ) *ᵥ w) he
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, CB, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_zero] at hc
  have hs : (small f) *ᵥ z = 0 := by
    funext i
    have h0 : embed L v (loc (f i)) = 0 := hz i v.1
    have hi := congrFun hc (loc (f i))
    simpa only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, h0, mul_zero, zero_add,
      Matrix.mulVec, dotProduct, c_spike, small] using hi
  have zi : z = 0 := Matrix.mulVec_injective_of_det_ne_zero (small_det f hf)
    (hs.trans (Matrix.mulVec_zero _).symm)
  subst z
  rw [Matrix.mulVec_zero, add_zero] at hc
  have ev : embed L v = 0 := (smul_eq_zero.mp hc).resolve_left (by norm_num)
  exact Prod.ext (embed_inj L (ev.trans (map_zero _).symm)) rfl

/-- The two perpendicular spaces have respective dimensions dim L + 5 and
dim L + 1 in a 17-dimensional ambient space. -/
private theorem bound (L : Submodule ℂ Vec) (h : Level L) (f : Fin 4 → Fin 16)
    (hf : StrictMono f) (hz : ∀ i (x : L), x.val (finProdFinEquiv.symm (f i)) = 0) :
    finrank ℂ L ≤ 5 := by
  have upper := perp_bound (joined L f).range (embed L).range (by
    rintro _ ⟨⟨u,z⟩,rfl⟩ _ ⟨v,rfl⟩
    change (∑ s, ((B *ᵥ embed L u) s + (spike f *ᵥ z) s) * embed L v s) = _
    rw [show (∑ s, ((B *ᵥ embed L u) s + (spike f *ᵥ z) s) * embed L v s) =
      (∑ s, (B *ᵥ embed L u) s * embed L v s) + ∑ s, (spike f *ᵥ z) s * embed L v s by
        simp only [add_mul, sum_add_distrib], b_perp L h, zero_add]
    simp only [Matrix.mulVec, dotProduct, sum_mul]
    rw [sum_comm]
    apply sum_eq_zero
    intro i _
    have h0 : embed L v (loc (f i)) = 0 := hz i v.1
    simp [spike, ite_mul, h0])
  rw [LinearMap.finrank_range_of_inj (joined_inj L f hf hz),
      LinearMap.finrank_range_of_inj (embed_inj L)] at upper
  simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] at upper
  have card : Fintype.card Slot = 17 := by decide
  omega

/-- At most three coordinate functions vanish on all of L. -/
theorem missing_bound (L : Submodule ℂ Vec) (h : Level L) (hd : 6 ≤ finrank ℂ L)
    (S : Finset Cell) (hz : ∀ p ∈ S, ∀ x ∈ L, x p = 0) : S.card ≤ 3 := by
  by_contra! large
  let ix : Cell ≃ Fin 16 := finProdFinEquiv
  have hc : 4 ≤ (S.map ix.toEmbedding).card := by rw [Finset.card_map]; omega
  obtain ⟨T, hT, h4⟩ := Finset.le_card_iff_exists_subset_card.mp hc
  let f := T.orderEmbOfFin h4
  have hsmall := bound L h f f.strictMono (by
    intro i x
    obtain ⟨p,hp,he⟩ := Finset.mem_map.mp (hT (T.orderEmbOfFin_mem h4 i))
    change ix p = f i at he
    change x.val (ix.symm (f i)) = 0
    rw [← he, Equiv.symm_apply_apply]
    exact hz p hp x x.property)
  omega

private theorem match_count : ∀ p : Cell,
    (univ.filter (fun σ : Equiv.Perm (Fin 4) => σ p.1 = p.2)).card = 6 := by decide

/-- Each missing cell can destroy at most six of the 24 matchings. -/
theorem matching_bound (L : Submodule ℂ Vec) (h : Level L) (hd : 6 ≤ finrank ℂ L) :
    ∃ M : Finset (Equiv.Perm (Fin 4)), 6 ≤ M.card ∧
      ∀ σ ∈ M, ∀ i, ∃ x ∈ L, x (i,σ i) ≠ 0 := by
  classical
  let S := univ.filter (fun p : Cell => ∀ x ∈ L, x p = 0)
  let bad (p : Cell) := univ.filter (fun σ : Equiv.Perm (Fin 4) => σ p.1 = p.2)
  have hs := missing_bound L h hd S (fun _ hp => (mem_filter.mp hp).2)
  have hb := Finset.card_biUnion_le (s := S) (t := bad)
  have he : (∑ p ∈ S, (bad p).card) = S.card * 6 := by simp [bad,match_count]
  rw [he] at hb
  refine ⟨(S.biUnion bad)ᶜ, ?_, ?_⟩
  · rw [Finset.card_compl]
    have all : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by decide
    omega
  · intro σ hσ i
    by_contra! hm
    exact (Finset.mem_compl.mp hσ) (Finset.mem_biUnion.mpr
      ⟨(i,σ i), Finset.mem_filter.mpr ⟨mem_univ _,hm⟩, Finset.mem_filter.mpr ⟨mem_univ _,rfl⟩⟩)

end GctFrontier.HallSupport

open GctFrontier.HallSupport in
theorem PEqualNP.Research.HallSupport (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (lev : ∀ t ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      (if i = j then (2 : ℂ) else 1) + t (i,j)) = 65) (hd : 6 ≤ Module.finrank ℂ L) :
    (∀ S : Finset (Fin 4 × Fin 4), (∀ p ∈ S, ∀ x ∈ L, x p = 0) → S.card ≤ 3) ∧
    ∃ M : Finset (Equiv.Perm (Fin 4)), 6 ≤ M.card ∧
      ∀ σ ∈ M, ∀ i, ∃ x ∈ L, x (i,σ i) ≠ 0 := by
  have h : Level L := by
    intro x hx
    rw [PEqualNP.Gct.Extension.eval_perm]
    simpa only [Matrix.permanent, Matrix.of_apply, base, aZ, Int.cast_ite, Int.cast_ofNat,
      Int.cast_one] using lev x hx
  exact ⟨missing_bound L h hd, matching_bound L h hd⟩
