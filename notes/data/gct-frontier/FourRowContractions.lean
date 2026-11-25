import PEqualNP.Gct.Helpers.ColumnCore

/-! The quartic obstruction on row-centered subspaces of a four-row permanent level space. -/

namespace GctFrontier.FourRowContractions

noncomputable section

open Finset Module

section Sums

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def mass (a : ι → ℂ) : ℂ := ∑ i, a i

def pairSum (a b : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, if i = j then 0 else a i * b j

def tripleSum (a b c : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, if i = j ∨ i = k ∨ j = k then 0 else a i * b j * c k

def fourSum (a b c d : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, if i = j ∨ i = k ∨ i = l ∨ j = k ∨ j = l ∨ k = l
    then 0 else a i * b j * c k * d l

private theorem omit_coords (d : ι → ℂ) (s : Finset ι) :
    (∑ l, if l ∈ s then 0 else d l) = mass d - ∑ l ∈ s, d l := by
  apply eq_sub_of_add_eq
  have h : (∑ l, if l ∈ s then d l else 0) = ∑ l ∈ s, d l := by simp
  rw [← h, ← sum_add_distrib]
  apply sum_congr rfl
  intro l _
  by_cases hl : l ∈ s <;> simp [hl]

private theorem pair_rec (a b : ι → ℂ) :
    pairSum a b = mass a * mass b - mass (a*b) := by
  unfold pairSum
  rw [show mass a * mass b = ∑ i, a i * mass b from Finset.sum_mul _ _ _,
    show mass (a*b) = ∑ i, a i * b i from rfl,
    ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  have he : (∑ j, if i = j then 0 else a i * b j) =
      a i * (∑ j, if j ∈ ({i} : Finset ι) then 0 else b j) := by
    simp [mul_sum, mul_ite, eq_comm]
  rw [he, omit_coords]
  simp [mass, mul_sub]

private theorem triple_rec (a b c : ι → ℂ) :
    tripleSum a b c = mass c * pairSum a b - pairSum (a*c) b - pairSum a (b*c) := by
  unfold tripleSum pairSum
  simp only [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  by_cases hij : i = j
  · simp [hij]
  have he : (∑ k, if i = j ∨ i = k ∨ j = k then 0 else a i * b j * c k) =
      (a i * b j) * (∑ k, if k ∈ ({i,j} : Finset ι) then 0 else c k) := by
    simp [mul_sum, mul_ite, hij, eq_comm]
  rw [he, omit_coords]
  simp [hij]
  ring

private theorem four_rec (a b c d : ι → ℂ) :
    fourSum a b c d = mass d * tripleSum a b c - tripleSum (a*d) b c -
      tripleSum a (b*d) c - tripleSum a b (c*d) := by
  unfold fourSum tripleSum
  simp only [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  by_cases hij : i = j
  · simp [hij]
  by_cases hik : i = k
  · simp [hik]
  by_cases hjk : j = k
  · simp [hjk]
  have he : (∑ l, if i = j ∨ i = k ∨ i = l ∨ j = k ∨ j = l ∨ k = l then 0
        else a i*b j*c k*d l) =
      (a i*b j*c k) * (∑ l, if l ∈ ({i,j,k} : Finset ι) then 0 else d l) := by
    simp [mul_sum, mul_ite, hij, hik, hjk, eq_comm]
  rw [he, omit_coords]
  simp [hij, hik, hjk]
  ring

private theorem three_centered {a b c : ι → ℂ} (ha : mass a = 0)
    (hb : mass b = 0) (hc : mass c = 0) :
    tripleSum a b c = 2*mass (a*b*c) := by
  simp only [triple_rec, pair_rec, ha, hb, hc, zero_mul, mul_zero, zero_sub]
  ring_nf

/-- Three pairings of the four row vectors, using the bilinear dot product. -/
def pairingSum (a b c d : ι → ℂ) : ℂ :=
  mass (a*b)*mass (c*d) + mass (a*c)*mass (b*d) + mass (a*d)*mass (b*c)

theorem four_centered {a b c d : ι → ℂ} (ha : mass a = 0)
    (hb : mass b = 0) (hc : mass c = 0) (hd : mass d = 0) :
    fourSum a b c d = pairingSum a b c d - 6*mass (a*b*c*d) := by
  simp only [four_rec, triple_rec, pair_rec, ha, hb, hc, hd, pairingSum,
    zero_mul, mul_zero, zero_sub, sub_neg_eq_add]
  simp only [mul_left_comm, mul_comm]
  ring

end Sums

abbrev Array4 (q : ℕ) := Fin 4 × Fin q → ℂ

def row {q : ℕ} (x : Array4 q) (i : Fin 4) : Fin q → ℂ := fun j => x (i,j)

def pairTotal {q : ℕ} (x : Array4 q) : ℂ :=
  ∑ i : Fin 4, ∑ k : Fin 4, if i < k then pairSum (row x i) (row x k) else 0

def tripleTotal {q : ℕ} (x : Array4 q) : ℂ :=
  ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, if i < j ∧ j < k
    then tripleSum (row x i) (row x j) (row x k) else 0

def paired {q : ℕ} (x : Array4 q) : ℂ := pairingSum (row x 0) (row x 1) (row x 2) (row x 3)

/-- The matching sums of degrees one through four in the public statements. -/
def OnLevel {q : ℕ} (L : Submodule ℂ (Array4 q)) : Prop :=
  ∀ x ∈ L, (∑ i, mass (row x i)) = 0 ∧ pairTotal x = 0 ∧ tripleTotal x = 0 ∧
    fourSum (row x 0) (row x 1) (row x 2) (row x 3) = 0

/-- The column-first ordering and row inequalities from the desk. -/
def PostedEquations {q : ℕ} (L : Submodule ℂ (Array4 q)) : Prop :=
  ∀ t ∈ L, (∑ i : Fin 4, ∑ j, t (i,j)) = 0 ∧
    (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4,
      if a < b then t (a,j)*t (b,l) else 0) = 0 ∧
    (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else
      ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
        if a < b ∧ b < c then t (a,j)*t (b,l)*t (c,m) else 0) = 0 ∧
    (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n
      then 0 else t (0,j)*t (1,l)*t (2,m)*t (3,n)) = 0

theorem onLevel_of_posted {q : ℕ} {L : Submodule ℂ (Array4 q)} (h : PostedEquations L) :
    OnLevel L := by
  intro x hx
  obtain ⟨h₁,h₂,h₃,h₄⟩ := h x hx
  refine ⟨h₁, ?_, ?_, h₄⟩
  · refine Eq.trans ?_ h₂
    simp [pairTotal, pairSum, Fin.sum_univ_four, row, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro l _
    by_cases h : j = l <;> simp [h]
  · refine Eq.trans ?_ h₃
    simp [tripleTotal, tripleSum, Fin.sum_univ_four, row, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro l _
    apply sum_congr rfl
    intro m _
    by_cases h : j = l ∨ j = m ∨ l = m <;> simp [h]

private theorem column_identity {q : ℕ} {x : Array4 q} (hx : ∀ i, mass (row x i) = 0)
    (h₂ : pairTotal x = 0) (h₃ : tripleTotal x = 0)
    (h₄ : fourSum (row x 0) (row x 1) (row x 2) (row x 3) = 0) (hP : paired x = 0)
    (z : ℂ) : ∑ j, ∏ i, (z + x (i,j)) = q * z^4 := by
  let a := row x 0
  let b := row x 1
  let c := row x 2
  let d := row x 3
  have hp : mass (a*b) + mass (a*c) + mass (a*d) + mass (b*c) + mass (b*d) + mass (c*d) = 0 := by
    simp [pairTotal, Fin.sum_univ_four, pair_rec, hx] at h₂
    dsimp [a,b,c,d]
    linear_combination -h₂
  have ht : mass (a*b*c) + mass (a*b*d) + mass (a*c*d) + mass (b*c*d) = 0 := by
    simp [tripleTotal, Fin.sum_univ_four, three_centered (hx _) (hx _) (hx _)] at h₃
    dsimp [a,b,c,d]
    linear_combination h₃ / 2
  have hf : mass (a*b*c*d) = 0 := by
    rw [four_centered (hx _) (hx _) (hx _) (hx _)] at h₄
    change pairingSum _ _ _ _ = 0 at hP
    dsimp [a,b,c,d]
    linear_combination (hP - h₄) / 6
  have expansion : (∑ j, ∏ i, (z + x (i,j))) =
      (q : ℂ)*z^4 + z^3*(mass a+mass b+mass c+mass d) +
      z^2*(mass (a*b)+mass (a*c)+mass (a*d)+mass (b*c)+mass (b*d)+mass (c*d)) +
      z*(mass (a*b*c)+mass (a*b*d)+mass (a*c*d)+mass (b*c*d)) + mass (a*b*c*d) := by
    have hz : (q : ℂ)*z^4 = ∑ _ : Fin q, z^4 := by simp
    rw [hz]
    unfold mass
    simp only [mul_add, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    simp [Fin.prod_univ_four, a,b,c,d,row]
    ring
  rw [expansion, hp, ht, hf, show mass a = 0 from hx _, show mass b = 0 from hx _,
    show mass c = 0 from hx _, show mass d = 0 from hx _]
  ring

noncomputable def rowSums (q : ℕ) : Array4 q →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun x i := mass (row x i)
  map_add' _ _ := by ext; simp [mass,row,sum_add_distrib]
  map_smul' _ _ := by ext; simp [mass,row,mul_sum]

/-- A centered complex level subspace on which the pairing sum vanishes
has dimension strictly less than the number of columns. -/
theorem centered_dimension {q : ℕ} (hq : 0 < q) (K : Submodule ℂ (Array4 q))
    (lev : OnLevel K) (centered : ∀ x ∈ K, ∀ i, mass (row x i) = 0)
    (vanish : ∀ x ∈ K, paired x = 0) : finrank ℂ K < q := by
  classical
  apply PEqualNP.Gct.Helpers.ColumnCore.bound q (Finset.univ : Finset (Fin q)) K (by simp)
    ⟨⟨0,hq⟩, by simp⟩
  intro x hx
  obtain ⟨_, h₂, h₃, h₄⟩ := lev x hx
  exact ⟨by simp, fun z => by
    simpa using column_identity (centered x hx) h₂ h₃ h₄ (vanish x hx) z⟩

/-- If the quartic pairing vanishes on the row-centered part, the exact bound
requested by L-gct-195 and L-gct-196 holds, uniformly in the number of columns. -/
theorem dimension_of_centered_pairing {q : ℕ} (hq : 0 < q) (L : Submodule ℂ (Array4 q))
    (lev : OnLevel L) (vanish : ∀ x ∈ L, (∀ i, mass (row x i) = 0) → paired x = 0) :
    finrank ℂ L ≤ q+2 := by
  classical
  let f := (rowSums q).domRestrict L
  let K := L ⊓ LinearMap.ker (rowSums q)
  have hr (x : Array4 q) (hx : x ∈ K) (i : Fin 4) : mass (row x i) = 0 :=
    congrFun (LinearMap.mem_ker.mp hx.2) i
  have hK := centered_dimension hq K (fun x hx => lev x hx.1) hr
    (fun x hx => vanish x hx.1 (hr x hx))
  have hrange : finrank ℂ (LinearMap.range f) ≤ 3 := by
    let g : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) := LinearMap.funLeft ℂ ℂ Fin.succ
    apply le_trans ((g.domRestrict f.range).finrank_le_finrank_of_injective ?_) (by simp)
    intro y z he
    apply Subtype.ext
    obtain ⟨u, hu⟩ := y.property
    obtain ⟨v, hv⟩ := z.property
    have hs (i : Fin 3) : y.val i.succ = z.val i.succ := congrFun he i
    have hy : ∑ i, y.val i = 0 := by rw [← hu]; exact (lev _ u.property).1
    have hz : ∑ i, z.val i = 0 := by rw [← hv]; exact (lev _ v.property).1
    ext i
    refine Fin.cases ?_ (fun j => hs j) i
    rw [Fin.sum_univ_succ] at hy hz
    rw [Finset.sum_congr rfl (fun j _ => hs j)] at hy
    linear_combination hy - hz
  have hdim := PEqualNP.Gct.Helpers.ColumnCore.finrank_map_add_finrank_inf_ker (rowSums q) L
  have hmap : LinearMap.range f = L.map (rowSums q) := LinearMap.range_domRestrict ..
  rw [hmap] at hrange
  change finrank ℂ (L.map (rowSums q)) + finrank ℂ K = finrank ℂ L at hdim
  omega

/-- A counterexample to either desk bound supplies a row-centered member
with a nonzero, explicitly evaluable quartic. -/
theorem obstruction_of_large_space {q : ℕ} (hq : 0 < q) (L : Submodule ℂ (Array4 q))
    (h : PostedEquations L) (large : q+2 < finrank ℂ L) :
    ∃ x ∈ L, (∀ i, mass (row x i) = 0) ∧ paired x ≠ 0 := by
  by_contra! hn
  exact (Nat.not_le_of_gt large) (dimension_of_centered_pairing hq L (onLevel_of_posted h) hn)

private def mask {q : ℕ} (s : Finset (Fin 4)) (x : Array4 q) : Array4 q :=
  fun p => if p.1 ∈ s then x p else 0

/-- The part of L whose rows can be perturbed independently inside L. -/
def pureRows {q : ℕ} (L : Submodule ℂ (Array4 q)) : Submodule ℂ (Array4 q) where
  carrier := {x | ∀ s, mask s x ∈ L}
  zero_mem' := by
    intro s
    have he : mask s (0 : Array4 q) = 0 := by funext p; simp [mask]
    rw [he]
    exact L.zero_mem
  add_mem' {x y} hx hy s := by
    have h : mask s (x+y) = mask s x + mask s y := by
      funext p; by_cases h : p.1 ∈ s <;> simp [mask,h]
    rw [h]
    exact L.add_mem (hx s) (hy s)
  smul_mem' t x hx s := by
    have h : mask s (t • x) = t • mask s x := by
      funext p; by_cases h : p.1 ∈ s <;> simp [mask,h]
    rw [h]
    exact L.smul_mem t (hx s)

/-- In any four-row level space the direct sum of all single-row direction
spaces has dimension at most q-1, even when the full space has coupled rows. -/
theorem pureRows_dimension {q : ℕ} (hq : 0 < q) (L : Submodule ℂ (Array4 q))
    (lev : OnLevel L) : finrank ℂ (pureRows L) < q := by
  have hin {x} (hx : x ∈ pureRows L) (s : Finset (Fin 4)) := (show ∀ s, mask s x ∈ L from hx) s
  have sub : pureRows L ≤ L := by
    intro x hx
    have he : mask Finset.univ x = x := by funext p; simp [mask]
    exact he ▸ hin hx Finset.univ
  have hr {x} (hx : x ∈ pureRows L) (i : Fin 4) : mass (row x i) = 0 := by
    have h := (lev _ (hin hx {i})).1
    fin_cases i <;> simpa [Fin.sum_univ_four, mask, row, mass] using h
  apply centered_dimension hq (pureRows L) (fun x hx => lev x (sub hx)) (fun _ hx => hr hx)
  intro x hx
  have hd (j : Fin 4) (hj : j ≠ 0) : mass (row x 0 * row x j) = 0 := by
    have hp := (lev _ (hin hx {0,j})).2.1
    have h0 := hr hx 0
    simp only [mass, row] at h0
    fin_cases j <;> first | contradiction |
      simpa [pairTotal, Fin.sum_univ_four, pair_rec, mask, row, mass, h0] using hp
  simp [paired, pairingSum, hd _ (by decide : (1 : Fin 4) ≠ 0),
    hd _ (by decide : (2 : Fin 4) ≠ 0), hd _ (by decide : (3 : Fin 4) ≠ 0)]

end

end GctFrontier.FourRowContractions

open GctFrontier.FourRowContractions in
theorem PEqualNP.Research.FourRowContractions (q : ℕ) (hq : 0 < q) (L : Submodule ℂ (Array4 q))
    (h : PostedEquations L) :
    ((∀ x ∈ L, (∀ i, mass (row x i) = 0) → paired x = 0) → Module.finrank ℂ L ≤ q + 2) ∧
    (∀ K : Submodule ℂ (Array4 q), K ≤ pureRows L → Module.finrank ℂ K < q) := by
  have lev := onLevel_of_posted h
  exact ⟨dimension_of_centered_pairing hq L lev,
    fun _ hk => lt_of_le_of_lt (Submodule.finrank_mono hk) (pureRows_dimension hq L lev)⟩
