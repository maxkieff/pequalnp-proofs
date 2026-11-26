import PEqualNP.Outside.L_gct_234
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Positive-root orders when three sparse inputs span at most a pencil. -/

namespace GctFrontier.DependentTrinomialCubes

open Polynomial Finset PEqualNP.Outside.L_gct_234.SparseCubes

private theorem order_power (p : ℝ[X]) (x : ℝ) (n : ℕ) :
    (p^n).rootMultiplicity x = n*p.rootMultiplicity x := by
  by_cases hp : p=0
  · subst p
    cases n <;> simp
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,rootMultiplicity_mul (mul_ne_zero (pow_ne_zero n hp) hp),ih,Nat.succ_mul]

private theorem support_linear (p q : ℝ[X]) (a b : ℝ) :
    (C a*p+C b*q).support ⊆ p.support ∪ q.support := by
  intro k hk
  by_contra h
  simp only [Finset.mem_union,not_or,Polynomial.notMem_support_iff] at h
  exact (mem_support_iff.mp hk) (by simp [coeff_C_mul,h.1,h.2])

private theorem small_order (p : ℝ[X]) (U : Finset ℕ) (hs : p.support ⊆ U) (r : ℝ) (hr : r≠0) :
    p.rootMultiplicity r ≤ U.card-1 := by
  by_cases hp : p=0
  · simp [hp]
  have h := (rootMultiplicity_lt_support_card r hr p hp).trans_le (card_le_card hs)
  omega

private theorem quadratic_order (p q : ℝ[X]) (r : ℝ) (hp : p≠0)
    (ord : p.rootMultiplicity r ≤ q.rootMultiplicity r) :
    (p^2-p*q+q^2).rootMultiplicity r = 2*p.rootMultiplicity r := by
  let m := p.rootMultiplicity r
  obtain ⟨P,ep,en⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp r
  have pe : P.eval r≠0 := fun h => en (dvd_iff_isRoot.mpr h)
  obtain ⟨Q,eqn⟩ := (pow_dvd_pow (X-C r) ord).trans (pow_rootMultiplicity_dvd q r)
  have e : p^2-p*q+q^2=(P^2-P*Q+Q^2)*(X-C r)^(2*m) := by
    change p=(X-C r)^m*P at ep
    change q=(X-C r)^m*Q at eqn
    rw [ep,eqn,show 2*m=m*2 by omega,pow_mul]
    ring
  have unit : (P^2-P*Q+Q^2).eval r ≠ 0 := by
    simp only [eval_add,eval_sub,eval_pow,eval_mul]
    nlinarith [sq_nonneg (2*Q.eval r-P.eval r),sq_pos_of_ne_zero pe]
  have nn : P^2-P*Q+Q^2 ≠ 0 := by intro he; simp [he] at unit
  rw [e,rootMultiplicity_mul_X_sub_C_pow nn,rootMultiplicity_eq_zero (p:=P^2-P*Q+Q^2) unit,
    zero_add]

private theorem two_plain (p q : ℝ[X]) (k : ℕ) (hp : p.support.card≤k) (hq : q.support.card≤k)
    (r : ℝ) (hr : r≠0) : (p^3+q^3).rootMultiplicity r ≤ 4*k-3 := by
  by_cases zp : p=0
  · by_cases zq : q=0
    · simp [zp,zq]
    have v := (rootMultiplicity_lt_support_card r hr q zq).trans_le hq
    simp only [zp,zero_pow (by decide : 3≠0),zero_add,order_power]
    omega
  by_cases zq : q=0
  · have v := (rootMultiplicity_lt_support_card r hr p zp).trans_le hp
    simp only [zq,zero_pow (by decide : 3≠0),add_zero,order_power]
    omega
  rw [show p^3+q^3=(p+q)*(p^2-p*q+q^2) by ring]
  by_cases nz : (p+q)*(p^2-p*q+q^2)=0
  · simp [nz]
  rw [rootMultiplicity_mul nz]
  have s := (rootMultiplicity_lt_support_card r hr (p+q) (left_ne_zero_of_mul nz)).trans_le
    ((card_le_card (Polynomial.support_add ..)).trans (Finset.card_union_le _ _))
  rcases le_total (p.rootMultiplicity r) (q.rootMultiplicity r) with h|h
  · rw [quadratic_order p q r zp h]
    have v := (rootMultiplicity_lt_support_card r hr p zp).trans_le hp
    omega
  · rw [show p^2-p*q+q^2=q^2-q*p+p^2 by ring,quadratic_order q p r zq h]
    have v := (rootMultiplicity_lt_support_card r hr q zq).trans_le hq
    omega

private theorem cube_root (a : ℝ) : ∃ t : ℝ, t^3=a := by
  by_cases h : 0≤a
  · exact ⟨a^(3:ℝ)⁻¹,Real.rpow_inv_natCast_pow h (by decide : (3:ℕ)≠0)⟩
  have hn : 0≤ -a := by linarith
  refine ⟨-((-a)^(3:ℝ)⁻¹),?_⟩
  have hh := Real.rpow_inv_natCast_pow hn (by decide : (3:ℕ)≠0)
  linear_combination -hh

theorem two_weighted (p q : ℝ[X]) (k : ℕ) (hp : p.support.card≤k) (hq : q.support.card≤k)
    (a b r : ℝ) (hr : r≠0) : (C a*p^3+C b*q^3).rootMultiplicity r ≤ 4*k-3 := by
  obtain ⟨u,rfl⟩ := cube_root a
  obtain ⟨v,rfl⟩ := cube_root b
  have h := two_plain (C u*p) (C v*q) k ((support_C_mul_card_le ..).trans hp)
    ((support_C_mul_card_le ..).trans hq) r hr
  simpa only [mul_pow,map_pow] using h

private noncomputable def binary (a b c d : ℝ) (p q : ℝ[X]) : ℝ[X] :=
  C a*p^3+C b*p^2*q+C c*p*q^2+C d*q^3

private theorem local_order (a b c d r : ℝ) (P H : ℝ[X]) (hu : P.eval r≠0) (hz : H.eval r=0)
    (k : ℕ) (hk : 2≤k) (h3 : b=0 → c=0 → 3≤k) :
    (binary a b c d P H).rootMultiplicity r ≤ k*H.rootMultiplicity r := by
  by_cases za : a=0
  · subst a
    by_cases zb : b=0
    · subst b
      by_cases zc : c=0
      · subst c
        by_cases zd : d=0
        · simp [binary,zd]
        · simp only [binary,C_0,zero_mul,zero_add,rootMultiplicity_C_mul zd,order_power]
          exact Nat.mul_le_mul_right _ (h3 rfl rfl)
      have he : binary 0 0 c d P H=H^2*(C c*P+C d*H) := by simp [binary]; ring
      have unit : (C c*P+C d*H).eval r≠0 := by simpa [hz] using mul_ne_zero zc hu
      rw [he]
      by_cases z : H^2*(C c*P+C d*H)=0
      · simp [z]
      rw [rootMultiplicity_mul z,rootMultiplicity_eq_zero (p:=C c*P+C d*H) unit,order_power]
      simpa only [add_zero] using Nat.mul_le_mul_right (H.rootMultiplicity r) hk
    have he : binary 0 b c d P H=H*(C b*P^2+C c*P*H+C d*H^2) := by simp [binary]; ring
    have unit : (C b*P^2+C c*P*H+C d*H^2).eval r≠0 := by
      simpa [hz] using mul_ne_zero zb (pow_ne_zero 2 hu)
    rw [he]
    by_cases z : H*(C b*P^2+C c*P*H+C d*H^2)=0
    · simp [z]
    rw [rootMultiplicity_mul z,rootMultiplicity_eq_zero (p:=C b*P^2+C c*P*H+C d*H^2) unit]
    have hh := Nat.mul_le_mul_right (H.rootMultiplicity r) hk
    omega
  have unit : (binary a b c d P H).eval r≠0 := by
    simpa [binary,hz] using mul_ne_zero za (pow_ne_zero 3 hu)
  rw [rootMultiplicity_eq_zero (p:=binary a b c d P H) unit]
  omega

private theorem ordered_binary (p q : ℝ[X]) (U : Finset ℕ) (hp : p.support ⊆ U)
    (hq : q.support ⊆ U) (a b c d r : ℝ) (hr : r≠0) (np : p≠0)
    (ord : p.rootMultiplicity r ≤ q.rootMultiplicity r) :
    (binary a b c d p q).rootMultiplicity r ≤ 3*(U.card-1) ∧
    ((∀ l : ℝ, ¬(b+2*c*l+3*d*l^2=0 ∧ c+3*d*l=0)) →
      (binary a b c d p q).rootMultiplicity r ≤ p.rootMultiplicity r+2*(U.card-1)) := by
  let m := p.rootMultiplicity r
  obtain ⟨P,ep,en⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p np r
  have pe : P.eval r≠0 := fun h => en (dvd_iff_isRoot.mpr h)
  obtain ⟨Q,eqn⟩ := (pow_dvd_pow (X-C r) ord).trans (pow_rootMultiplicity_dvd q r)
  change p=(X-C r)^m*P at ep
  change q=(X-C r)^m*Q at eqn
  let l := Q.eval r/P.eval r
  let H := Q-C l*P
  have hH : H.eval r=0 := by simp [H,l,pe]
  have eqQ : Q=H+C l*P := by simp [H]
  let T := binary (a+b*l+c*l^2+d*l^3) (b+2*c*l+3*d*l^2) (c+3*d*l) d P H
  have he : binary a b c d p q = T*(X-C r)^(3*m) := by
    rw [ep,eqn,eqQ,show 3*m=m*3 by omega,pow_mul]
    dsimp only [T,binary]
    simp only [map_add,map_mul,map_pow,map_ofNat]
    ring
  rw [he]
  by_cases zT : T=0
  · simp [zT]
  rw [rootMultiplicity_mul_X_sub_C_pow zT]
  have upper : H.rootMultiplicity r+m ≤ U.card-1 := by
    by_cases zH : H=0
    · rw [zH,rootMultiplicity_zero,zero_add]
      exact small_order p U hp r hr
    have linear : C 1*q+C (-l)*p = H*(X-C r)^m := by
      rw [ep,eqn]
      simp [H]
      ring
    have hs := (support_linear q p 1 (-l)).trans (Finset.union_subset hq hp)
    have bound := small_order _ U hs r hr
    rwa [linear,rootMultiplicity_mul_X_sub_C_pow zH] at bound
  constructor
  · have h3 : T.rootMultiplicity r ≤ 3*H.rootMultiplicity r :=
      local_order _ _ _ _ r P H pe hH 3 (by decide) (by simp)
    omega
  · intro reg
    have h2 : T.rootMultiplicity r ≤ 2*H.rootMultiplicity r :=
      local_order _ _ _ _ r P H pe hH 2 (by decide) (fun eb ec => False.elim (reg l ⟨eb,ec⟩))
    change T.rootMultiplicity r+3*m ≤ m+2*(U.card-1)
    omega

private theorem binary_bound (p q : ℝ[X]) (U : Finset ℕ) (hp : p.support ⊆ U)
    (hq : q.support ⊆ U) (a b c d r : ℝ) (hr : r≠0) :
    (binary a b c d p q).rootMultiplicity r ≤ 3*(U.card-1) := by
  by_cases zp : p=0
  · by_cases zd : d=0
    · simp [binary,zp,zd]
    · simp only [binary,zp,zero_pow (by decide : 2≠0),zero_pow (by decide : 3≠0),
        mul_zero,zero_mul,zero_add,rootMultiplicity_C_mul zd,order_power]
      have := small_order q U hq r hr
      omega
  by_cases zq : q=0
  · by_cases za : a=0
    · simp [binary,zq,za]
    · simp only [binary,zq,zero_pow (by decide : 2≠0),zero_pow (by decide : 3≠0),
        mul_zero,add_zero,rootMultiplicity_C_mul za,order_power]
      have := small_order p U hp r hr
      omega
  rcases le_total (p.rootMultiplicity r) (q.rootMultiplicity r) with h|h
  · exact (ordered_binary p q U hp hq _ _ _ _ r hr zp h).1
  · rw [show binary a b c d p q=binary d c b a q p by unfold binary; ring]
    exact (ordered_binary q p U hq hp _ _ _ _ r hr zq h).1

private theorem union_card (p q : ℝ[X]) (a b : ℝ) (ha : a≠0) (hb : b≠0) :
    2*(p.support ∪ q.support).card ≤ p.support.card+q.support.card+(C a*p+C b*q).support.card := by
  have hs : p.support ∪ q.support ⊆ (p.support ∩ q.support) ∪ (C a*p+C b*q).support := by
    intro n hn
    by_cases pn : n∈p.support
    · by_cases qn : n∈q.support
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨pn,qn⟩)
      · apply Finset.mem_union_right
        simpa [Polynomial.mem_support_iff,coeff_C_mul,Polynomial.notMem_support_iff.mp qn] using
          mul_ne_zero ha (Polynomial.mem_support_iff.mp pn)
    · have qn := (Finset.mem_union.mp hn).resolve_left pn
      apply Finset.mem_union_right
      simpa [Polynomial.mem_support_iff,coeff_C_mul,Polynomial.notMem_support_iff.mp pn] using
        mul_ne_zero hb (Polynomial.mem_support_iff.mp qn)
  have h1 := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have h2 := Finset.card_union_add_card_inter p.support q.support
  omega

theorem dependent_explicit (p q : ℝ[X]) (a b u v w r : ℝ) (hr : r≠0)
    (hp : p.support.card≤3) (hq : q.support.card≤3) (hs : (C a*p+C b*q).support.card≤3) :
    (C u*p^3+C v*q^3+C w*(C a*p+C b*q)^3).rootMultiplicity r ≤ 9 := by
  by_cases ha : a=0
  · rw [show C u*p^3+C v*q^3+C w*(C a*p+C b*q)^3 = C u*p^3+C (v+w*b^3)*q^3 by
      simp [ha,mul_pow,map_add,map_mul,map_pow]; ring]
    exact two_weighted p q 3 hp hq _ _ r hr
  by_cases hb : b=0
  · rw [show C u*p^3+C v*q^3+C w*(C a*p+C b*q)^3 = C (u+w*a^3)*p^3+C v*q^3 by
      simp [hb,mul_pow,map_add,map_mul,map_pow]; ring]
    exact two_weighted p q 3 hp hq _ _ r hr
  let U := p.support ∪ q.support
  have hU : U.card≤4 := by have := union_card p q a b ha hb; dsimp [U]; omega
  have he : C u*p^3+C v*q^3+C w*(C a*p+C b*q)^3 =
      binary (u+w*a^3) (3*w*a^2*b) (3*w*a*b^2) (v+w*b^3) p q := by
    simp only [binary,map_add,map_mul,map_pow,map_ofNat]
    ring
  rw [he]
  have hh := binary_bound p q U Finset.subset_union_left Finset.subset_union_right
    (u+w*a^3) (3*w*a^2*b) (3*w*a*b^2) (v+w*b^3) r hr
  omega

private theorem genuine_ordered (p q : ℝ[X]) (a b u v w r : ℝ) (hr : r≠0) (np : p≠0)
    (ord : p.rootMultiplicity r ≤ q.rootMultiplicity r) (ha : a≠0) (hb : b≠0) (hv : v≠0) (hw : w≠0)
    (hp : p.support.card≤3) (hq : q.support.card≤3) (hs : (C a*p+C b*q).support.card≤3) :
    (C u*p^3+C v*q^3+C w*(C a*p+C b*q)^3).rootMultiplicity r ≤ 8 := by
  let U := p.support ∪ q.support
  have hU : U.card≤4 := by have := union_card p q a b ha hb; dsimp [U]; omega
  have he : C u*p^3+C v*q^3+C w*(C a*p+C b*q)^3 =
      binary (u+w*a^3) (3*w*a^2*b) (3*w*a*b^2) (v+w*b^3) p q := by
    simp only [binary,map_add,map_mul,map_pow,map_ofNat]
    ring
  rw [he]
  have reg (l : ℝ) : ¬(3*w*a^2*b+2*(3*w*a*b^2)*l+3*(v+w*b^3)*l^2=0 ∧
      3*w*a*b^2+3*(v+w*b^3)*l=0) := by
    rintro ⟨h1,h2⟩
    have hzero : w*a*b*(a+b*l)=0 := by linear_combination (h1-l*h2)/3
    have hab := (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero (mul_ne_zero hw ha) hb)
    have hvl : v*l=0 := by linear_combination h2/3-w*b^2*hab
    have hl := (mul_eq_zero.mp hvl).resolve_left hv
    simp [hl,ha] at hab
  have hh := (ordered_binary p q U Finset.subset_union_left Finset.subset_union_right
    (u+w*a^3) (3*w*a^2*b) (3*w*a*b^2) (v+w*b^3) r hr np ord).2 reg
  have low := (rootMultiplicity_lt_support_card r hr p np).trans_le hp
  omega

theorem genuine_three (p q : ℝ[X]) (a b u v w r : ℝ) (hr : r≠0)
    (np : p≠0) (nq : q≠0) (ha : a≠0) (hb : b≠0) (hu : u≠0) (hv : v≠0) (hw : w≠0)
    (hp : p.support.card≤3) (hq : q.support.card≤3) (hs : (C a*p+C b*q).support.card≤3) :
    (C u*p^3+C v*q^3+C w*(C a*p+C b*q)^3).rootMultiplicity r ≤ 8 := by
  rcases le_total (p.rootMultiplicity r) (q.rootMultiplicity r) with h|h
  · exact genuine_ordered p q a b u v w r hr np h ha hb hv hw hp hq hs
  · have rev := genuine_ordered q p b a v u w r hr nq h hb ha hu hw hq hp
      (show (C b*q+C a*p).support.card≤3 by rwa [add_comm])
    simpa only [add_comm,add_left_comm,add_assoc] using rev

private theorem solve_relation (p q t : ℝ[X]) (a b c : ℝ) (hc : c≠0)
    (rel : C a*p+C b*q+C c*t=0) : t=C (-a/c)*p+C (-b/c)*q := by
  apply mul_left_cancel₀ (C_ne_zero.mpr hc)
  have ha : c*(-a/c)= -a := by field_simp
  have hb : c*(-b/c)= -b := by field_simp
  simp only [mul_add,← mul_assoc,← map_mul,ha,hb,map_neg,neg_mul]
  linear_combination rel

theorem dependent_bound (g : Fin 3 → ℝ[X]) (s : Fin 3 → ℝ)
    (hs : ∀ i, (g i).support.card≤3) (hd : ¬LinearIndependent ℝ g) (r : ℝ) (hr : r≠0) :
    (∑ i, C (s i)*(g i)^3).rootMultiplicity r ≤ 9 := by
  obtain ⟨c,rel,i,hi⟩ := Fintype.not_linearIndependent_iff.mp hd
  simp only [Fin.sum_univ_three,smul_eq_C_mul] at rel
  rw [Fin.sum_univ_three]
  have finish (i j k : Fin 3) (hk : c k≠0)
      (eqn : C (c i)*g i+C (c j)*g j+C (c k)*g k=0) :
      (C (s i)*(g i)^3+C (s j)*(g j)^3+C (s k)*(g k)^3).rootMultiplicity r≤9 := by
    have eqt := solve_relation _ _ _ _ _ _ hk eqn
    have hs' := hs k
    rw [eqt] at hs' ⊢
    exact dependent_explicit _ _ _ _ _ _ _ _ hr (hs i) (hs j) hs'
  fin_cases i
  · have ans := finish 1 2 0 hi (by linear_combination rel)
    simpa only [add_comm,add_left_comm,add_assoc] using ans
  · have ans := finish 0 2 1 hi (by linear_combination rel)
    simpa only [add_comm,add_left_comm,add_assoc] using ans
  · exact finish 0 1 2 hi rel

private noncomputable def tri (e f h : ℕ) (a b c : ℝ) : ℝ[X] :=
  C a*X^e+C b*X^f+C c*X^h

private theorem tri_card (e f h : ℕ) (a b c : ℝ) : (tri e f h a b c).support.card≤3 := by
  apply (Finset.card_le_card (support_trinomial_subset e f h a b c)).trans
  exact (Finset.card_insert_le _ _).trans (by have hh := Finset.card_le_two (a:=f) (b:=h); omega)

theorem attain_nine :
    ∃ g : Fin 3 → ℝ[X], (∀ i, (g i).support.card≤3) ∧ ¬LinearIndependent ℝ g ∧
      (∑ i,(g i)^3)≠0 ∧ (∑ i,(g i)^3).rootMultiplicity 1=9 := by
  let p := tri 0 4 5 1 (-5) 4
  let q := tri 1 2 6 (-4) 5 (-1)
  let g : Fin 3 → ℝ[X] := ![p,q,0]
  refine ⟨g,?_,?_,?_⟩
  · intro i
    fin_cases i
    · apply tri_card
    · apply tri_card
    · simp [g]
  · intro hi
    exact hi.ne_zero 2 (by simp [g])
  let U : ℝ[X] := 4*X^3+3*X^2+2*X+1
  let V : ℝ[X] := -X^4-2*X^3-3*X^2-4*X
  have eP : p=(X-1)^2*U := by simp [p,tri,U,map_neg,map_ofNat]; ring
  have eQ : q=(X-1)^2*V := by simp [q,tri,V,map_neg,map_ofNat]; ring
  have es : p+q= -(X+1)*(X-1)^5 := by simp [p,q,tri,map_neg,map_ofNat]; ring
  let R : ℝ[X] := -(X+1)*(U^2-U*V+V^2)
  have eqn : (∑ i,(g i)^3)=R*(X-C 1)^9 := by
    simp only [g,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
    change p^3+q^3+0^3=_
    rw [show p^3+q^3=(p+q)*(p^2-p*q+q^2) by ring,es,eP,eQ]
    dsimp only [R]
    rw [C_1]
    ring
  have hr : R.eval 1≠0 := by norm_num [R,U,V]
  have hn : R≠0 := by intro eq; simp [eq] at hr
  rw [eqn,rootMultiplicity_mul_X_sub_C_pow hn,rootMultiplicity_eq_zero (p:=R) hr,zero_add]
  exact ⟨mul_ne_zero hn (pow_ne_zero _ (X_sub_C_ne_zero _)),rfl⟩

theorem attain_eight :
    ∃ (p q : ℝ[X]) (a b u v w : ℝ),
      p≠0 ∧ q≠0 ∧ a≠0 ∧ b≠0 ∧ u≠0 ∧ v≠0 ∧ w≠0 ∧
      p.support.card≤3 ∧ q.support.card≤3 ∧ (C a*p+C b*q).support.card≤3 ∧
      (C u*p^3+C v*q^3+C w*(C a*p+C b*q)^3).rootMultiplicity 1=8 := by
  let p := tri 0 1 2 1 (-2) 1
  let q := tri 1 2 3 1 (-2) 1
  refine ⟨p,q,1,2,-9,-18,1,?_,?_,by norm_num,by norm_num,by norm_num,by norm_num,by norm_num,
    tri_card ..,tri_card ..,?_,?_⟩
  · intro z
    have h := congrArg (Polynomial.eval 2) z
    norm_num [p,tri] at h
  · intro z
    have h := congrArg (Polynomial.eval 2) z
    norm_num [q,tri] at h
  · rw [show C 1*p+C 2*q=tri 0 2 3 1 (-3) 2 by simp [p,q,tri,map_neg,map_ofNat]; ring]
    apply tri_card
  · let R : ℝ[X] := -8-10*X
    have eqn : C (-9)*p^3+C (-18)*q^3+C 1*(C 1*p+C 2*q)^3=R*(X-C 1)^8 := by
      simp [p,q,tri,R,map_neg,map_ofNat]
      ring
    have hr : R.eval 1≠0 := by norm_num [R]
    have hn : R≠0 := by intro e; simp [e] at hr
    rw [eqn,rootMultiplicity_mul_X_sub_C_pow hn,rootMultiplicity_eq_zero (p:=R) hr,zero_add]

end GctFrontier.DependentTrinomialCubes

open GctFrontier.DependentTrinomialCubes in
theorem PEqualNP.Research.DependentTrinomialCubes :
    (∀ (g : Fin 3 → Polynomial ℝ) (s : Fin 3 → ℝ), (∀ i, (g i).support.card ≤ 3) →
      ¬LinearIndependent ℝ g → ∀ r : ℝ, r ≠ 0 →
      Polynomial.rootMultiplicity r (∑ i, Polynomial.C (s i)*(g i)^3) ≤ 9) ∧
    (∃ g : Fin 3 → Polynomial ℝ, (∀ i, (g i).support.card ≤ 3) ∧ ¬LinearIndependent ℝ g ∧
      (∑ i,(g i)^3) ≠ 0 ∧ Polynomial.rootMultiplicity 1 (∑ i,(g i)^3) = 9) ∧
    (∀ (p q : Polynomial ℝ) (a b u v w r : ℝ), r≠0 → p≠0 → q≠0 → a≠0 → b≠0 →
      u≠0 → v≠0 → w≠0 → p.support.card≤3 → q.support.card≤3 →
      (Polynomial.C a*p+Polynomial.C b*q).support.card≤3 →
      Polynomial.rootMultiplicity r (Polynomial.C u*p^3+Polynomial.C v*q^3+
        Polynomial.C w*(Polynomial.C a*p+Polynomial.C b*q)^3) ≤ 8) ∧
    (∃ (p q : Polynomial ℝ) (a b u v w : ℝ), p≠0 ∧ q≠0 ∧ a≠0 ∧ b≠0 ∧ u≠0 ∧ v≠0 ∧ w≠0 ∧
      p.support.card≤3 ∧ q.support.card≤3 ∧ (Polynomial.C a*p+Polynomial.C b*q).support.card≤3 ∧
      Polynomial.rootMultiplicity 1 (Polynomial.C u*p^3+Polynomial.C v*q^3+
        Polynomial.C w*(Polynomial.C a*p+Polynomial.C b*q)^3) = 8) ∧
    (∀ (p q : Polynomial ℝ) (k : ℕ), p.support.card≤k → q.support.card≤k → ∀ a b r : ℝ, r≠0 →
      Polynomial.rootMultiplicity r (Polynomial.C a*p^3+Polynomial.C b*q^3) ≤ 4*k-3) :=
  ⟨dependent_bound,attain_nine,genuine_three,attain_eight,two_weighted⟩
