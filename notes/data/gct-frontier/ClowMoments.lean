import Mathlib
import PEqualNP.Defs.Gct

/-! A coefficient equation for scalar closed-walk programs at four rows.
    Each two-step prefix and each two-step suffix may have an independent weight. -/

namespace GctFrontier.ClowMoments

open MvPolynomial Filter Topology

abbrev V := Fin 4
abbrev Var := V × V

structure Arc where
  head : V
  src : V
  dst : V
  nextHead : Option V
  deriving DecidableEq, Repr

abbrev Half := Arc × Arc
abbrev Walk := Half × Half

private def steps (h u : V) : List (Arc × (V × V)) :=
  let later := (List.finRange 4).filter (h < ·)
  later.map (fun v => (⟨h,u,v,some h⟩,(h,v))) ++
    later.map (fun g => (⟨h,u,h,some g⟩,(g,g)))

/-- At each closing arc the next head strictly increases. The first head is zero. -/
def walks : Finset Walk := (do
  let (a,s) ← steps 0 0
  let (b,t) ← steps s.1 s.2
  let (c,u) ← steps t.1 t.2
  return ((a,b),(c,(⟨u.1,u.2,u.1,none⟩ : Arc)))).toFinset

private noncomputable def edge (x : Arc) : Var →₀ ℕ := Finsupp.single (x.src,x.dst) 1
noncomputable def exponent (w : Walk) : Var →₀ ℕ :=
  edge w.1.1 + edge w.1.2 + edge w.2.1 + edge w.2.2

private def hit (a : Arc) (v : Var) : ℕ := if (a.src,a.dst) = v then 1 else 0
private def signature (w : Walk) (v : Var) : ℕ :=
  hit w.1.1 v + hit w.1.2 v + hit w.2.1 v + hit w.2.2 v

private theorem exponent_apply (w : Walk) (v : Var) : exponent w v = signature w v := by
  simp [exponent, edge, signature, hit, Finsupp.single_apply]

/-- This family contains every scalar edge weighting, even if a label depends
    on time and on the next head chosen at a closing step. -/
noncomputable def walkPoly (p v : Half → ℂ) : MvPolynomial Var ℂ :=
  ∑ w ∈ walks, monomial (exponent w) (p w.1 * v w.2)

private def focus (s : Bool) : V := if s then 3 else 1
private def vertexPrefix (z u : V) : Half := (⟨0,0,z,some 0⟩, ⟨0,z,u,some 0⟩)
private def headPrefix (z h : V) : Half := (⟨0,0,z,some 0⟩, ⟨0,z,0,some h⟩)

private def tails (i : V) : Fin 6 → Half :=
  let j : V := 2
  let h := min i j
  let r := max i j
  ![(⟨0,i,0,some j⟩,⟨j,j,j,none⟩), (⟨h,h,h,some r⟩,⟨r,r,r,none⟩),
    (⟨0,j,i,some 0⟩,⟨0,i,0,none⟩), (⟨h,h,r,some h⟩,⟨h,r,h,none⟩),
    (⟨0,i,j,some 0⟩,⟨0,j,0,none⟩), (⟨0,j,0,some i⟩,⟨i,i,i,none⟩)]

private def firstWalk (s : Bool) : Fin 9 → Walk :=
  let i := focus s
  let l := focus (!s)
  let h := min i 2
  let t := tails i
  ![(vertexPrefix l i,t 0), (headPrefix l h,t 1), (vertexPrefix l 2,t 2),
    (headPrefix l h,t 3), (vertexPrefix l i,t 4), (vertexPrefix l 2,t 5),
    (vertexPrefix i i,t 0), (vertexPrefix i 2,t 2), (vertexPrefix i i,t 4)]

private def otherWalk (s : Bool) : Fin 3 → Walk :=
  let i := focus s
  let t := tails i
  ![(headPrefix i (min i 2),t 1), (headPrefix i (min i 2),t 3), (vertexPrefix i 2,t 5)]

private def expected (s : Bool) (k : Fin 9) : Finset Walk :=
  if h : k.val < 6 then {firstWalk s k}
  else {firstWalk s k, otherWalk s ⟨k.val-6,by omega⟩}

noncomputable def index (s : Bool) (k : Fin 9) : Var →₀ ℕ := exponent (firstWalk s k)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem enumeration : ∀ s k, walks.filter (fun w => signature w = signature (firstWalk s k)) = expected s k := by
  decide

set_option maxRecDepth 20000 in
private theorem distinct : ∀ s (k : Fin 9) (h : ¬ k.val < 6),
    firstWalk s k ≠ otherWalk s ⟨k.val-6,by omega⟩ := by decide

def denom (z : Fin 9 → ℂ) : ℂ := z 0*z 3*z 5 + z 1*z 2*z 4
def numer (z : Fin 9 → ℂ) : ℂ := z 0*z 3*z 8 - z 3*z 4*z 6 + z 1*z 4*z 7

def equation (z : Bool → Fin 9 → ℂ) : ℂ :=
  numer (z false) * numer (z true) - denom (z false) * denom (z true)

private def frame (p u : Fin 3 → ℂ) (v : Fin 6 → ℂ) : Fin 9 → ℂ :=
  ![p 0*v 0, p 2*v 1, p 1*v 2, p 2*v 3, p 0*v 4, p 1*v 5,
    u 0*v 0 + u 2*v 1, u 1*v 2 + u 2*v 3, u 0*v 4 + u 1*v 5]

private def pref (p : Half → ℂ) (z i : V) : Fin 3 → ℂ :=
  ![p (vertexPrefix z i),p (vertexPrefix z 2),p (headPrefix z (min i 2))]

set_option maxRecDepth 4096 in
private theorem frame_coeff (p v : Half → ℂ) (s : Bool) :
    (fun k => (walkPoly p v).coeff (index s k)) =
      frame (pref p (focus (!s)) (focus s)) (pref p (focus s) (focus s)) (v ∘ tails (focus s)) := by
  funext k
  have hc : (walkPoly p v).coeff (index s k) = ∑ w ∈ expected s k, p w.1 * v w.2 := by
    have eqv (w : Walk) : exponent w = index s k ↔ signature w = signature (firstWalk s k) := by
      rw [DFunLike.ext_iff, funext_iff]
      simp [index, exponent_apply]
    rw [← enumeration, Finset.sum_filter]
    simp [walkPoly, coeff_monomial, eqv]
  rw [hc]
  clear hc
  by_cases h : k.val < 6
  · simp only [expected, dite_eq_left h, Finset.sum_singleton]
    fin_cases k <;> first | exact ((by decide : ¬ _) h).elim | rfl
  · simp only [expected, dite_eq_right h, Finset.sum_pair (distinct s k h)]
    fin_cases k <;> first | exact (h (by decide)).elim | rfl

private theorem collapse (p u : Fin 3 → ℂ) (v : Fin 6 → ℂ) :
    denom (frame p u v) = p 0*p 1*p 2*(v 0*v 3*v 5 + v 1*v 2*v 4) ∧
    numer (frame p u v) = p 0*u 1*p 2*(v 0*v 3*v 5 + v 1*v 2*v 4) := by
  constructor <;> simp [frame, denom, numer] <;> ring

/-- A homogeneous sextic in eighteen selected coefficient slots vanishes for
    every scalar closed-walk polynomial, including all singular weight choices. -/
theorem walk_equation (p v : Half → ℂ) :
    equation (fun s k => (walkPoly p v).coeff (index s k)) = 0 := by
  simp only [equation, frame_coeff, (collapse _ _ _).1, (collapse _ _ _).2]
  simp [pref]
  ring

private noncomputable def permExp (σ : Equiv.Perm V) : Var →₀ ℕ :=
  ∑ i : V, Finsupp.single (σ i,i) 1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
private theorem match_count : ∀ s (k : Fin 9),
    (Finset.univ.filter (fun σ : Equiv.Perm V => (fun e : Var => if σ e.2 = e.1 then 1 else 0) =
      signature (firstWalk s k))).card = (if k.val < 6 then 1 else 0) := by decide

private theorem permExp_apply (σ : Equiv.Perm V) (e : Var) :
    permExp σ e = if σ e.2 = e.1 then 1 else 0 := by
  obtain ⟨i,j⟩ := e
  fin_cases j <;> simp [permExp, Fin.sum_univ_four, Finsupp.single_apply, Prod.ext_iff]

private theorem perm_term (σ : Equiv.Perm V) : (∏ i : V, (MvPolynomial.X (σ i,i) : MvPolynomial Var ℂ)) =
    monomial (permExp σ) 1 := by
  simp [permExp, Fin.prod_univ_four, Fin.sum_univ_four, X]

private theorem perm_coeff (s : Bool) (k : Fin 9) :
    (PEqualNP.Gct.permPoly ℂ 4).coeff (index s k) = if k.val < 6 then 1 else 0 := by
  simp only [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply, perm_term,
    coeff_sum, coeff_monomial]
  have eqv (σ : Equiv.Perm V) : permExp σ = index s k ↔
      (fun e : Var => if σ e.2 = e.1 then 1 else 0) = signature (firstWalk s k) := by
    rw [DFunLike.ext_iff, funext_iff]
    simp [permExp_apply,index,exponent_apply]
  simp_rw [eqv]
  have h := congrArg (fun n : ℕ => (n : ℂ)) (match_count s k)
  simpa only [Finset.card_filter, Nat.cast_sum, apply_ite, Nat.cast_one, Nat.cast_zero] using h

theorem permanent_equation :
    equation (fun s k => (PEqualNP.Gct.permPoly ℂ 4).coeff (index s k)) = -4 := by
  simp [equation, denom, numer, perm_coeff]
  norm_num

/-- Even a coordinatewise convergent sequence of scalar walk coefficients
    cannot approach the four-row permanent. No boundedness of weights is assumed. -/
theorem no_scalar_walk_limit (p v : ℕ → Half → ℂ) :
    ¬ ∀ d, Tendsto (fun n => (walkPoly (p n) (v n)).coeff d) atTop
      (𝓝 ((PEqualNP.Gct.permPoly ℂ 4).coeff d)) := by
  intro h
  have hc : Continuous equation := by unfold equation numer denom; fun_prop
  have he := (hc.tendsto (fun s k => (PEqualNP.Gct.permPoly ℂ 4).coeff (index s k))).comp
    (tendsto_pi_nhds.mpr fun s => tendsto_pi_nhds.mpr fun k => h (index s k))
  change Tendsto (fun n => equation (fun s k => (walkPoly (p n) (v n)).coeff (index s k)))
    atTop (𝓝 _) at he
  have absurd : (0 : ℂ) = -4 := by
    simpa only [walk_equation, permanent_equation, tendsto_const_nhds_iff] using he
  norm_num at absurd

private def nextOrigin (a : Arc) : V :=
  if a.dst = a.head then a.nextHead.getD 0 else a.dst

/-- For fixed nonzero v, this separates the two nonzero choices other than v. -/
private def bit (v a : V) : Bool := decide (a = if v = 1 then 2 else 1)

private def enters (channel : Bool) (a : Arc) : Bool :=
  let v := nextOrigin a
  decide (a.src ≠ 0 ∧ v ≠ 0 ∧ a.src ≠ v ∧ bit v a.src = channel)

private def leaves (channel : Bool) (a : Arc) : Bool :=
  let v := a.src
  let t := nextOrigin a
  decide (v ≠ 0 ∧ t ≠ 0 ∧ v ≠ t ∧ bit v t ≠ channel)

private def accepted (channel : Bool) : Finset Walk :=
  walks.filter (fun w => enters channel w.1.2 && leaves channel w.2.1)

/-- Only the middle cut has two channels. The entrance gate depends just on
    the second arc and the exit gate just on the third arc. -/
noncomputable def twoChannelPoly : MvPolynomial Var ℂ :=
  (∑ w ∈ accepted false, monomial (exponent w) 1) +
   ∑ w ∈ accepted true, monomial (exponent w) 1

private def permSig (σ : Equiv.Perm V) (e : Var) : ℕ := if σ e.2 = e.1 then 1 else 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private theorem accepted_signatures :
    (accepted false).val.map signature + (accepted true).val.map signature =
      (Finset.univ : Finset (Equiv.Perm V)).val.map permSig := by decide

/-- The explicit one-bit repair computes the whole four-row permanent. -/
theorem two_channels_suffice : twoChannelPoly = PEqualNP.Gct.permPoly ℂ 4 := by
  let term (f : Var → ℕ) : MvPolynomial Var ℂ := monomial (Finsupp.equivFunOnFinite.symm f) 1
  have hw (w : Walk) : term (signature w) = monomial (exponent w) 1 := by
    have he : Finsupp.equivFunOnFinite.symm (signature w) = exponent w := by
      ext v
      exact (exponent_apply w v).symm
    simp [term,he]
  have hp (σ : Equiv.Perm V) : term (permSig σ) = monomial (permExp σ) 1 := by
    have he : Finsupp.equivFunOnFinite.symm (permSig σ) = permExp σ := by
      ext v
      exact (permExp_apply σ v).symm
    simp [term,he]
  have h := congrArg (fun m : Multiset (Var → ℕ) => (m.map term).sum) accepted_signatures
  simpa [twoChannelPoly, PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply,
    perm_term, Function.comp_def, hw, hp] using h

end GctFrontier.ClowMoments
