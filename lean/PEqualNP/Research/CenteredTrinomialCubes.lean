import PEqualNP.Outside.L_gct_234
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! A common double root for three trinomials with the same sum of exponents.
The shifted Euler moments are those in the project's checked binomial theorem. -/

namespace GctFrontier.CenteredTrinomialCubes

open Polynomial Finset PEqualNP.Outside.L_gct_234.SparseCubes

private def convolution (f g : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ range (n+1), f j * g (n-j) * (n.choose j : ℝ)

private theorem moment_monomial (u r c : ℝ) (k n : ℕ) :
    moment u r n (monomial k c) = c*r^k*((k:ℝ)-u)^n := by
  simpa only [C_mul_X_pow_eq_monomial] using moment_term u r c k n

private theorem moment_product (u v r : ℝ) (p q : ℝ[X]) (n : ℕ) :
    moment (u+v) r n (p*q) =
      convolution (fun j => moment u r j p) (fun j => moment v r j q) n := by
  induction p using Polynomial.induction_on' with
  | add p s hp hs =>
    simp only [add_mul,moment_add,hp,hs,convolution,Finset.sum_add_distrib]
  | monomial k c =>
    induction q using Polynomial.induction_on' with
    | add p s hp hs =>
      simp only [mul_add,moment_add,hp,hs,convolution,add_mul,Finset.sum_add_distrib]
    | monomial l d =>
      simp only [monomial_mul_monomial,moment_monomial,convolution,Nat.cast_add,pow_add]
      rw [show (k:ℝ)+l-(u+v)=((k:ℝ)-u)+((l:ℝ)-v) by ring, add_pow,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

private theorem scale_convolution (a b : ℝ) (f g : ℕ → ℝ) (n : ℕ) :
    convolution (fun j => a*f j) (fun j => b*g j) n = a*b*convolution f g n := by
  unfold convolution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem moment_shift (u v r : ℝ) (p : ℝ[X]) (n : ℕ) :
    moment v r n p = convolution (fun j => moment u r j p) (fun j => (u-v)^j) n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [moment_add,hp,hq,convolution,add_mul,Finset.sum_add_distrib]
  | monomial k c =>
    simp only [moment_monomial,convolution]
    rw [show (k:ℝ)-v=((k:ℝ)-u)+(u-v) by ring,add_pow,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

private def sequence (A B : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n+3 => A*sequence A B (n+1)+B*sequence A B n

private def profile (A B : ℝ) : ℕ → ℝ :=
  convolution (convolution (sequence A B) (sequence A B)) (sequence A B)

private theorem normalized (p : ℝ[X]) (u r A B : ℝ) (h0 : p.eval r=0)
    (h1 : p.derivative.eval r=0)
    (he : ∀ k ∈ p.support, ((k:ℝ)-u)^3=A*((k:ℝ)-u)+B) :
    ∀ n, moment u r n p = moment u r 2 p * sequence A B n := by
  have stepMoment (n : ℕ) : moment u r (n+3) p = A*moment u r (n+1) p+B*moment u r n p := by
    simp only [moment_eq_support_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [pow_add,he k hk,pow_succ]
    ring
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | _ | _ | n
    · simp [moment,sequence,h0]
    · simp [moment,euler,sequence,h0,h1]
    · simp [sequence]
    · rw [stepMoment,ih (n+1) (by omega),ih n (by omega),sequence]
      ring

private theorem normalized_cube (p : ℝ[X]) (u r A B : ℝ)
    (h : ∀ n, moment u r n p = moment u r 2 p * sequence A B n) (n : ℕ) :
    moment (u+u+u) r n (p^3) = (moment u r 2 p)^3 * profile A B n := by
  have square (j : ℕ) : moment (u+u) r j (p*p) = (moment u r 2 p * moment u r 2 p) *
      convolution (sequence A B) (sequence A B) j := by
    rw [moment_product u u r p p j,funext h]
    exact scale_convolution ..
  rw [show p^3=p*p*p by ring, moment_product (u+u) u,funext square,funext h,scale_convolution]
  unfold profile
  ring

set_option maxHeartbeats 2000000 in
private theorem profile_values (A B : ℝ) :
    profile A B 6 = 90 ∧ profile A B 8 = 1260*A ∧ profile A B 9 = 2268*B ∧
    profile A B 10 = 13230*A^2 ∧ profile A B 12 = 126720*A^3+58806*B^2 := by
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    norm_num [profile,convolution,Finset.sum_range_succ,sequence,Nat.choose] <;> ring

private theorem initial_moments (p : ℝ[X]) (u r A B : ℝ)
    (h : ∀ n, moment u r n p = moment u r 2 p * sequence A B n) :
    moment 0 r 6 (p^3)=90*(moment u r 2 p)^3 ∧
    moment 0 r 7 (p^3)=1890*u*(moment u r 2 p)^3 := by
  have step (n : ℕ) := moment_shift (u+u+u) 0 r (p^3) n
  rw [funext (normalized_cube p u r A B h)] at step
  constructor
  · rw [step 6]
    norm_num [profile,convolution,Finset.sum_range_succ,sequence,Nat.choose]
    ring
  · rw [step 7]
    norm_num [profile,convolution,Finset.sum_range_succ,sequence,Nat.choose]
    ring

private theorem pair_equal (p q r x y z : ℝ) (hp : p≠0) (hq : q≠0)
    (h0 : p+q+r=0) (h1 : p*x+q*y+r*z=0) (h2 : p*x^2+q*y^2+r*z^2=0) : x=y := by
  have e0 : p+q= -r := by linarith
  have e1 : p*x+q*y= -(r*z) := by linarith
  have e2 : p*x^2+q*y^2= -(r*z^2) := by linarith
  have hh : p*q*(x-y)^2=0 := by
    calc
      _ = (p+q)*(p*x^2+q*y^2)-(p*x+q*y)^2 := by ring
      _ = 0 := by rw [e0,e1,e2]; ring
  exact sub_eq_zero.mp (pow_eq_zero_iff (by decide : 2≠0) |>.mp
    ((mul_eq_zero.mp hh).resolve_left (mul_ne_zero hp hq)))

private theorem concentrated (w v : Fin 3 → ℝ) (h0 : ∑ i, w i=0)
    (h1 : ∑ i, w i*v i=0) (h2 : ∑ i, w i*(v i)^2=0) :
    ∃ a : ℝ, ∀ i, w i=0 ∨ v i=a := by
  simp only [Fin.sum_univ_three] at h0 h1 h2
  by_cases hw : w 0=0
  · refine ⟨v 1,?_⟩
    intro i
    fin_cases i
    · exact Or.inl hw
    · exact Or.inr rfl
    · by_cases hz : w 2=0
      · exact Or.inl hz
      right
      apply pair_equal (w 2) (w 1) (w 0) (v 2) (v 1) (v 0) hz (by intro e; rw [hw,e] at h0; apply hz; linarith)
        <;> linarith
  · refine ⟨v 0,?_⟩
    intro i
    by_cases hi : w i=0
    · exact Or.inl hi
    right
    fin_cases i
    · rfl
    · apply pair_equal (w 1) (w 0) (w 2) (v 1) (v 0) (v 2) hi hw <;> linarith
    · apply pair_equal (w 2) (w 0) (w 1) (v 2) (v 0) (v 1) hi hw <;> linarith

private theorem annihilates (w A B : Fin 3 → ℝ)
    (hh : ∀ n ≤ 12, ∑ i, w i*profile (A i) (B i) n=0) :
    ∀ n, ∑ i, w i*profile (A i) (B i) n=0 := by
  have h6 := hh 6 (by decide)
  have h8 := hh 8 (by decide)
  have h9 := hh 9 (by decide)
  have h10 := hh 10 (by decide)
  have h12 := hh 12 (by decide)
  simp only [Fin.sum_univ_three,fun a b => (profile_values a b).1] at h6
  simp only [Fin.sum_univ_three,fun a b => (profile_values a b).2.1] at h8
  simp only [Fin.sum_univ_three,fun a b => (profile_values a b).2.2.1] at h9
  simp only [Fin.sum_univ_three,fun a b => (profile_values a b).2.2.2.1] at h10
  simp only [Fin.sum_univ_three,fun a b => (profile_values a b).2.2.2.2] at h12
  have h0 : ∑ i, w i=0 := by rw [Fin.sum_univ_three]; linarith
  obtain ⟨a,ha⟩ := concentrated w A h0
    (by rw [Fin.sum_univ_three]; linear_combination h8/1260)
    (by rw [Fin.sum_univ_three]; linear_combination h10/13230)
  have hA3 : ∑ i, w i*(A i)^3=0 := by
    calc
      _ = ∑ i, w i*a^3 := Finset.sum_congr rfl (fun i _ => by rcases ha i with h|h <;> simp [h])
      _ = 0 := by rw [← Finset.sum_mul,h0,zero_mul]
  rw [Fin.sum_univ_three] at hA3
  obtain ⟨b,hb⟩ := concentrated w B h0
    (by rw [Fin.sum_univ_three]; linear_combination h9/2268)
    (by rw [Fin.sum_univ_three]; linear_combination (h12-126720*hA3)/58806)
  intro n
  calc
    _ = ∑ i, w i*profile a b n := Finset.sum_congr rfl (fun i _ => by
      rcases ha i with h|h <;> rcases hb i with j|j <;> simp [h,j])
    _ = 0 := by rw [← Finset.sum_mul,h0,zero_mul]

/-- The common centered characteristic cubic is allowed to vary in its two coefficients. -/
theorem characteristic_bound (g : Fin 3 → ℝ[X]) (s A B : Fin 3 → ℝ) (u r : ℝ) (hr : r≠0)
    (hz : ∀ i, (g i).eval r=0 ∧ (g i).derivative.eval r=0)
    (hs : ∀ i, ∀ k ∈ (g i).support, ((k:ℝ)-u)^3=A i*((k:ℝ)-u)+B i) :
    (∑ i, C (s i)*(g i)^3).rootMultiplicity r ≤ 12 := by
  let F := ∑ i, C (s i)*(g i)^3
  let w (i : Fin 3) := s i*(moment u r 2 (g i))^3
  have momentF (n : ℕ) : moment (u+u+u) r n F = ∑ i, w i*profile (A i) (B i) n := by
    simp only [F,moment_sum,moment_C_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [normalized_cube _ u r (A i) (B i) (normalized _ _ _ _ _ (hz i).1 (hz i).2 (hs i))]
    dsimp only [w]
    ring
  change F.rootMultiplicity r ≤ 12
  by_contra! large
  have low (n : ℕ) (hn : n≤12) := moment_eq_zero_of_lt_rootMultiplicity (u+u+u) r F (lt_of_le_of_lt hn large)
  have alln := annihilates w A B (fun n hn => (momentF n).symm.trans (low n hn))
  have hF := eq_zero_of_moments (u+u+u) r hr F (fun n _ => (momentF n).trans (alln n))
  simp [hF] at large

theorem common_sum_bound (g : Fin 3 → ℝ[X]) (s : Fin 3 → ℝ) (e f h : Fin 3 → ℕ)
    (N : ℕ) (hN : ∀ i, e i+f i+h i=N) (he : ∀ i, (g i).support ⊆ {e i,f i,h i})
    (r : ℝ) (hr : r≠0) (hz : ∀ i, (g i).eval r=0 ∧ (g i).derivative.eval r=0) :
    (∑ i, C (s i)*(g i)^3).rootMultiplicity r ≤ 12 := by
  let u := (N:ℝ)/3
  let a (i : Fin 3) := (e i:ℝ)-u
  let b (i : Fin 3) := (f i:ℝ)-u
  let c (i : Fin 3) := (h i:ℝ)-u
  have sum0 (i : Fin 3) : a i+b i+c i=0 := by
    have hn : (e i:ℝ)+f i+h i=N := by exact_mod_cast hN i
    dsimp [a,b,c,u]
    linarith
  apply characteristic_bound g s (fun i => -(a i*b i+b i*c i+c i*a i))
    (fun i => a i*b i*c i) u r hr hz
  intro i k hk
  have hx := he i hk
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl|rfl|rfl
  · change (a i)^3=_
    linear_combination (a i)^2*sum0 i
  · change (b i)^3=_
    linear_combination (b i)^2*sum0 i
  · change (c i)^3=_
    linear_combination (c i)^2*sum0 i

private theorem two_centers (w m : Fin 3 → ℝ) (h0 : ∑ i, w i=0)
    (h1 : ∑ i, w i*m i=0) (rep : ¬Function.Injective m) :
    ∃ a : ℝ, ∀ i, w i=0 ∨ m i=a := by
  simp only [Fin.sum_univ_three] at h0 h1
  have duplicate : m 0=m 1 ∨ m 0=m 2 ∨ m 1=m 2 := by
    by_contra! h
    apply rep
    intro i j e
    fin_cases i <;> fin_cases j <;> simp_all
  rcases duplicate with e | e | e
  · refine ⟨m 0,?_⟩
    have eqn : w 2*(m 2-m 0)=0 := by rw [← e] at h1; linear_combination h1-m 0*h0
    intro i
    fin_cases i
    · exact Or.inr rfl
    · exact Or.inr e.symm
    · exact (mul_eq_zero.mp eqn).imp_right sub_eq_zero.mp
  · refine ⟨m 0,?_⟩
    have eqn : w 1*(m 1-m 0)=0 := by rw [← e] at h1; linear_combination h1-m 0*h0
    intro i
    fin_cases i
    · exact Or.inr rfl
    · exact (mul_eq_zero.mp eqn).imp_right sub_eq_zero.mp
    · exact Or.inr e.symm
  · refine ⟨m 1,?_⟩
    have eqn : w 0*(m 0-m 1)=0 := by rw [← e] at h1; linear_combination h1-m 1*h0
    intro i
    fin_cases i
    · exact (mul_eq_zero.mp eqn).imp_right sub_eq_zero.mp
    · exact Or.inr rfl
    · exact Or.inr e.symm

/-- Already a single coincidence between exponent sums suffices. -/
theorem repeated_sum_bound (g : Fin 3 → ℝ[X]) (s : Fin 3 → ℝ) (e f h : Fin 3 → ℕ)
    (he : ∀ i, (g i).support ⊆ {e i,f i,h i})
    (rep : ¬Function.Injective (fun i => e i+f i+h i))
    (r : ℝ) (hr : r≠0) (hz : ∀ i, (g i).eval r=0 ∧ (g i).derivative.eval r=0) :
    (∑ i, C (s i)*(g i)^3).rootMultiplicity r ≤ 12 := by
  let F := ∑ i, C (s i)*(g i)^3
  let u (i : Fin 3) := ((e i:ℝ)+f i+h i)/3
  let a (i : Fin 3) := (e i:ℝ)-u i
  let b (i : Fin 3) := (f i:ℝ)-u i
  let c (i : Fin 3) := (h i:ℝ)-u i
  let A (i : Fin 3) := -(a i*b i+b i*c i+c i*a i)
  let B (i : Fin 3) := a i*b i*c i
  let w (i : Fin 3) := s i*(moment (u i) r 2 (g i))^3
  have shape (i : Fin 3) (k : ℕ) (hk : k ∈ (g i).support) :
      ((k:ℝ)-u i)^3=A i*((k:ℝ)-u i)+B i := by
    have hx := he i hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl <;> dsimp [u,a,b,c,A,B] <;> ring
  have normed (i : Fin 3) := normalized (g i) (u i) r (A i) (B i) (hz i).1 (hz i).2 (shape i)
  have ini (i : Fin 3) := initial_moments (g i) (u i) r (A i) (B i) (normed i)
  change F.rootMultiplicity r ≤ 12
  by_contra! large
  have m6 := moment_eq_zero_of_lt_rootMultiplicity 0 r F (show 6 < F.rootMultiplicity r by omega)
  have m7 := moment_eq_zero_of_lt_rootMultiplicity 0 r F (show 7 < F.rootMultiplicity r by omega)
  simp only [F,Fin.sum_univ_three,moment_add,moment_C_mul,fun i => (ini i).1] at m6
  simp only [F,Fin.sum_univ_three,moment_add,moment_C_mul,fun i => (ini i).2] at m7
  have h0 : ∑ i, w i=0 := by rw [Fin.sum_univ_three]; dsimp only [w]; linear_combination m6/90
  have h1 : ∑ i, w i*u i=0 := by rw [Fin.sum_univ_three]; dsimp only [w]; linear_combination m7/1890
  have hrep : ¬Function.Injective u := by
    intro hinj
    apply rep
    intro i j hij
    apply hinj
    dsimp only [u]
    congr 1
    exact_mod_cast hij
  obtain ⟨v,hv⟩ := two_centers w u h0 h1 hrep
  let g' (i : Fin 3) : ℝ[X] := if w i=0 then 0 else g i
  have hz' (i : Fin 3) : (g' i).eval r=0 ∧ (g' i).derivative.eval r=0 := by
    by_cases hi : w i=0 <;> simp [g',hi,hz]
  have hs' (i : Fin 3) (k : ℕ) (hk : k ∈ (g' i).support) :
      ((k:ℝ)-v)^3=A i*((k:ℝ)-v)+B i := by
    by_cases hi : w i=0
    · simp [g',hi] at hk
    · rw [← (hv i).resolve_left hi]
      exact shape i k (by simpa [g',hi] using hk)
  have eqF : F=∑ i, C (s i)*(g' i)^3 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : w i=0
    · simp only [g',hi,ite_true,zero_pow (by decide : 3≠0),mul_zero]
      rcases mul_eq_zero.mp hi with hsi | hm
      · simp [hsi]
      · have htwo : moment (u i) r 2 (g i)=0 := (pow_eq_zero_iff (by decide : 3≠0)).mp hm
        have hg := eq_zero_of_moments (u i) r hr (g i) (fun n _ => by
          rw [normed i n,htwo,zero_mul])
        simp [hg]
    · simp [g',hi]
  rw [eqF] at large
  exact (not_lt_of_ge (characteristic_bound g' s A B v r hr hz' hs')) large

private noncomputable def tri (e f h : ℕ) (a b c : ℝ) : ℝ[X] :=
  C a*X^e+C b*X^f+C c*X^h

/-- The three exponent triples have sum 24 and sum of squares 290. -/
theorem attained :
    ∃ (g : Fin 3 → ℝ[X]) (e f h : Fin 3 → ℕ),
      (∀ i, (g i).support ⊆ {e i,f i,h i} ∧ e i+f i+h i=24 ∧
        (g i).eval 1=0 ∧ (g i).derivative.eval 1=0) ∧
      (∑ i, (g i)^3)≠0 ∧ (∑ i, (g i)^3).rootMultiplicity 1=12 := by
  let t := (2 : ℝ)^(3 : ℝ)⁻¹
  have ht : t^3=2 := Real.rpow_inv_natCast_pow (by norm_num) (by decide : (3 : ℕ)≠0)
  let e : Fin 3 → ℕ := ![0,1,3]
  let f : Fin 3 → ℕ := ![11,8,5]
  let h : Fin 3 → ℕ := ![13,15,16]
  let g : Fin 3 → ℝ[X] := ![tri 0 11 13 98 (-637) 539,
    tri 1 8 15 (-143*t) (286*t) (-143*t),tri 3 5 16 539 (-637) 98]
  refine ⟨g,e,f,h,?_,?_⟩
  · intro i
    constructor
    · fin_cases i <;> apply support_trinomial_subset
    refine ⟨?_,?_,?_⟩
    · fin_cases i <;> decide
    · fin_cases i <;> norm_num [g,tri]
      ring
    · fin_cases i <;> norm_num [g,tri,derivative_C_mul,derivative_pow]
      ring
  let F := ∑ i, (g i)^3
  have mid : g 1 = C (-143*t)*(X-2*X^8+X^15) := by
    simp [g,tri,map_mul,map_neg,map_ofNat]
    ring
  have cm : (C (-143*t) : ℝ[X])^3 = -5848414 := by
    rw [← map_pow, mul_pow, ht, show (-143 : ℝ)^3*2 = -5848414 by norm_num,map_neg,map_ofNat]
  have expr : F=117649*(2-13*X^11+11*X^13)^3-5848414*(X-2*X^8+X^15)^3+
      117649*(11*X^3-13*X^5+2*X^16)^3 := by
    rw [show F=g 0^3+g 1^3+g 2^3 from Fin.sum_univ_three _,mid,mul_pow,cm]
    simp [g,tri,map_neg,map_ofNat]
    ring
  let Q : ℝ[X] :=
        941192 + 11294304*X^1 + 73412976*X^2 + 336745474*X^3
         + 1214546112*X^4 + 3654950364*X^5 + 9519369496*X^6 + 21969409098*X^7
         + 45591301392*X^8 + 85859227475*X^9 + 147767730648*X^10 + 233973758811*X^11
         + 343119030904*X^12 + 468976601226*X^13 + 600789791196*X^14 + 724781584254*X^15
         + 826469068152*X^16 + 893220184155*X^17 + 916477221244*X^18 + 893220184155*X^19
         + 826469068152*X^20 + 724781584254*X^21 + 600789791196*X^22 + 468976601226*X^23
         + 343119030904*X^24 + 233973758811*X^25 + 147767730648*X^26 + 85859227475*X^27
         + 45591301392*X^28 + 21969409098*X^29 + 9519369496*X^30 + 3654950364*X^31
         + 1214546112*X^32 + 336745474*X^33 + 73412976*X^34 + 11294304*X^35
         + 941192*X^36
  have hF : F=Q*(X-C 1)^12 := by rw [expr]; dsimp [Q]; rw [C_1]; ring
  have hQ1 : Q.eval 1≠0 := by norm_num [Q]
  have hQ : Q≠0 := by intro hzero; simp [hzero] at hQ1
  change F≠0 ∧ F.rootMultiplicity 1=12
  rw [hF,rootMultiplicity_mul_X_sub_C_pow hQ,rootMultiplicity_eq_zero (p := Q) hQ1,zero_add]
  exact ⟨mul_ne_zero hQ (pow_ne_zero _ (X_sub_C_ne_zero _)),rfl⟩

end GctFrontier.CenteredTrinomialCubes

open Polynomial in
theorem PEqualNP.Research.CenteredTrinomialCubes :
    (∀ (g : Fin 3 → ℝ[X]) (s : Fin 3 → ℝ) (e f h : Fin 3 → ℕ), (∀ i, (g i).support ⊆ {e i,f i,h i}) →
      ¬Function.Injective (fun i => e i+f i+h i) → ∀ r : ℝ, r≠0 →
      (∀ i, (g i).eval r=0 ∧ (g i).derivative.eval r=0) →
      (∑ i, C (s i)*(g i)^3).rootMultiplicity r ≤ 12) ∧
    (∃ (g : Fin 3 → ℝ[X]) (e f h : Fin 3 → ℕ),
      (∀ i, (g i).support ⊆ {e i,f i,h i} ∧ e i+f i+h i=24 ∧
        (g i).eval 1=0 ∧ (g i).derivative.eval 1=0) ∧
      (∑ i, (g i)^3)≠0 ∧ (∑ i, (g i)^3).rootMultiplicity 1=12) :=
  ⟨GctFrontier.CenteredTrinomialCubes.repeated_sum_bound, GctFrontier.CenteredTrinomialCubes.attained⟩
