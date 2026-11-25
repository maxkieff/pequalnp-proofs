import PEqualNP.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.ZMod.Basic

/-! Sharp order seven for the common-root case of L-gct-234. At a common
nonzero root the first five normalized Euler moments of a binomial cube have
integer center and squared width. A relation at three distinct centers gives
two simultaneous square equations with an obstruction modulo five. -/

namespace GctFrontier.SparseCubeBoundary

open Polynomial Finset

private theorem square_mod_five : ∀ x y : ZMod 5, x^2 = 3*y^2 → x=0 ∧ y=0 := by decide

private theorem five_divides (x y u v : ℤ) (h : x^2=8*y^2+5*u+5*v) :
    (5 : ℤ) ∣ x ∧ (5 : ℤ) ∣ y := by
  have hh := congrArg (Int.castRingHom (ZMod 5)) h
  simp only [map_pow,map_add,map_mul, map_ofNat, Int.coe_castRingHom] at hh
  have eq : (x : ZMod 5)^2 = 3*(y : ZMod 5)^2 := by
    simpa only [show (8 : ZMod 5) = 3 by decide, show (5 : ZMod 5) = 0 by decide,
      zero_mul,add_zero] using hh
  obtain ⟨hx,hy⟩ := square_mod_five _ _ eq
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd x 5).mp hx,
    (ZMod.intCast_zmod_eq_zero_iff_dvd y 5).mp hy⟩

private theorem square_descent (p q x y : ℤ) (hp : p ≠ 0)
    (hx : x^2=8*p^2+5*p*q+5*q^2) (hy : y^2=5*p^2+5*p*q+8*q^2) : False := by
  induction hn : p.natAbs using Nat.strong_induction_on generalizing p q x y with
  | ind n ih =>
    obtain ⟨⟨x',ex⟩,⟨p',ep⟩⟩ := five_divides x p (p*q) (q^2) (by linear_combination hx)
    obtain ⟨⟨y',ey⟩,⟨q',eq⟩⟩ := five_divides y q (p*q) (p^2) (by linear_combination hy)
    subst x; subst p; subst y; subst q
    have hp' : p' ≠ 0 := by intro hz; simp [hz] at hp
    have hs : 0 < p'.natAbs := Int.natAbs_pos.mpr hp'
    have hlt : p'.natAbs < n := by
      rw [← hn, Int.natAbs_mul]
      change p'.natAbs < 5*p'.natAbs
      omega
    apply ih p'.natAbs hlt p' q' x' y' hp' _ _ rfl
    · nlinarith only [hx]
    · nlinarith only [hy]

private noncomputable def moment (u v : ℝ) : Fin 5 → ℝ :=
  ![1, u, u^2+v, u^3+3*u*v, u^4+6*u^2*v+13/5*v^2]

private theorem translate (a b c u A w B z V t : ℝ)
    (h : ∀ j, a*moment u A j+b*moment w B j+c*moment z V j=0) :
    ∀ j, a*moment (u+t) A j+b*moment (w+t) B j+c*moment (z+t) V j=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  intro j
  fin_cases j <;> norm_num [moment] at *
  · linear_combination h0
  · linear_combination t*h0+h1
  · linear_combination t^2*h0+2*t*h1+h2
  · linear_combination t^3*h0+3*t^2*h1+3*t*h2+h3
  · linear_combination t^4*h0+4*t^3*h1+6*t^2*h2+4*t*h3+h4

private theorem lattice_obstruction (p q x y z : ℤ) (hp : p≠0) (hq : q≠0) (ht : p+q≠0)
    (h : ∀ j, (p:ℝ)*moment (3*q) ((x:ℝ)^2) j + (q:ℝ)*moment (-3*p) ((y:ℝ)^2) j =
      ((p:ℝ)+q)*moment 0 ((z:ℝ)^2) j) : False := by
  let P := (p:ℝ)
  let Q := (q:ℝ)
  let A := (x:ℝ)^2
  let B := (y:ℝ)^2
  let V := (z:ℝ)^2
  have hp' : P ≠ 0 := by dsimp [P]; exact_mod_cast hp
  have hq' : Q ≠ 0 := by dsimp [Q]; exact_mod_cast hq
  have ht' : P+Q ≠ 0 := by dsimp [P,Q]; exact_mod_cast ht
  change ∀ j, P*moment (3*Q) A j+Q*moment (-3*P) B j=(P+Q)*moment 0 V j at h
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  norm_num [moment] at h2 h3 h4
  have d : A = B+3*(P^2-Q^2) := by
    apply mul_left_cancel₀ (mul_ne_zero hp' hq')
    linear_combination h3/9
  have e : V = B+3*P^2+6*P*Q := by
    apply mul_left_cancel₀ ht'
    rw [d] at h2
    linear_combination -h2
  have f : B=5*P^2+5*P*Q+8*Q^2 := by
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hp' hq') ht')
    rw [d,e] at h4
    linear_combination (5/36 : ℝ)*h4
  have g : A=8*P^2+5*P*Q+5*Q^2 := by linear_combination d+f
  dsimp [A,B,P,Q] at f g
  apply square_descent p q x y hp
  · exact_mod_cast g
  · exact_mod_cast f

/-- For two nonzero weights the first three moments determine both parameters. -/
private theorem two (a b : ℝ) (u w A B : ℤ) (G : ℤ → ℤ → ℝ)
    (h : ∀ j, a*moment (3*u) A j+b*moment (3*w) B j=0) :
    a*G u A+b*G w B=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  norm_num [moment] at h0 h1 h2
  by_cases ha : a=0
  · have hb : b=0 := by linarith
    simp [ha,hb]
  have eu : (u:ℝ)=(w:ℝ) := by
    apply mul_left_cancel₀ ha
    linear_combination h1/3 - (w:ℝ)*h0
  have eu' : u=w := by exact_mod_cast eu
  subst w
  have ev : (A:ℝ)=(B:ℝ) := by
    apply mul_left_cancel₀ ha
    linear_combination h2 - ((3*(u:ℝ))^2+(B:ℝ))*h0
  have ev' : A=B := by exact_mod_cast ev
  subst B
  linear_combination G u A*h0

private theorem three (a b c : ℝ) (u w z x y v : ℤ) (G : ℤ → ℤ → ℝ)
    (h : ∀ j, a*moment (3*u) ((x:ℝ)^2) j+b*moment (3*w) ((y:ℝ)^2) j+
      c*moment (3*z) ((v:ℝ)^2) j=0) :
    a*G u (x^2)+b*G w (y^2)+c*G z (v^2)=0 := by
  by_cases ha : a=0
  · subst a
    simp only [zero_mul,zero_add] at h ⊢
    apply two b c w z (y^2) (v^2) G
    simpa only [Int.cast_pow] using h
  by_cases hb : b=0
  · subst b
    simp only [zero_mul,add_zero] at h ⊢
    apply two a c u z (x^2) (v^2) G
    simpa only [Int.cast_pow] using h
  by_cases hc : c=0
  · subst c
    simp only [zero_mul,add_zero] at h ⊢
    apply two a b u w (x^2) (y^2) G
    simpa only [Int.cast_pow] using h
  have h0 := h 0
  norm_num [moment] at h0
  let p := z-w
  let q := u-z
  have hcen (j : Fin 5) :
      a*moment (3*(q:ℝ)) ((x:ℝ)^2) j+b*moment (-3*(p:ℝ)) ((y:ℝ)^2) j+
      c*moment 0 ((v:ℝ)^2) j=0 := by
    have hz := translate _ _ _ _ _ _ _ _ _ (-(3*(z:ℝ))) h j
    have eu : 3*(u:ℝ) + -(3*(z:ℝ)) = 3*(q:ℝ) := by dsimp [q]; push_cast; ring
    have ew : 3*(w:ℝ) + -(3*(z:ℝ)) = -3*(p:ℝ) := by dsimp [p]; push_cast; ring
    simpa only [eu,ew,add_neg_cancel] using hz
  have h1 := hcen 1
  norm_num [moment] at h1
  have bal : a*(q:ℝ)=b*(p:ℝ) := by linear_combination h1/3
  by_cases e : u=w
  · have eq : q= -p := by dsimp [p,q]; omega
    have eq' : (q:ℝ)= -(p:ℝ) := by exact_mod_cast eq
    rw [eq'] at bal
    have cp : c*(p:ℝ)=0 := by linear_combination (p:ℝ)*h0+bal
    have p0 : p=0 := by exact_mod_cast (mul_eq_zero.mp cp).resolve_left hc
    have z0 : z=w := sub_eq_zero.mp p0
    have q0 : q=0 := by rw [eq,p0,neg_zero]
    simp only [p0,q0,Int.cast_zero,mul_zero] at hcen
    have h2 := hcen 2
    have h4 := hcen 4
    norm_num [moment] at h2 h4
    let X := (x:ℝ)^2
    let Y := (y:ℝ)^2
    let Z := (v:ℝ)^2
    change a*X+b*Y+c*Z=0 at h2
    have hh4 : a*X^2+b*Y^2+c*Z^2=0 := by
      dsimp [X,Y,Z]
      linear_combination (5/13 : ℝ)*h4
    have f : a*((X-Y)*(X-Z))=0 := by linear_combination hh4-(Y+Z)*h2+Y*Z*h0
    have ef := (mul_eq_zero.mp ((mul_eq_zero.mp f).resolve_left ha))
    have XZ : X=Z := by
      rcases ef with xy | xz
      · have xy' := sub_eq_zero.mp xy
        rw [xy'] at h2
        apply sub_eq_zero.mp
        rw [xy']
        apply (mul_eq_zero.mp (show c*(Y-Z)=0 by linear_combination Y*h0-h2)).resolve_left hc
      · exact sub_eq_zero.mp xz
    have YZ : Y=Z := by
      rw [XZ] at h2
      apply mul_left_cancel₀ hb
      linear_combination h2-Z*h0
    dsimp [X,Y,Z] at XZ YZ
    have ex : x^2=v^2 := by exact_mod_cast XZ
    have ey : y^2=v^2 := by exact_mod_cast YZ
    rw [e,← z0,ex,ey]
    linear_combination G z (v^2)*h0
  · exfalso
    have ht : p+q≠0 := by dsimp [p,q]; omega
    have hp : p≠0 := by
      intro h0p
      have hq := (mul_eq_zero.mp (show a*(q:ℝ)=0 by simpa [h0p] using bal)).resolve_left ha
      have hq' : q=0 := by exact_mod_cast hq
      exact ht (by rw [h0p,hq',add_zero])
    have hq : q≠0 := by
      intro h0q
      have h0p := (mul_eq_zero.mp (show b*(p:ℝ)=0 by simpa [h0q] using bal.symm)).resolve_left hb
      exact hp (by exact_mod_cast h0p)
    apply lattice_obstruction p q x y v hp hq ht
    intro j
    apply mul_left_cancel₀ ha
    linear_combination (p:ℝ)*(hcen j) +
      (moment (-3*(p:ℝ)) ((y:ℝ)^2) j - moment 0 ((v:ℝ)^2) j)*bal -
      (p:ℝ)*moment 0 ((v:ℝ)^2) j*h0

/-- Evaluation at one after n applications of the Euler operator X d/dX. -/
private noncomputable def euler : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  (LinearMap.mulLeft ℝ X).comp derivative

private noncomputable def jet : ℕ → ℝ[X] →ₗ[ℝ] ℝ
  | 0 => Polynomial.leval 1
  | n+1 => (jet n).comp euler

private theorem jet_mono (n e : ℕ) (c : ℝ) : jet n (monomial e c) = c*(e:ℝ)^n := by
  induction n generalizing c with
  | zero => simp [jet, Polynomial.leval_apply]
  | succ n ih =>
    change jet n (X * (monomial e c).derivative) = _
    have hd : X * (monomial e c).derivative = monomial e (c*(e:ℝ)) := by
      cases e with
      | zero => simp
      | succ e => simp [X_mul_monomial]
    rw [hd,ih,pow_succ]
    ring

private theorem jet_power (n e : ℕ) : jet n (X^e) = (e:ℝ)^n := by
  simpa only [← C_mul_X_pow_eq_monomial, C_1, one_mul] using jet_mono n e 1

private theorem jet_scalar (n : ℕ) (c : ℝ) (p : ℝ[X]) :
    jet n (C c * p) = c*jet n p := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

private theorem jet_dvd (n : ℕ) (p : ℝ[X]) (hd : (X-1)^(n+1) ∣ p) : jet n p = 0 := by
  induction n generalizing p with
  | zero =>
    obtain ⟨r,hr⟩ := hd
    simp [jet, Polynomial.leval_apply, hr]
  | succ n ih =>
    change jet n (X*p.derivative) = 0
    apply ih
    have hh := Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd hd
    exact dvd_mul_of_dvd_right (by simpa using hh) X

private theorem jet_cube (n a b : ℕ) :
    jet n ((X^a-X^b)^3) =
      ((a:ℝ)+a+a)^n-3*((a:ℝ)+a+b)^n+3*((a:ℝ)+b+b)^n-((b:ℝ)+b+b)^n := by
  have he : ((X:ℝ[X])^a-X^b)^3 =
      X^(a+a+a)-C 3*X^(a+a+b)+C 3*X^(a+b+b)-X^(b+b+b) := by
    simp only [pow_add, map_ofNat]
    ring
  simp only [he,map_sub,map_add,jet_scalar,jet_power,Nat.cast_add]

private def factor (j : Fin 5) : ℕ := ![48,192,480,960,1680] j

private theorem difference (a b : ℕ) (j : Fin 5) :
    (2:ℝ)^(j.val+3)*jet (j.val+3) ((X^a-X^b)^3) =
      (factor j:ℝ)*((a:ℝ)-b)^3 * moment (3*((a:ℝ)+b)) (((a:ℝ)-b)^2) j := by
  rw [jet_cube]
  fin_cases j <;> norm_num [factor,moment] <;> ring

private theorem form_at_one (p : ℝ[X]) (hs : p.support.card ≤ 2) (hr : p.eval 1=0) :
    ∃ (a b : ℕ), b < a ∧ ∃ t : ℝ, p = C t * (X^a-X^b) := by
  obtain ⟨T,hT,h2⟩ := Infinite.exists_superset_card_eq p.support 2 hs
  obtain ⟨u,v,huv,et⟩ := Finset.card_eq_two.mp h2
  have hp : p = monomial u (p.coeff u) + monomial v (p.coeff v) := by
    calc
      p = ∑ j ∈ p.support, monomial j (p.coeff j) := p.as_sum_support
      _ = ∑ j ∈ T, monomial j (p.coeff j) := Finset.sum_subset hT (fun j _ hj => by
        simp [Polynomial.notMem_support_iff.mp hj])
      _ = _ := by rw [et]; simp [huv]
  have hsum : p.coeff u+p.coeff v=0 := by
    have hh := congrArg (fun f : ℝ[X] => f.eval 1) hp
    simpa [hr,eq_comm] using hh
  rcases lt_or_gt_of_ne huv with h | h
  · refine ⟨v,u,h,p.coeff v, hp.trans ?_⟩
    rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]
    rw [show p.coeff u = -(p.coeff v) by linarith, map_neg]
    ring
  · refine ⟨u,v,h,p.coeff u, hp.trans ?_⟩
    rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]
    rw [show p.coeff v = -(p.coeff u) by linarith, map_neg]
    ring

private theorem binomial_bound (a b : Fin 3 → ℕ) (hab : ∀ i, b i < a i) (w : Fin 3 → ℝ) :
    (∑ i, C (w i) * ((X:ℝ[X])^(a i)-X^(b i))^3).rootMultiplicity 1 ≤ 7 := by
  let F := ∑ i, C (w i) * ((X:ℝ[X])^(a i)-X^(b i))^3
  change F.rootMultiplicity 1 ≤ 7
  by_contra! large
  have hn : F≠0 := by intro h; simp [h] at large
  have hd : ((X:ℝ[X])-1)^8 ∣ F := by
    simpa using (Polynomial.le_rootMultiplicity_iff hn).mp (show 8 ≤ F.rootMultiplicity 1 by omega)
  let L (i : Fin 3) : ℤ := (a i:ℤ)+b i
  let D (i : Fin 3) : ℤ := (a i:ℤ)-b i
  let W (i : Fin 3) : ℝ := w i*(D i:ℝ)^3
  have dpos (i) : 0 < D i := by dsimp [D]; exact_mod_cast (sub_pos.mpr (show (b i:ℤ)<a i by exact_mod_cast hab i))
  have heights (j : Fin 5) :
      (∑ i, W i*moment (3*(L i:ℝ)) ((D i:ℝ)^2) j)=0 := by
    have hz := jet_dvd (j.val+3) F ((pow_dvd_pow _ (show j.val+3+1≤8 by omega)).trans hd)
    have eq (i : Fin 3) : (2:ℝ)^(j.val+3)*jet (j.val+3) ((X^(a i)-X^(b i))^3) =
        (factor j:ℝ)*(D i:ℝ)^3*moment (3*(L i:ℝ)) ((D i:ℝ)^2) j := by
      simpa only [L,D,Int.cast_add,Int.cast_sub,Int.cast_natCast] using difference (a i) (b i) j
    have he : (2:ℝ)^(j.val+3)*jet (j.val+3) F =
        (factor j:ℝ)*∑ i, W i*moment (3*(L i:ℝ)) ((D i:ℝ)^2) j := by
      simp only [F,map_sum,jet_scalar,mul_sum]
      apply sum_congr rfl
      intro i _
      dsimp only [W]
      linear_combination w i*eq i
    rw [hz,mul_zero] at he
    have hf : factor j ≠ 0 := by fin_cases j <;> decide
    exact (mul_eq_zero.mp he.symm).resolve_left (by exact_mod_cast hf)
  apply hn
  apply Polynomial.funext
  intro z
  let R (i : Fin 3) := (z^(a i)-z^(b i))^3 / (D i:ℝ)^3
  have compat (i j : Fin 3) (hl : L i=L j) (hd' : (D i)^2=(D j)^2) : R i=R j := by
    have ed : D i=D j := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hd' with t | t
      · exact t
      · linarith [dpos i,dpos j]
    have eab : a i=a j ∧ b i=b j := by dsimp [L,D] at hl ed; omega
    simp only [R,eab.1,eab.2,ed]
  let G (l v : ℤ) : ℝ := if h : ∃ i, L i=l ∧ D i^2=v then R h.choose else 0
  have recov (i : Fin 3) : G (L i) (D i^2)=R i := by
    have hi : ∃ j, L j=L i ∧ D j^2=D i^2 := ⟨i,rfl,rfl⟩
    exact (dite_eq_left hi).trans (compat _ _ hi.choose_spec.1 hi.choose_spec.2)
  have hh := three (W 0) (W 1) (W 2) (L 0) (L 1) (L 2) (D 0) (D 1) (D 2) G
    (fun j => by simpa only [Fin.sum_univ_three] using heights j)
  rw [recov,recov,recov] at hh
  have cancel (i : Fin 3) : W i*R i=w i*(z^(a i)-z^(b i))^3 := by
    have hd' : (D i:ℝ) ≠ 0 := by exact_mod_cast (dpos i).ne'
    dsimp [W,R]
    field_simp [hd']
  rw [cancel,cancel,cancel] at hh
  simpa [F,Fin.sum_univ_three] using hh

/-- Real weights are arbitrary. The same proof applies at a negative nonzero common root. -/
theorem common_root_bound (s : Fin 3 → ℝ) (g : Fin 3 → ℝ[X]) (hs : ∀ i, (g i).support.card≤2)
    (x : ℝ) (hx : x≠0) (hr : ∀ i, (g i).eval x=0) :
    (∑ i, C (s i)*(g i)^3).rootMultiplicity x ≤ 7 := by
  let h (i : Fin 3) := (g i).comp (C x*X)
  have hs' (i) : (h i).support.card ≤ 2 := by
    apply le_trans (Finset.card_le_card (show (h i).support ⊆ (g i).support from ?_)) (hs i)
    intro k hk
    by_contra hn
    apply (Polynomial.mem_support_iff.mp hk)
    simp [h,Polynomial.notMem_support_iff.mp hn]
  have hr' (i) : (h i).eval 1=0 := by simp [h,eval_comp,hr]
  choose a b hab t ht using fun i => form_at_one (h i) (hs' i) (hr' i)
  let F := ∑ i, C (s i)*(g i)^3
  have scale : (F.comp (C x*X)).rootMultiplicity 1 = F.rootMultiplicity x := by
    simpa using Polynomial.rootMultiplicity_comp_C_mul_X_add_C F x 0 1 (isUnit_iff_ne_zero.mpr hx)
  change F.rootMultiplicity x ≤ 7
  rw [← scale]
  have exp : F.comp (C x*X) = ∑ i, C (s i*(t i)^3)*(X^(a i)-X^(b i))^3 := by
    simp only [F, Polynomial.sum_comp, mul_comp, C_comp, pow_comp]
    apply sum_congr rfl
    intro i _
    change C (s i)*(h i)^3 = _
    rw [ht,mul_pow,← map_pow, map_mul]
    ring
  rw [exp]
  exact binomial_bound _ _ hab _

private theorem two_terms (a b : ℕ) (t : ℝ) :
    (C t * ((X : ℝ[X])^a-X^b)).support.card ≤ 2 := by
  apply le_trans (card_le_card (show (C t * ((X : ℝ[X])^a-X^b)).support ⊆ {a,b} from ?_))
    Finset.card_le_two
  intro j hj
  by_contra hn
  have h : j ≠ a ∧ j ≠ b := by simpa using hn
  exact (mem_support_iff.mp hj) (by simp [coeff_C_mul,coeff_X_pow,h.1,h.2])

/-- All three input binomials vanish at one and all three outer signs are positive. -/
theorem common_root_seven :
    ∃ g : Fin 3 → ℝ[X], (∀ i, (g i).support.card ≤ 2 ∧ (g i).eval 1 = 0) ∧
      (∑ i, g i^3) ≠ 0 ∧ (∑ i, g i^3).rootMultiplicity 1 = 7 := by
  let u := (2250 : ℝ) ^ (3 : ℝ)⁻¹
  let v := (9 : ℝ) ^ (3 : ℝ)⁻¹
  have hu : u^3=2250 := Real.rpow_inv_natCast_pow (by norm_num) (by decide : (3 : ℕ)≠0)
  have hv : v^3=9 := Real.rpow_inv_natCast_pow (by norm_num) (by decide : (3 : ℕ)≠0)
  let g : Fin 3 → ℝ[X] := ![C u*(X^3-X^2), C (-5)*(X^4-X^1), C v*(X^5-X^0)]
  have hg (i : Fin 3) : (g i).support.card ≤ 2 ∧ (g i).eval 1=0 := by
    constructor
    · fin_cases i <;> apply two_terms
    · fin_cases i <;> simp [g]
  let F := ∑ i, (g i)^3
  have expr : F = 2250*(X^3-X^2)^3-125*(X^4-X)^3+9*(X^5-1)^3 := by
    have cu : (C u : ℝ[X])^3 = 2250 := by rw [← map_pow,hu,map_ofNat]
    have cv : (C v : ℝ[X])^3 = 9 := by rw [← map_pow,hv,map_ofNat]
    have cm : (C (-5 : ℝ) : ℝ[X])^3 = -125 := by
      rw [← map_pow,show (-5 : ℝ)^3 = -125 by norm_num,map_neg,map_ofNat]
    rw [show F = (C u*(X^3-X^2))^3+(C (-5)*(X^4-X))^3+(C v*(X^5-1))^3 by
      simp [F,g,Fin.sum_univ_three]]
    simp only [mul_pow,cu,cm,cv]
    ring
  have nf : F ≠ 0 := by
    intro h
    have eqn := congrArg (fun p : ℝ[X] => p.eval 2) (expr.symm.trans h)
    norm_num at eqn
  have hd : ((X : ℝ[X])-1)^7 ∣ F := by
    refine ⟨9*X^8+63*X^7+252*X^6+631*X^5+1015*X^4+631*X^3+252*X^2+63*X+9, ?_⟩
    rw [expr]
    ring
  have lo : 7 ≤ F.rootMultiplicity 1 := (Polynomial.le_rootMultiplicity_iff nf).mpr (by simpa using hd)
  have hi := common_root_bound (fun _ => 1) g (fun i => (hg i).1) 1 one_ne_zero (fun i => (hg i).2)
  exact ⟨g,hg,nf,le_antisymm (by simpa only [C_1,one_mul,F] using hi) lo⟩

end GctFrontier.SparseCubeBoundary

theorem PEqualNP.Research.SparseCubeBoundary :
    (∀ (s : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ), (∀ i, (g i).support.card ≤ 2) →
      ∀ x : ℝ, x ≠ 0 → (∀ i, (g i).eval x = 0) →
      Polynomial.rootMultiplicity x (∑ i, Polynomial.C (s i)*(g i)^3) ≤ 7) ∧
    (∃ g : Fin 3 → Polynomial ℝ, (∀ i, (g i).support.card ≤ 2 ∧ (g i).eval 1 = 0) ∧
      (∑ i, g i^3) ≠ 0 ∧ Polynomial.rootMultiplicity 1 (∑ i, g i^3) = 7) :=
  ⟨GctFrontier.SparseCubeBoundary.common_root_bound, GctFrontier.SparseCubeBoundary.common_root_seven⟩
