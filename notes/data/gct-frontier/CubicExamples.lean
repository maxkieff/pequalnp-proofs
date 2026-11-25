import Mathlib.Combinatorics.Nullstellensatz
import PEqualNP.Gct.L002
import PEqualNP.Gct.L006
import PEqualNP.Gct.L007
import PEqualNP.Gct.L010
import PEqualNP.Gct.Helpers.BorderSubst
import PEqualNP.Gct.Helpers.Pointwise

/-! Small cubic-padding instances and interpolation of determinant pencils on sparse rays. -/

namespace GctFrontier.CubicExamples

open MvPolynomial PEqualNP.Gct Filter Topology

private theorem pad_expression {σ : Type} {p : MvPolynomial σ ℂ} {d N : ℕ}
    (h : HasDetExpression p d) (hle : d ≤ N) : HasDetExpression p N := by
  induction hle with
  | refl => exact h
  | step _ ih => exact L002 σ ℂ p _ ih

/-- All nine positive sizes up to the first crossing in the subset construction
    give actual orbit containment at the exponent-three size in the project. -/
theorem small_cubic_containment (m : ℕ) (hm : 1 ≤ m) (h9 : m ≤ 9) :
    paddedPerm ℂ m (m^3) ∈ orbitClosure (detPoly ℂ (m^3 + 1)) := by
  have hsize : 2^m - 1 ≤ m^3 + 1 := by interval_cases m <;> norm_num
  exact L006 m (m^3) (Nat.le_self_pow (by decide) _) (pad_expression (L007 ℂ m hm) hsize)

/-- The nonnegative integer simplex of radius m determines every polynomial of
    total degree at most m over the complex numbers. -/
theorem eq_zero_of_simplex {σ : Type} [Fintype σ] {m : ℕ} (p : MvPolynomial σ ℂ)
    (hd : p.totalDegree ≤ m)
    (hz : ∀ a : σ → ℕ, (∑ i, a i) ≤ m → eval (fun i => (a i : ℂ)) p = 0) : p = 0 := by
  classical
  by_contra hp
  let : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  let s := MonomialOrder.degLex.degree p
  have hs : s.degree = p.totalDegree := degree_degLexDegree
  let castNat : ℕ ↪ ℂ := ⟨Nat.cast, Nat.cast_injective⟩
  let S (i : σ) := (Finset.range (s i + 1)).map castNat
  obtain ⟨x, hx, hne⟩ := combinatorial_nullstellensatz_exists_eval_ne_zero p s
    (mem_support_iff.mp (MonomialOrder.degLex.degree_mem_support hp)) hs.symm S (by simp [S])
  have hnat (i : σ) : ∃ a : ℕ, a ≤ s i ∧ (a : ℂ) = x i := by
    obtain ⟨a, ha, hax⟩ := Finset.mem_map.mp (hx i)
    exact ⟨a, Nat.le_of_lt_succ (Finset.mem_range.mp ha), hax⟩
  choose a ha he using hnat
  have hsum : (∑ i, a i) ≤ m := calc
    _ ≤ ∑ i, s i := Finset.sum_le_sum fun i _ => ha i
    _ = s.degree := (Finsupp.degree_eq_sum s).symm
    _ ≤ m := hs.trans_le hd
  exact hne (funext he ▸ hz a hsum)

/-- Substitution x = t v, with the scalar t kept as a polynomial variable. -/
noncomputable def ray {σ : Type} (v : σ → ℂ) : MvPolynomial σ ℂ →+* Polynomial ℂ :=
  eval₂Hom Polynomial.C (fun i => Polynomial.C (v i) * Polynomial.X)

private theorem eval_ray {σ : Type} (v : σ → ℂ) (t : ℂ) (p : MvPolynomial σ ℂ) :
    (ray v p).eval t = eval (t • v) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [ray]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    have hx : ray v (X i) = Polynomial.C (v i) * Polynomial.X := by simp [ray]
    simp only [map_mul, hx, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      hp, eval_X, Pi.smul_apply, smul_eq_mul]
    ring

private theorem ray_homogeneous {σ : Type} (v : σ → ℂ) {p : MvPolynomial σ ℂ} {r : ℕ}
    (h : p.IsHomogeneous r) : ray v p = Polynomial.C (eval v p) * Polynomial.X^r := by
  apply Polynomial.funext
  intro t
  rw [eval_ray, h.eval_smul]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

theorem coeff_ray {σ : Type} (v : σ → ℂ) (p : MvPolynomial σ ℂ) (j : ℕ) :
    (ray v p).coeff j = eval v (homogeneousComponent j p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    have h := isHomogeneous_monomial (σ := σ) c (rfl : s.degree = s.degree)
    rw [ray_homogeneous v h, homogeneousComponent_of_mem h]
    by_cases hj : j = s.degree <;> simp [hj, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]

/-- Two polynomials with the same Taylor data through order m on the simplex
    rays have the same entire Taylor polynomial through that order. -/
theorem components_of_simplex_rays {σ : Type} [Fintype σ] {m : ℕ}
    (p q : MvPolynomial σ ℂ)
    (h : ∀ (a : σ → ℕ), (∑ i, a i) ≤ m → ∀ j ≤ m,
      (ray (fun i => (a i : ℂ)) p).coeff j = (ray (fun i => (a i : ℂ)) q).coeff j)
    (j : ℕ) (hj : j ≤ m) : homogeneousComponent j p = homogeneousComponent j q := by
  apply sub_eq_zero.mp
  apply eq_zero_of_simplex _ (((homogeneousComponent_isHomogeneous j p).sub
    (homogeneousComponent_isHomogeneous j q)).totalDegree_le.trans hj)
  intro a ha
  rw [map_sub, sub_eq_zero, ← coeff_ray, ← coeff_ray]
  exact h a ha j hj

private noncomputable def dilate {σ : Type} (z : ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  bind₁ (fun i => C z * X i)

private theorem dilate_homogeneous {σ : Type} {p : MvPolynomial σ ℂ} {r : ℕ}
    (h : p.IsHomogeneous r) (z : ℂ) : dilate z p = C (z^r) * p := by
  apply MvPolynomial.funext
  intro x
  change eval₂Hom (RingHom.id ℂ) x (bind₁ _ p) = _
  rw [eval₂Hom_bind₁]
  change eval (fun i => eval x (C z * X i)) p = _
  have hx : (fun i => eval x (C z * X i)) = z • x := by
    funext i
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hx, h.eval_smul]
  simp

private theorem coeff_dilate {σ : Type} (p : MvPolynomial σ ℂ) (z : ℂ) (s : σ →₀ ℕ) :
    (dilate z p).coeff s = z^s.degree * p.coeff s := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [dilate_homogeneous (isHomogeneous_monomial c rfl), coeff_C_mul, coeff_monomial]
    split_ifs <;> simp_all
  | add p q hp hq => simp [hp, hq, mul_add]

private theorem scale_output {σ : Type} {p : MvPolynomial σ ℂ} {N : ℕ} (hN : 0 < N)
    (hp : HasDetExpression p N) (z : ℂ) : HasDetExpression (C z * p) N := by
  obtain ⟨A, hA, hdet⟩ := hp
  let i₀ : Fin N := ⟨0,hN⟩
  refine ⟨A.updateRow i₀ ((C z : MvPolynomial σ ℂ) • A i₀), ?_, ?_⟩
  · intro i j
    by_cases hi : i = i₀
    · subst i
      rw [Matrix.updateRow_self, Pi.smul_apply, smul_eq_mul]
      exact (totalDegree_mul _ _).trans (by simpa using hA i₀ j)
    · rw [Matrix.updateRow_ne hi]
      exact hA i j
  · rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self, hdet]

/-- A determinant with the prescribed initial form degenerates to that form
    without increasing its size. Higher homogeneous components are unrestricted. -/
theorem border_of_initial_form {σ : Type} {p H : MvPolynomial σ ℂ} {m N : ℕ}
    (hN : 0 < N) (hp : HasDetExpression p N) (hH : H.IsHomogeneous m)
    (hc : ∀ s : σ →₀ ℕ, s.degree ≤ m → p.coeff s = H.coeff s) : HasBorderDetExpression H N := by
  let z (k : ℕ) : ℂ := 1 / ((k : ℂ) + 1)
  have hz (k : ℕ) : z k ≠ 0 := by
    have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    exact div_ne_zero one_ne_zero hk
  have hlim : Tendsto z atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let q (k : ℕ) := C ((z k)^m)⁻¹ * dilate (z k) p
  refine ⟨q, ?_, ?_⟩
  · intro k
    apply scale_output hN
    apply Helpers.hasDetExpression_bind₁ _ ?_ hp
    intro i
    exact (totalDegree_mul _ _).trans (by simp)
  · intro s
    have hcoeff (k : ℕ) : (q k).coeff s = ((z k)^m)⁻¹ * ((z k)^s.degree * p.coeff s) := by
      change (C _ * dilate (z k) p).coeff s = _
      rw [coeff_C_mul, coeff_dilate]
    simp only [hcoeff]
    rcases lt_trichotomy s.degree m with h | h | h
    · rw [hc s h.le, hH.coeff_eq_zero h.ne]
      simp
    · simp [h, hc s h.le, hz]
    · rw [hH.coeff_eq_zero h.ne']
      obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_lt h
      have hpow := hlim.pow (l+1)
      have ht : Tendsto (fun k => z k ^ (l+1) * p.coeff s) atTop (𝓝 0) := by
        simpa using hpow.mul_const (p.coeff s)
      convert ht using 1
      funext k
      have hs : s.degree = m + (l+1) := by omega
      rw [hs, pow_add]
      field_simp [hz]

/-- A single affine pencil fitting the first m Taylor coefficients and the
    order-m coefficient of the permanent on the finite simplex of rays yields
    border determinantal complexity at most the size of that pencil. -/
theorem border_perm_of_simplex_rays {m N : ℕ} (hN : 0 < N)
    (p : MvPolynomial (Fin m × Fin m) ℂ) (hp : HasDetExpression p N)
    (h : ∀ a : Fin m × Fin m → ℕ, (∑ i, a i) ≤ m → ∀ j ≤ m,
      (ray (fun i => (a i : ℂ)) p).coeff j =
        (ray (fun i => (a i : ℂ)) (permPoly ℂ m)).coeff j) :
    HasBorderDetExpression (permPoly ℂ m) N := by
  apply border_of_initial_form hN hp (Helpers.perm_isHomogeneous m)
  intro s hs
  have e := congrArg (fun f : MvPolynomial (Fin m × Fin m) ℂ => f.coeff s)
    (components_of_simplex_rays p (permPoly ℂ m) h s.degree hs)
  simpa [coeff_homogeneousComponent] using e

/-- Among m+1 disjoint sets of coordinates, any support of size at most m
    avoids at least one set. -/
private theorem exists_disjoint {σ : Type} {m : ℕ} (F : Fin (m+1) → Finset σ)
    (hF : ∀ i j, i ≠ j → Disjoint (F i) (F j)) (s : Finset σ) (hs : s.card ≤ m) :
    ∃ i, Disjoint s (F i) := by
  classical
  by_contra! h
  choose f hf hg using fun i => Finset.not_disjoint_iff.mp (h i)
  let u (i : Fin (m+1)) : ↥s := ⟨f i, hf i⟩
  have hu : Function.Injective u := by
    intro i j heq
    by_contra hij
    have he : f i = f j := congrArg Subtype.val heq
    exact Finset.disjoint_left.mp (hF i j hij) (hg i) (he ▸ hg j)
  have hcard := Fintype.card_le_of_injective u hu
  simp only [Fintype.card_fin, Fintype.card_coe] at hcard
  omega

/-- One pencil agreeing exactly with the permanent on all m+1 coordinate
    subspaces, whose respective zero sets of entries are pairwise disjoint,
    gives a border representation of the full permanent at the same size. -/
theorem border_perm_of_disjoint_restrictions {m N : ℕ} (hN : 0 < N)
    (p : MvPolynomial (Fin m × Fin m) ℂ) (hp : HasDetExpression p N)
    (F : Fin (m+1) → Finset (Fin m × Fin m)) (hF : ∀ i j, i ≠ j → Disjoint (F i) (F j))
    (hfit : ∀ i (x : Fin m × Fin m → ℂ), (∀ v ∈ F i, x v = 0) →
      eval x p = eval x (permPoly ℂ m)) : HasBorderDetExpression (permPoly ℂ m) N := by
  classical
  apply border_perm_of_simplex_rays hN p hp
  intro a ha j _
  let s := Finset.univ.filter (fun i => a i ≠ 0)
  have hs : s.card ≤ m := calc
    s.card = ∑ i ∈ s, 1 := by simp
    _ ≤ ∑ i ∈ s, a i := Finset.sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.mpr
      (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i, a i := Finset.sum_le_sum_of_subset (Finset.subset_univ s)
    _ ≤ m := ha
  obtain ⟨i, hi⟩ := exists_disjoint F hF s hs
  have he : ray (fun v => (a v : ℂ)) p = ray (fun v => (a v : ℂ)) (permPoly ℂ m) := by
    apply Polynomial.funext
    intro t
    rw [eval_ray, eval_ray]
    apply hfit i
    intro v hv
    have hzero : a v = 0 := by
      by_contra hn
      exact Finset.disjoint_left.mp hi (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hn⟩) hv
    simp [Pi.smul_apply, hzero]
  exact congrArg (fun q : Polynomial ℂ => q.coeff j) he

/-- Ten cyclic triples and one extra triple give the eleven explicit subspaces
    used for the size-ten experiment. Indices start at zero. -/
def deletedTriple (i : Fin 11) : Finset (Fin 10 × Fin 10) :=
  if hi : i.val < 10 then
    let j : Fin 10 := ⟨i.val,hi⟩
    {(j,j), (j+1,j), (j+2,j)}
  else {(3,0), (4,0), (5,0)}

theorem deletedTriple_disjoint :
    ∀ i j : Fin 11, i ≠ j → Disjoint (deletedTriple i) (deletedTriple j) := by decide

theorem ten_by_ten_shared_pencil (p : MvPolynomial (Fin 10 × Fin 10) ℂ)
    (hp : HasDetExpression p 1001)
    (hfit : ∀ i (x : Fin 10 × Fin 10 → ℂ), (∀ v ∈ deletedTriple i, x v = 0) →
      eval x p = eval x (permPoly ℂ 10)) : HasBorderDetExpression (permPoly ℂ 10) 1001 :=
  border_perm_of_disjoint_restrictions (by decide) p hp deletedTriple deletedTriple_disjoint hfit

private noncomputable def indices (m n : ℕ) : Finset ((Fin m × Fin m) →₀ ℕ) :=
  (Finsupp.finite_of_degree_le (n+1)).toFinset

/-- Homogenization to degree n+1 is a fixed finite linear map on the coefficients.
    This description makes it commute with coefficientwise limits. -/
private noncomputable def liftForm (m n : ℕ) (q : MvPolynomial (Fin m × Fin m) ℂ) :
    MvPolynomial (Fin (n+1) × Fin (n+1)) ℂ :=
  ∑ s ∈ indices m n, C (q.coeff s) * (X (0,0)^(n+1-s.degree) *
    rename (padIndex m n) (monomial s (1 : ℂ)))

private theorem cancel_powers {z : ℂ} (hz : z ≠ 0) {a b : ℕ} (hb : b ≤ a) :
    z^a * z⁻¹^b = z^(a-b) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hb
  rw [pow_add, inv_pow, Nat.add_sub_cancel_left]
  field_simp

private theorem eval_liftForm {m n : ℕ} (q : MvPolynomial (Fin m × Fin m) ℂ)
    (hd : q.totalDegree ≤ n+1) (w : Fin (n+1) × Fin (n+1) → ℂ) (hz : w (0,0) ≠ 0) :
    eval w (liftForm m n q) = w (0,0)^(n+1) *
      eval ((w (0,0))⁻¹ • (w ∘ padIndex m n)) q := by
  classical
  have hS (s : Fin m × Fin m →₀ ℕ) (hs : s ∉ indices m n) : q.coeff s = 0 := by
    apply coeff_eq_zero_of_totalDegree_lt
    have hn : ¬s.degree ≤ n+1 := by simpa [indices] using hs
    exact lt_of_le_of_lt hd (lt_of_not_ge hn)
  have hsum := congrArg (eval ((w (0,0))⁻¹ • (w ∘ padIndex m n)))
    (Helpers.BorderMR.eq_sum_monomial (indices m n) q hS)
  simp only [map_sum, smul_eq_C_mul, map_mul, eval_C] at hsum
  rw [hsum, Finset.mul_sum]
  simp only [liftForm, map_sum, map_mul, eval_C, map_pow, eval_X, eval_rename]
  apply Finset.sum_congr rfl
  intro s hs
  have hdeg : s.degree ≤ n+1 := by simpa [indices] using hs
  rw [(isHomogeneous_monomial (1 : ℂ) (rfl : s.degree = s.degree)).eval_smul]
  calc
    _ = (w (0,0)^(n+1-s.degree)) *
        (q.coeff s * eval (w ∘ padIndex m n) (monomial s 1)) := by ring
    _ = _ := by rw [← cancel_powers hz hdeg]; ring

private theorem ext_off_corner {n : ℕ} {p q : MvPolynomial (Fin (n+1) × Fin (n+1)) ℂ}
    (h : ∀ w, w (0,0) ≠ 0 → eval w p = eval w q) : p = q := by
  refine mul_left_cancel₀ (X_ne_zero (R := ℂ) (0,0)) (MvPolynomial.funext fun w => ?_)
  simp only [map_mul, eval_X]
  by_cases hz : w (0,0) = 0
  · simp [hz]
  · rw [h w hz]

private theorem lift_of_det {m n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) (MvPolynomial (Fin m × Fin m) ℂ))
    (hA : ∀ i j, (A i j).totalDegree ≤ 1) :
    liftForm m n A.det = linSubst (Helpers.homMat A) (detPoly ℂ (n+1)) := by
  apply ext_off_corner
  intro w hz
  let z := w (0,0)
  let x := w ∘ padIndex m n
  have hm : (Matrix.of fun i j => (Helpers.homMat A).mulVec w (i,j)) =
      z • (Matrix.of fun i j => eval (z⁻¹ • x) (A i j)) := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Helpers.homMat_mulVec,
      Helpers.eval_affine _ (hA i j), Pi.smul_apply, mul_add, Finset.mul_sum, x, z,
      Function.comp_apply]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro v _
      field_simp
  have hd := L003 _ ℂ A.det (n+1) ⟨A, hA, rfl⟩
  rw [eval_liftForm A.det hd w hz, Helpers.eval_linSubst, detPoly, Matrix.eval_det_mvPolynomialX,
    hm, Matrix.det_smul, Fintype.card_fin, RingHom.map_det]
  rfl

private theorem lift_perm {m n : ℕ} (hmn : m ≤ n) :
    liftForm m n (permPoly ℂ m) = paddedPerm ℂ m n := by
  apply ext_off_corner
  intro w hz
  have h := Helpers.perm_isHomogeneous m
  rw [eval_liftForm _ (h.totalDegree_le.trans (by omega)) w hz, h.eval_smul,
    ← mul_assoc, cancel_powers hz (by omega)]
  simp [paddedPerm, eval_rename]

private theorem orbit_as_closure {ι : Type} [Fintype ι] [DecidableEq ι]
    (p f : MvPolynomial ι ℂ) :
    p ∈ orbitClosure f ↔ (fun s => p.coeff s) ∈ closure
      (Set.range fun g : Matrix.GeneralLinearGroup ι ℂ => fun s => (linSubst g.val f).coeff s) := by
  constructor
  · rintro ⟨g,hg⟩
    apply mem_closure_iff_seq_limit.mpr
    exact ⟨fun k s => (linSubst (g k).val f).coeff s, fun k => ⟨g k,rfl⟩,
      tendsto_pi_nhds.mpr hg⟩
  · intro h
    obtain ⟨a,ha,hl⟩ := mem_closure_iff_seq_limit.mp h
    choose g hg using ha
    refine ⟨g, ?_⟩
    have he : (fun k s => (linSubst (g k).val f).coeff s) = a := funext hg
    rw [← he] at hl
    exact tendsto_pi_nhds.mp hl

/-- A border expression homogenizes into the determinant orbit closure at the
    same size, including when its affine coefficients have no finite limit. -/
theorem padded_mem_of_border {m n : ℕ} (hmn : m ≤ n)
    (hb : HasBorderDetExpression (permPoly ℂ m) (n+1)) :
    paddedPerm ℂ m n ∈ orbitClosure (detPoly ℂ (n+1)) := by
  classical
  obtain ⟨q,hq,hlim⟩ := hb
  have hmem (k : ℕ) : liftForm m n (q k) ∈ orbitClosure (detPoly ℂ (n+1)) := by
    obtain ⟨A,hA,hdet⟩ := hq k
    rw [← hdet, lift_of_det A hA]
    exact Helpers.linSubst_mem_orbitClosure _ _
  have ht : Tendsto (fun k s => (liftForm m n (q k)).coeff s) atTop
      (𝓝 (fun s => (liftForm m n (permPoly ℂ m)).coeff s)) := by
    apply tendsto_pi_nhds.mpr
    intro t
    simp only [liftForm, coeff_sum, coeff_C_mul]
    exact tendsto_finsetSum _ fun s _ => (hlim s).mul_const _
  rw [← lift_perm hmn, orbit_as_closure]
  exact isClosed_closure.mem_of_tendsto ht (.of_forall fun k => (orbit_as_closure _ _).mp (hmem k))

theorem ten_by_ten_shared_pencil_orbit (p : MvPolynomial (Fin 10 × Fin 10) ℂ)
    (hp : HasDetExpression p 1001)
    (hfit : ∀ i (x : Fin 10 × Fin 10 → ℂ), (∀ v ∈ deletedTriple i, x v = 0) →
      eval x p = eval x (permPoly ℂ 10)) :
    paddedPerm ℂ 10 (10^3) ∈ orbitClosure (detPoly ℂ (10^3+1)) :=
  padded_mem_of_border (by decide) (ten_by_ten_shared_pencil p hp hfit)

end GctFrontier.CubicExamples
