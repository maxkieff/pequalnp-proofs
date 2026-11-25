import PEqualNP.Gct.L001
import PEqualNP.Gct.L023
import PEqualNP.Gct.L074
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Orbit separation for small exponents, and the reduction of the full
statement of L-gct-011 to a quantitative border-circuit lower bound. -/

namespace GctFrontier.OrbitSeparation

open MvPolynomial PEqualNP.Gct

private theorem pad_values {m n : ℕ} (hmn : m ≤ n) (x : Fin m × Fin m) :
    ((padIndex m n x).1 : ℕ) = x.1.val + 1 ∧
    ((padIndex m n x).2 : ℕ) = x.2.val + 1 := by
  have hx := x.1.isLt
  have hy := x.2.isLt
  simp [padIndex, Nat.mod_eq_of_lt (show x.1.val + 1 < n + 1 by omega),
    Nat.mod_eq_of_lt (show x.2.val + 1 < n + 1 by omega)]

private theorem pad_injective {m n : ℕ} (hmn : m ≤ n) :
    Function.Injective (padIndex m n) := by
  intro x y h
  have h₁ := congrArg (fun p : Fin (n+1) × Fin (n+1) => p.1.val) h
  have h₂ := congrArg (fun p : Fin (n+1) × Fin (n+1) => p.2.val) h
  change (padIndex m n x).1.val = (padIndex m n y).1.val at h₁
  change (padIndex m n x).2.val = (padIndex m n y).2.val at h₂
  rw [(pad_values hmn x).1, (pad_values hmn y).1] at h₁
  rw [(pad_values hmn x).2, (pad_values hmn y).2] at h₂
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

private theorem pad_ne_corner {m n : ℕ} (hmn : m ≤ n) (x : Fin m × Fin m) :
    padIndex m n x ≠ (0, 0) := by
  intro h
  have he := congrArg (fun p : Fin (n+1) × Fin (n+1) => p.1.val) h
  change (padIndex m n x).1.val = 0 at he
  rw [(pad_values hmn x).1] at he
  omega

/-- At the padding corner substitute one, retain the permanent's variables, and
    set every other entry to zero. -/
private noncomputable def unpad (m n : ℕ) (p : Fin (n+1) × Fin (n+1)) :
    MvPolynomial (Fin m × Fin m) ℂ := by
  classical
  exact if p = (0, 0) then 1
    else if h : ∃ i, padIndex m n i = p then X h.choose else 0

private theorem unpad_affine (m n : ℕ) (p : Fin (n+1) × Fin (n+1)) :
    (unpad m n p).totalDegree ≤ 1 := by
  classical
  unfold unpad
  split_ifs <;> simp

private theorem unpad_block {m n : ℕ} (hmn : m ≤ n) :
    unpad m n ∘ padIndex m n = X := by
  classical
  funext i
  have hi : ∃ j, padIndex m n j = padIndex m n i := ⟨i, rfl⟩
  simp only [Function.comp_apply, unpad, ite_eq_right (pad_ne_corner hmn i), dite_eq_left hi]
  rw [pad_injective hmn hi.choose_spec]

private theorem unpad_paddedPerm {m n : ℕ} (hmn : m ≤ n) :
    bind₁ (unpad m n) (paddedPerm ℂ m n) = permPoly ℂ m := by
  have hz : unpad m n (0,0) = 1 := by classical simp [unpad]
  rw [paddedPerm, map_mul, map_pow, bind₁_X_right, hz, one_pow, one_mul,
    bind₁_rename, unpad_block hmn, bind₁_X_left]
  rfl

private theorem linear_det_expression {d : ℕ} (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    HasDetExpression (linSubst A (detPoly ℂ d)) d := by
  unfold linSubst
  refine Helpers.hasDetExpression_bind₁ (fun i => ∑ j, C (A i j) * X j) ?_ (L001 ℂ d)
  intro i
  apply totalDegree_finsetSum_le
  intro j _
  exact (totalDegree_mul _ _).trans (by simp)

private theorem border_of_orbit {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}
    {p f : MvPolynomial ι ℂ}
    (hA : ∀ A : Matrix.GeneralLinearGroup ι ℂ, HasDetExpression (linSubst A.val f) d)
    (hp : p ∈ orbitClosure f) : HasBorderDetExpression p d := by
  obtain ⟨g, hlim⟩ := hp
  exact ⟨fun k => linSubst (g k).val f, fun k => hA (g k), hlim⟩

/-- Every limit of homogeneous determinant substitutions has a border affine
    determinant expression of the original size. -/
theorem border_of_mem_det_orbit {d : ℕ}
    {p : MvPolynomial (Fin d × Fin d) ℂ}
    (hp : p ∈ orbitClosure (detPoly ℂ d)) : HasBorderDetExpression p d :=
  border_of_orbit (fun A => linear_det_expression A.val) hp

/-- Dehomogenization transfers any putative orbit containment to the unpadded
    permanent, including all coefficientwise limits in the definition. -/
theorem border_of_padded_mem {m n : ℕ} (hmn : m ≤ n)
    (hp : paddedPerm ℂ m n ∈ orbitClosure (detPoly ℂ (n+1))) :
    HasBorderDetExpression (permPoly ℂ m) (n+1) := by
  have h := L023 _ _ _ (unpad m n) _ (unpad_affine m n) (border_of_mem_det_orbit hp)
  rwa [unpad_paddedPerm hmn] at h

/-- Any fixed constant times the quadratic size is eventually excluded,
    uniformly over the whole interval of determinant sizes. -/
theorem exclude_quadratic (K : ℕ) :
    ∃ m₀ : ℕ, ∀ m n : ℕ, m₀ ≤ m → m ≤ n → n ≤ K * m ^ 2 →
      paddedPerm ℂ m n ∉ orbitClosure (detPoly ℂ (n+1)) := by
  obtain ⟨M, hM⟩ := L074 (K + 2)
  refine ⟨max M 1, ?_⟩
  intro m n hm hmn hn hp
  have hmM := (Nat.le_max_left M 1).trans hm
  have hm1 := (Nat.le_max_right M 1).trans hm
  have h := hM m (n+1) hmM (border_of_padded_mem hmn hp)
  have hsq : 1 ≤ m^2 := Nat.one_le_pow _ _ hm1
  rw [Nat.add_mul] at h
  omega

/-- The original quantifier order of L-gct-011 with the exponent restricted
    to the two positive integers at most two. -/
theorem first_two_exponents (c : ℕ) (hc : 1 ≤ c) (hc' : c ≤ 2) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      paddedPerm ℂ m (m ^ c) ∉ orbitClosure (detPoly ℂ (m ^ c + 1)) := by
  obtain ⟨M, hM⟩ := exclude_quadratic 1
  refine ⟨max M 1, ?_⟩
  intro m hm
  have hm1 := (Nat.le_max_right M 1).trans hm
  have hsq : m ≤ m^2 := by nlinarith
  apply hM m (m^c) ((Nat.le_max_left M 1).trans hm)
  · interval_cases c <;> simp_all
  · interval_cases c <;> simp_all

open Filter Topology

/-- Coordinates of the degree-d component, including zero coefficients. -/
def degreeCoeffs {σ : Type} (d : ℕ) (p : MvPolynomial σ ℂ)
    (s : {e : σ →₀ ℕ // e.sum (fun _ k => k) = d}) : ℂ :=
  p.coeff s.val

/-- Zariski closure after projecting the outputs onto one homogeneous degree. -/
def InDegreeClosure {σ : Type} (d : ℕ) (outputs : Set (MvPolynomial σ ℂ))
    (p : MvPolynomial σ ℂ) : Prop :=
  ∀ F : MvPolynomial {e : σ →₀ ℕ // e.sum (fun _ k => k) = d} ℂ,
    (∀ q ∈ outputs, eval (degreeCoeffs d q) F = 0) → eval (degreeCoeffs d p) F = 0

/-- For a fixed matrix order all scalar parameters occur in a single family. -/
noncomputable def pencilDet {σ : Type} [Fintype σ] (N : ℕ)
    (a : Fin N → Fin N → Option σ → ℂ) : MvPolynomial σ ℂ :=
  (Matrix.of fun i j => C (a i j none) + ∑ v, C (a i j (some v)) * X v).det

theorem mem_pencil_range {σ : Type} [Fintype σ] [DecidableEq σ]
    {p : MvPolynomial σ ℂ} {N : ℕ} (hp : HasDetExpression p N) :
    p ∈ Set.range (pencilDet (σ := σ) N) := by
  obtain ⟨A, hA, rfl⟩ := hp
  let a (i j : Fin N) : Option σ → ℂ
    | none => (A i j).coeff 0
    | some v => (A i j).coeff (Finsupp.single v 1)
  refine ⟨a, ?_⟩
  apply congrArg Matrix.det
  ext i j : 1
  exact (Helpers.affine_normal_form _ (hA i j)).symm

/-- Polynomial equations on any homogeneous degree survive a coefficientwise limit. -/
theorem degreeClosure_of_limit {σ : Type} {p : MvPolynomial σ ℂ} (d : ℕ)
    {S : Set (MvPolynomial σ ℂ)} (q : ℕ → MvPolynomial σ ℂ) (hq : ∀ j, q j ∈ S)
    (hlim : ∀ e, Tendsto (fun j => (q j).coeff e) atTop (𝓝 (p.coeff e))) :
    InDegreeClosure d S p := by
  intro F hF
  have hv : Tendsto (fun j => degreeCoeffs d (q j)) atTop (𝓝 (degreeCoeffs d p)) :=
    tendsto_pi_nhds.mpr fun e => hlim e.val
  have hc : IsClosed {x | eval x F = (0 : ℂ)} := isClosed_eq F.continuous_eval continuous_const
  exact hc.mem_of_tendsto hv (.of_forall fun j => hF _ (hq j))

/-- Project orbit containment implies Zariski closure of degree-m observations of
the fixed affine pencil family. No convergence of individual entries is assumed. -/
theorem degreeClosure_of_padded_mem {m n : ℕ} (hmn : m ≤ n)
    (hp : paddedPerm ℂ m n ∈ orbitClosure (detPoly ℂ (n+1))) :
    InDegreeClosure m (Set.range (pencilDet (σ := Fin m × Fin m) (n+1))) (permPoly ℂ m) := by
  obtain ⟨q, hq, hl⟩ := border_of_padded_mem hmn hp
  exact degreeClosure_of_limit m q (fun j => mem_pencil_range (hq j)) hl

/-- The quantitative affine-determinant consequence of Theorem 1.1 of
"Circuit lower bounds for Hamiltonian cycle and the permanent" (November 24, 2026).
This definition specifies the external input to the final implication. -/
def QuantitativePencilBound : Prop :=
  ∃ b : ℝ, 0 < b ∧ ∃ M : ℕ, ∀ m ≥ M, ∀ N : ℕ,
    InDegreeClosure m (Set.range (pencilDet (σ := Fin m × Fin m) N)) (permPoly ℂ m) →
    Real.exp (b * Real.log m ^ 2 / Real.log (Real.log m) ^ 2) ≤ N

/-- Each natural power is eventually dominated by the quantitative lower bound. -/
theorem eventually_pow_le_bound {b : ℝ} (hb : 0 < b) (d : ℕ) :
    ∀ᶠ m : ℕ in atTop, (m : ℝ)^d ≤
      Real.exp (b * Real.log m ^ 2 / Real.log (Real.log m) ^ 2) := by
  have hl : Tendsto (fun m : ℕ => Real.log (Real.log m)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hl.eventually_ge_atTop (max 1 (6 * (d : ℝ) / b)),
    eventually_ge_atTop (2 : ℕ)] with m hm hm₂
  let x := Real.log (m : ℝ)
  let u := Real.log x
  have hu₁ : (1 : ℝ) ≤ u := le_trans (le_max_left _ _) hm
  have hu₂ : 6 * (d : ℝ) / b ≤ u := le_trans (le_max_right _ _) hm
  have hu : 0 < u := by linarith
  have hx : 0 < x := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have he : u^3 / 6 ≤ x := by
    simpa [u, Real.exp_log hx, Nat.factorial] using Real.pow_div_factorial_le_exp u hu.le 3
  have hdu : 6 * (d : ℝ) ≤ u * b := (div_le_iff₀ hb).mp hu₂
  have hs : (d : ℝ) * u^2 ≤ b * x := by
    nlinarith [mul_le_mul_of_nonneg_right hdu (sq_nonneg u),
      mul_le_mul_of_nonneg_left he hb.le]
  have he' : (d : ℝ) * x ≤ b * x^2 / u^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hu)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hs hx.le]
  calc
    (m : ℝ)^d = Real.exp ((d : ℝ) * x) := by
      rw [Real.exp_nat_mul, Real.exp_log (by positivity : (0 : ℝ) < m)]
    _ ≤ _ := Real.exp_le_exp.mpr he'

/-- With the quantitative published input, a whole polynomial interval of
matrix orders is excluded with one threshold. -/
theorem uniform_separation_of_pencil_bound (h : QuantitativePencilBound) (c K : ℕ) :
    ∃ M : ℕ, ∀ m n : ℕ, M ≤ m → m ≤ n → n ≤ K * m^c →
      paddedPerm ℂ m n ∉ orbitClosure (detPoly ℂ (n+1)) := by
  obtain ⟨b, hb, M, hbound⟩ := h
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_pow_le_bound hb (c+1))
  refine ⟨max (max M T) (K+2), ?_⟩
  intro m n hm hmn hn hp
  have hMT := (Nat.le_max_left _ _).trans hm
  have hmM := (Nat.le_max_left M T).trans hMT
  have hmT := (Nat.le_max_right M T).trans hMT
  have hmK := (Nat.le_max_right (max M T) (K+2)).trans hm
  have hlow := (hT m hmT).trans (hbound m hmM (n+1) (degreeClosure_of_padded_mem hmn hp))
  have hnat : m^(c+1) ≤ n+1 := by exact_mod_cast hlow
  have hmpos : 1 ≤ m^c := Nat.one_le_pow _ _ (by omega)
  have hmul := Nat.mul_le_mul_right (m^c) hmK
  rw [pow_succ, Nat.mul_comm (m^c) m] at hnat
  rw [Nat.add_mul] at hmul
  omega

/-- Exact project quantifiers. The quantitative lower bound is an explicit input. -/
theorem L_gct_011_of_pencil_bound (h : QuantitativePencilBound) :
    ∀ c : ℕ, 1 ≤ c → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      paddedPerm ℂ m (m^c) ∉ orbitClosure (detPoly ℂ (m^c + 1)) := by
  intro c hc
  obtain ⟨M, hM⟩ := uniform_separation_of_pencil_bound h c 1
  refine ⟨M, fun m hm => hM m (m^c) hm (Nat.le_self_pow (by omega) m) (by simp)⟩

end GctFrontier.OrbitSeparation
