import PEqualNP.Gct.L001
import PEqualNP.Gct.L023
import PEqualNP.Gct.L074

/-! The linear and quadratic cases of the research map's L-gct-011. -/

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

end GctFrontier.OrbitSeparation
