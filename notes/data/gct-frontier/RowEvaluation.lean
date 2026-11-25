import Mathlib

/-! An exponential matrix of evaluations on two groups of rows, for both the permanent
and the determinant. Each size-2 block uses one row from each group. -/

namespace GctFrontier.RowEvaluation

open Filter Topology

private def rowChoice {k : ℕ} (a b : Fin k → Bool) (i : Fin k × Bool) : Fin k × Bool :=
  (i.1, if i.2 then !(b i.1) else a i.1)

/-- Row (i,false) depends only on a and row (i,true) depends only on b. -/
def testMatrix {k : ℕ} (a b : Fin k → Bool) : Matrix (Fin k × Bool) (Fin k × Bool) ℂ :=
  fun i j => if rowChoice a b i = j then 1 else 0

private theorem rowChoice_involutive {k : ℕ} (a : Fin k → Bool) :
    Function.Involutive (rowChoice a a) := by
  rintro ⟨i,x⟩
  cases x <;> cases h : a i <;> simp [rowChoice, h]

private def blockPerm {k : ℕ} (a : Fin k → Bool) : Equiv.Perm (Fin k × Bool) :=
  (rowChoice_involutive a).toPerm _

private theorem test_diagonal {k : ℕ} (a : Fin k → Bool) :
    testMatrix a a = (1 : Matrix _ _ ℂ).submatrix (blockPerm a) id := by
  ext i j
  by_cases h : rowChoice a a i = j <;>
    simp [testMatrix, blockPerm, Matrix.one_apply, Matrix.submatrix, h]

private theorem zero_column {k : ℕ} (a b : Fin k → Bool) (hab : a ≠ b) :
    ∃ col, ∀ row, testMatrix a b row col = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
  refine ⟨(i,b i), ?_⟩
  rintro ⟨j,x⟩
  by_cases hj : j = i
  · subst j
    cases x <;> cases ha : a i <;> cases hb : b i <;> simp_all [testMatrix, rowChoice]
  · simp [testMatrix, rowChoice, hj]

/-- The permanent on this row-separated grid is the identity of order 2^k. -/
theorem permanent_grid (k : ℕ) :
    (Matrix.of fun a b : Fin k → Bool => (testMatrix a b).permanent) = 1 := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [test_diagonal, Matrix.permanent_permute_cols]
  · obtain ⟨j, hj⟩ := zero_column a b hab
    simp only [Matrix.of_apply, Matrix.one_apply, ite_eq_right hab, Matrix.permanent]
    exact Finset.sum_eq_zero fun σ _ => Finset.prod_eq_zero (Finset.mem_univ j) (hj (σ j))

/-- The very same evaluations of the size-2k determinant give an invertible
    diagonal matrix. Its diagonal signs reflect the within-block swaps. -/
theorem determinant_grid_nonsingular (k : ℕ) :
    (Matrix.of fun a b : Fin k → Bool => (testMatrix a b).det).det ≠ 0 := by
  have hd : (Matrix.of fun a b : Fin k → Bool => (testMatrix a b).det) =
      Matrix.diagonal (fun a : Fin k → Bool => (testMatrix a a).det) := by
    ext a b
    by_cases hab : a = b
    · subst b
      simp
    · obtain ⟨j, hj⟩ := zero_column a b hab
      simp [Matrix.diagonal, hab, Matrix.det_eq_zero_of_column_eq_zero j hj]
  rw [hd, Matrix.det_diagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro a _
  rw [test_diagonal, Matrix.det_permute, Matrix.det_one, mul_one]
  exact_mod_cast (Equiv.Perm.sign (blockPerm a)).ne_zero

/-- A fixed linear substitution into a determinant of the same size. It extracts
    the diagonal blocks and negates the top right entry of each block. -/
def signedBlocks {k : ℕ} (M : Matrix (Fin k × Bool) (Fin k × Bool) ℂ) :
    Matrix (Fin 2 × Fin k) (Fin 2 × Fin k) ℂ :=
  Matrix.blockDiagonal (fun i : Fin k =>
    !![M (i,false) (i,false), -M (i,false) (i,true);
       M (i,true) (i,false), M (i,true) (i,true)])

/-- One substitution reproduces the permanent on every evaluation in the grid,
    including the signs of all diagonal values. -/
theorem signed_grid {k : ℕ} (a b : Fin k → Bool) :
    (signedBlocks (testMatrix a b)).det = (testMatrix a b).permanent := by
  let Q := testMatrix a b
  have hb (i : Fin k) : (!![Q (i,false) (i,false), -Q (i,false) (i,true);
      Q (i,true) (i,false), Q (i,true) (i,true)]).det = if a i = b i then 1 else 0 := by
    rw [Matrix.det_fin_two]
    cases ha : a i <;> cases hb : b i <;> simp [Q, testMatrix, rowChoice, ha, hb]
  have hp := congrFun (congrFun (permanent_grid k) a) b
  change (testMatrix a b).permanent = (1 : Matrix _ _ ℂ) a b at hp
  rw [hp, signedBlocks, Matrix.det_blockDiagonal]
  change (∏ i : Fin k, (!![Q (i,false) (i,false), -Q (i,false) (i,true);
      Q (i,true) (i,false), Q (i,true) (i,true)]).det) = _
  simp_rw [hb]
  by_cases hab : a = b
  · subst b
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
    rw [Matrix.one_apply, ite_eq_right hab]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- On the six permutation matrices of order three, the three even and three
    odd products use exactly the same nine entries. Their sign requirements
    are already incompatible with any single entrywise complex rescaling. -/
theorem incompatible_three_by_three (a b c d e f g h i : ℂ) :
    ¬ (a*e*i = 1 ∧ b*f*g = 1 ∧ c*d*h = 1 ∧
       a*f*h = -1 ∧ b*d*i = -1 ∧ c*e*g = -1) := by
  rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
  have he : (a*e*i)*(b*f*g)*(c*d*h) = (a*f*h)*(b*d*i)*(c*e*g) := by ring
  rw [h₁, h₂, h₃, h₄, h₅, h₆] at he
  norm_num at he

/-- Even an entrywise limit of width-w factorizations across the row split
    needs width at least 2^k when the matrix of evaluations is nonsingular. -/
theorem border_width {k w : ℕ} (P : Matrix (Fin k → Bool) (Fin k → Bool) ℂ)
    (hP : P.det ≠ 0)
    (L : ℕ → Matrix (Fin k → Bool) (Fin w) ℂ) (R : ℕ → Matrix (Fin w) (Fin k → Bool) ℂ)
    (hlim : ∀ a b, Tendsto (fun t => (L t * R t) a b) atTop (𝓝 (P a b))) :
    2^k ≤ w := by
  have hl : Tendsto (fun t => L t * R t) atTop (𝓝 P) :=
    tendsto_pi_nhds.mpr fun a => tendsto_pi_nhds.mpr fun b => hlim a b
  have hdet : Tendsto (fun t => (L t * R t).det) atTop (𝓝 P.det) :=
    (continuous_id.matrix_det.tendsto _).comp hl
  obtain ⟨t, ht⟩ := (hdet.eventually_ne hP).exists
  have h := (Matrix.rank_mul_le_left (L t) (R t)).trans (L t).rank_le_card_width
  rw [Matrix.rank_of_det_ne_zero ht] at h
  simpa using h

end GctFrontier.RowEvaluation
