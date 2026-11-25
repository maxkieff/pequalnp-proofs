import PEqualNP.Gct.Helpers.OrbitClosure

/-! A dimension bound for smooth homogeneous affine restrictions of the permanent. -/

namespace GctFrontier.SmoothSliceCap

open MvPolynomial PEqualNP.Gct

private noncomputable def ray {d : ℕ} (v : Fin d → ℂ) :
    MvPolynomial (Fin d) ℂ →+* Polynomial ℂ :=
  eval₂Hom Polynomial.C (fun i => Polynomial.C (v i) * Polynomial.X)

@[simp] private theorem ray_C {d : ℕ} (v : Fin d → ℂ) (z : ℂ) :
    ray v (C z) = Polynomial.C z := by simp [ray]

@[simp] private theorem ray_X {d : ℕ} (v : Fin d → ℂ) (i : Fin d) :
    ray v (X i) = Polynomial.C (v i) * Polynomial.X := by simp [ray]

private theorem eval_ray {d : ℕ} (v : Fin d → ℂ) (t : ℂ) (f : MvPolynomial (Fin d) ℂ) :
    (ray v f).eval t = eval (t • v) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f i hf =>
    simp only [map_mul, ray_X, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      hf, eval_X, Pi.smul_apply, smul_eq_mul]
    ring

private theorem ray_homogeneous {d r : ℕ} (v : Fin d → ℂ) {f : MvPolynomial (Fin d) ℂ}
    (h : f.IsHomogeneous r) : ray v f = Polynomial.C (eval v f) * Polynomial.X ^ r := by
  apply Polynomial.funext
  intro t
  rw [eval_ray, h.eval_smul]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

/-- On a ray the coefficient of degree r−1 in a first partial comes from the
    degree-r homogeneous component of the original polynomial. -/
private theorem coeff_ray_partial {d r : ℕ} (hr : 2 ≤ r) (v : Fin d → ℂ) (j : Fin d)
    (f : MvPolynomial (Fin d) ℂ) :
    (ray v (pderiv j f)).coeff (r-1) = eval v (pderiv j (homogeneousComponent r f)) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial a z =>
    have hm : (monomial a z).IsHomogeneous a.degree := isHomogeneous_monomial z rfl
    rw [homogeneousComponent_of_mem hm]
    by_cases ha : r = a.degree
    · subst r
      rw [ite_eq_left rfl, ray_homogeneous v (hm.pderiv (i := j))]
      simp
    · have hne : a.degree - 1 ≠ r - 1 := by omega
      rw [ite_eq_right ha, map_zero, map_zero, ray_homogeneous v (hm.pderiv (i := j))]
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne.symm]
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]

/-- Value of the linear part of an affine entry on a vector. -/
noncomputable def slope {d : ℕ} (f : MvPolynomial (Fin d) ℂ) (v : Fin d → ℂ) : ℂ :=
  ∑ i, f.coeff (Finsupp.single i 1) * v i

/-- The columns with nonzero directional slopes along a permutation of the rows. -/
noncomputable def matchingColumns {m d : ℕ} (g : Fin m × Fin m → MvPolynomial (Fin d) ℂ)
    (v : Fin d → ℂ) (σ : Equiv.Perm (Fin m)) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => slope (g (σ i, i)) v ≠ 0)

private theorem ray_affine {d : ℕ} {f : MvPolynomial (Fin d) ℂ} (hf : f.totalDegree ≤ 1)
    (v : Fin d → ℂ) :
    ray v f = Polynomial.C (f.coeff 0) + Polynomial.C (slope f v) * Polynomial.X := by
  apply Polynomial.funext
  intro t
  rw [eval_ray, Helpers.eval_affine f hf]
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
    Pi.smul_apply, smul_eq_mul, slope, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- An affine factor that is constant on the ray contributes no ray degree, even if
    the partial derivative differentiates a different factor. -/
private theorem prod_degrees {d : ℕ} {α : Type*} (s : Finset α)
    (f : α → MvPolynomial (Fin d) ℂ) (w : α → ℕ) (v : Fin d → ℂ) (j : Fin d)
    (hf : ∀ i, (ray v (f i)).natDegree ≤ w i)
    (hdf : ∀ i, (ray v (pderiv j (f i))).natDegree = 0) :
    (ray v (∏ i ∈ s, f i)).natDegree ≤ ∑ i ∈ s, w i ∧
    (ray v (pderiv j (∏ i ∈ s, f i))).natDegree ≤ ∑ i ∈ s, w i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    constructor
    · rw [map_mul]
      exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hf a) ih.1)
    · rw [Derivation.leibniz, map_add]
      simp only [smul_eq_mul, map_mul]
      apply Polynomial.natDegree_add_le_of_degree_le
      · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hf a) ih.2)
      · apply Polynomial.natDegree_mul_le.trans
        rw [hdf a, Nat.add_zero]
        exact ih.1.trans (Nat.le_add_left _ _)

/-- If every permutation meets at most r−2 nonzero slopes along a direction,
    the degree-r component has zero gradient there. -/
private theorem gradient_zero {m d r : ℕ} (hr : 2 ≤ r)
    (g : Fin m × Fin m → MvPolynomial (Fin d) ℂ) (hg : ∀ q, (g q).totalDegree ≤ 1)
    (v : Fin d → ℂ) (hshort : ∀ σ, (matchingColumns g v σ).card ≤ r-2) (j : Fin d) :
    eval v (pderiv j (homogeneousComponent r (bind₁ g (permPoly ℂ m)))) = 0 := by
  classical
  have hform : bind₁ g (permPoly ℂ m) = ∑ σ : Equiv.Perm (Fin m), ∏ i, g (σ i, i) := by
    simp [permPoly, Matrix.permanent]
  have hdeg : (ray v (pderiv j (bind₁ g (permPoly ℂ m)))).natDegree ≤ r-2 := by
    rw [hform]
    simp only [map_sum]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro σ _
    refine le_trans ?_ (hshort σ)
    let w : Fin m → ℕ := fun i => if i ∈ matchingColumns g v σ then 1 else 0
    have hf (i : Fin m) : (ray v (g (σ i,i))).natDegree ≤ w i := by
      rw [ray_affine (hg _) v]
      by_cases hi : i ∈ matchingColumns g v σ
      · simp only [w, ite_eq_left hi]
        apply Polynomial.natDegree_add_le_of_degree_le (by simp)
        exact Polynomial.natDegree_mul_le.trans (by simp)
      · have hz : slope (g (σ i,i)) v = 0 := by simpa [matchingColumns] using hi
        simp [w, hi, hz]
    have hd (i : Fin m) : (ray v (pderiv j (g (σ i,i)))).natDegree = 0 := by
      rw [Helpers.pderiv_of_totalDegree_le_one _ (hg _) j, ray_C, Polynomial.natDegree_C]
    have h := (prod_degrees Finset.univ (fun i => g (σ i,i)) w v j hf hd).2
    simpa [w] using h
  rw [← coeff_ray_partial hr]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (by omega))

/-- Every nonzero direction of a smooth degree-r component has a matching
    of at least r−1 nonzero entries in its matrix of linear parts. -/
theorem exists_matching {m d r : ℕ} (hr : 2 ≤ r)
    (g : Fin m × Fin m → MvPolynomial (Fin d) ℂ) (hg : ∀ q, (g q).totalDegree ≤ 1)
    (hsmooth : ∀ v : Fin d → ℂ,
      (∀ j, eval v (pderiv j (homogeneousComponent r (bind₁ g (permPoly ℂ m)))) = 0) → v = 0)
    (v : Fin d → ℂ) (hv : v ≠ 0) : ∃ σ, r-1 ≤ (matchingColumns g v σ).card := by
  by_contra! h
  apply hv (hsmooth v (gradient_zero hr g hg v ?_))
  intro σ
  have := h σ
  omega

/-- When the degree-r homogeneous component of an affine restriction is smooth,
    the complementary m−r+2 columns already detect every variable direction. -/
theorem component_dimension_bound {m d r : ℕ} (hr : 2 ≤ r) (hrm : r ≤ m)
    (g : Fin m × Fin m → MvPolynomial (Fin d) ℂ) (hg : ∀ q, (g q).totalDegree ≤ 1)
    (hsmooth : ∀ v : Fin d → ℂ,
      (∀ j, eval v (pderiv j (homogeneousComponent r (bind₁ g (permPoly ℂ m)))) = 0) → v = 0) :
    d ≤ m * (m-r+2) := by
  classical
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin m))) (n := r-2) (by simp; omega)
  let M : Matrix (Fin m × ↥(Sᶜ : Finset (Fin m))) (Fin d) ℂ :=
    fun k j => (g (k.1, k.2.val)).coeff (Finsupp.single j 1)
  have hker : ∀ v, M.mulVecLin v = 0 → v = 0 := by
    intro v hv
    by_contra hv'
    obtain ⟨σ, hσ⟩ := exists_matching hr g hg hsmooth v hv'
    have hsub : matchingColumns g v σ ⊆ S := by
      intro i hi
      by_contra h
      have he : slope (g (σ i,i)) v = 0 := congrFun hv (σ i, ⟨i, Finset.mem_compl.mpr h⟩)
      simp [matchingColumns, he] at hi
    have := Finset.card_le_card hsub
    omega
  have hinj := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr hker)
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  have hcount : m - (r-2) = m-r+2 := by omega
  simpa [Module.finrank_fintype_fun_eq_card, Finset.card_compl, hS, hcount] using hdim

/-- The numerator in the project's single-smooth-slice polar lower bound is
    at most m(m+1)^2/4, even for a smooth homogeneous component. -/
theorem component_polar_numerator_cap {m d r : ℕ} (hr : 2 ≤ r) (hrm : r ≤ m)
    (g : Fin m × Fin m → MvPolynomial (Fin d) ℂ) (hg : ∀ q, (g q).totalDegree ≤ 1)
    (hsmooth : ∀ v : Fin d → ℂ,
      (∀ j, eval v (pderiv j (homogeneousComponent r (bind₁ g (permPoly ℂ m)))) = 0) → v = 0) :
    4 * ((r-1) * (d-1)) ≤ m * (m+1)^2 := by
  have hd := component_dimension_bound hr hrm g hg hsmooth
  have hsum : (r-1) + (m-r+2) = m+1 := by omega
  calc
    4 * ((r-1) * (d-1)) ≤ 4 * ((r-1) * (m*(m-r+2))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ((Nat.sub_le d 1).trans hd))
    _ = m * (4*(r-1)*(m-r+2)) := by ring
    _ ≤ m * (m+1)^2 := Nat.mul_le_mul_left _ (hsum ▸ four_mul_le_sq_add (r-1) (m-r+2))

end GctFrontier.SmoothSliceCap
