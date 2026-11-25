import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace GctFrontier.CofactorConic

/-- Sum over injections from the four rows to the columns. -/
noncomputable def permanent {R : Type*} [CommRing R] {q : ℕ} (M : Fin 4 × Fin q → R) : R :=
  ∑ e : Fin 4 ↪ Fin q, ∏ i, M (i, e i)

/-- The lower rectangular permanent after deletion of column j,
indexed by the unique extension of each three-row matching. -/
noncomputable def cofactor {R : Type*} [CommRing R] {q : ℕ} (M : Fin 4 × Fin q → R) (j : Fin q) : R :=
  ∑ e : Fin 4 ↪ Fin q, if e 0 = j then ∏ i : Fin 3, M (i.succ, e i.succ) else 0

def inTop {R : Type*} [Zero R] {q : ℕ} (a : Fin q → R) : Fin 4 × Fin q → R :=
  fun p => if p.1 = 0 then a p.2 else 0

/-- The cofactor vector annihilates every available pure top-row
perturbation, at every point of a permanent level space. -/
theorem pure_row_annihilates_cofactors {K : Type*} [Field K] {q : ℕ}
    (L : Submodule K (Fin 4 × Fin q → K)) (J B : Fin 4 × Fin q → K) (a : Fin q → K)
    (level : ∀ Z ∈ L, permanent (J+Z) = permanent J) (hB : B ∈ L) (ha : inTop a ∈ L) :
    ∑ j, a j * cofactor (J+B) j = 0 := by
  classical
  let M := J+B
  let term := fun (e : Fin 4 ↪ Fin q) => ∏ i : Fin 3, M (i.succ, e i.succ)
  have grouped : ∑ j, a j * cofactor M j = ∑ e : Fin 4 ↪ Fin q, a (e 0) * term e := by
    simp only [cofactor, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    simp [term]
  have shifted : permanent (M + inTop a) = permanent M + ∑ e : Fin 4 ↪ Fin q, a (e 0)*term e := by
    unfold permanent
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    simp [Fin.prod_univ_succ, Pi.add_apply, inTop, term, add_mul]
  have same : permanent (M + inTop a) = permanent M := by
    change permanent ((J+B)+inTop a) = permanent (J+B)
    rw [add_assoc, level _ (L.add_mem hB ha), level _ hB]
  change ∑ j, a j * cofactor M j = 0
  rw [grouped]
  linear_combination same - shifted

/-- The bilinear dot product in the three cyclic coordinates of a
lower column. The two nontrivial orientations are isotropic. -/
theorem column_dot {R : Type*} [CommRing R] (w m u v n a b : R)
    (hw : w^2+w+1 = 0) :
    (m+u+v)*(n+a+b) + (m+w*u+w^2*v)*(n+w*a+w^2*b) +
      (m+w^2*u+w*v)*(n+w^2*a+w*b) = 3*(m*n+u*b+v*a) := by
  linear_combination (m*(a+b)+n*(u+v)+(u*a+v*b)*(w^2-w+1)+2*(u*b+v*a)*(w-1))*hw

/-- Normalization of the quadratic deleted-matching equation into a
sampled product at column weight d. -/
theorem quadratic_cofactor {K : Type*} [Field K] [CharZero K]
    (u v U V d t h : K)
    (deleted : 3*(U*v+V*u)+6*d^2*t^2-6*u*v = d*h) :
    (2*u-U)*(2*v-V) = U*V + d*(-2/3*h) + 4*d^2*t^2 := by
  linear_combination (-2/3)*deleted

/-- The alternating weighted sum of the three values extracts the
leading coefficient of a quadratic, times the Vandermonde product. -/
theorem three_values {R : Type*} [CommRing R] (a b c r s t : R) :
    (s-t)*(a+r*b+r^2*c) + (t-r)*(a+s*b+s^2*c) + (r-s)*(a+t*b+t^2*c) =
      (r-s)*(r-t)*(s-t)*c := by ring

/-- A separating family obeying a sum-of-products equals a square
has dimension at most the number of product terms. The maps `a`
and `b` collect the first and weighted second factors. -/
theorem split_products_dimension {K E V : Type*} [Field K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (a : E →ₗ[K] V) (b : E →ₗ[K] Module.Dual K V) (t : E →ₗ[K] K)
    (square : ∀ x, b x (a x) = (t x)^2)
    (separates : ∀ x, a x = 0 → b x = 0 → t x = 0 → x = 0) :
    Module.finrank K E ≤ Module.finrank K V := by
  have vanishes (x : LinearMap.ker a) : t (x : E) = 0 := by
    by_contra h
    apply pow_ne_zero 2 h
    simpa [LinearMap.mem_ker.mp x.property] using (square (x : E)).symm
  have annihilates (x : LinearMap.ker a) : b (x : E) ∈ a.range.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    rintro _ ⟨y, rfl⟩
    have h := square (y + (x : E))
    simp only [map_add, LinearMap.add_apply, LinearMap.mem_ker.mp x.property, add_zero,
      vanishes, square] at h
    linear_combination h
  let g := (b.domRestrict (LinearMap.ker a)).codRestrict _ annihilates
  have inj : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply separates
    · simp only [map_sub, LinearMap.mem_ker.mp x.property, LinearMap.mem_ker.mp y.property,
        sub_self]
    · exact (map_sub b _ _).trans (sub_eq_zero.mpr (congrArg Subtype.val h))
    · simp only [map_sub, vanishes, sub_self]
  have dimKer := g.finrank_le_finrank_of_injective inj
  have dimRange := a.finrank_range_add_finrank_ker
  have dimAnnihilator := Subspace.finrank_add_finrank_dualAnnihilator_eq a.range
  change Module.finrank K (LinearMap.ker a) ≤ Module.finrank K a.range.dualAnnihilator at dimKer
  omega

/-- If every nonzero column product is a linear combination of the
sampled products, then any direction killing the sampled factors kills
all original coordinates. This form also works for an infinite index set. -/
theorem factors_detected_by_samples {K E ι I : Type*} [Field K] [Fintype I]
    [AddCommGroup E] [Module K E] (f g : ι → E →ₗ[K] K) (sample : I → ι)
    (mix : ∀ j, ∃ c : I → K, ∀ x, f j x * g j x =
      ∑ k, c k * (f (sample k) x * g (sample k) x))
    (nonzero : ∀ j, ∃ base, f j base * g j base ≠ 0)
    {v : E} (hf : ∀ k, f (sample k) v = 0) (hg : ∀ k, g (sample k) v = 0) :
    (∀ j, f j v = 0) ∧ (∀ j, g j v = 0) := by
  have both (j : ι) : f j v = 0 ∧ g j v = 0 := by
    obtain ⟨c, hc⟩ := mix j
    obtain ⟨y, hy⟩ := nonzero j
    have same (s : K) : (f j y + s * f j v) * (g j y + s * g j v) = f j y * g j y := by
      have h := hc (y+s • v)
      simp only [map_add, map_smul, smul_eq_mul, hf, hg, mul_zero, add_zero] at h
      exact h.trans (hc y).symm
    have kill (a b : K) (hb : b ≠ 0) : a + (-(a/b))*b = 0 := by simp [hb]
    constructor
    · by_contra h
      exact hy (by simpa only [kill _ _ h, zero_mul] using (same (-(f j y / f j v))).symm)
    · by_contra h
      exact hy (by simpa only [kill _ _ h, mul_zero] using (same (-(g j y / g j v))).symm)
  exact ⟨fun j => (both j).1, fun j => (both j).2⟩

/-- The no-exception case of the dimension argument. The sampled
products span all column products and interpolate the leading square.
For a quadratic family three sampled indices suffice. -/
theorem no_exception_dimension {K E ι I : Type*} [Field K] [Fintype I]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (f g : ι → E →ₗ[K] K) (sample : I → ι) (weight : I → K) (t : E →ₗ[K] K)
    (weights : ∀ i, weight i ≠ 0)
    (mix : ∀ j, ∃ c : I → K, ∀ x, f j x * g j x =
      ∑ k, c k * (f (sample k) x * g (sample k) x))
    (nonzero : ∀ j, ∃ base, f j base * g j base ≠ 0)
    (leading : ∀ x, ∑ i, weight i * (f (sample i) x * g (sample i) x) = (t x)^2)
    (separates : ∀ v, t v = 0 → (∀ j, f j v = 0) → (∀ j, g j v = 0) → v = 0) :
    Module.finrank K E ≤ Fintype.card I := by
  classical
  let a := LinearMap.pi (fun i => f (sample i))
  let b : E →ₗ[K] Module.Dual K (I → K) :=
    ∑ i, (g (sample i)).smulRight (weight i • (LinearMap.proj i : Module.Dual K (I → K)))
  have evalB (x : E) (z : I → K) : b x z = ∑ i, g (sample i) x * (weight i * z i) := by
    simp [b, LinearMap.sum_apply, LinearMap.smulRight_apply]
  have square (x : E) : b x (a x) = (t x)^2 := by
    rw [evalB, ← leading]
    apply Finset.sum_congr rfl
    intro i _
    change g (sample i) x * (weight i * f (sample i) x) = _
    ring
  have dim := split_products_dimension a b t square (by
    intro v ha hb ht
    have hf (i : I) : f (sample i) v = 0 := congrFun ha i
    have hg (i : I) : g (sample i) v = 0 := by
      have zero := evalB v (Pi.single i 1)
      rw [hb] at zero
      simpa [Pi.single_apply, weights, eq_comm] using zero
    obtain ⟨h₁, h₂⟩ := factors_detected_by_samples f g sample mix nonzero hf hg
    exact separates v ht h₁ h₂)
  simpa using dim

/-- A third column with arbitrary mean and both orientations, paired
with two copies of (1,w,w²) in the three-column permanent. -/
theorem doubled_orientation {R : Type*} [CommRing R] (w m u v : R)
    (hw : w^2+w+1 = 0) :
    2*((m+u+v)*w*w^2 + (m+w*u+w^2*v)*w^2 + (m+w^2*u+w*v)*w) = 6*u := by
  linear_combination 2*(m*w+3*u*(w-1)+v*w^2)*hw

/-- Four centered entries whose third elementary symmetric function
vanishes split into opposite pairs. Zeros allow shorter rows as well. -/
theorem four_centered_pairs {R : Type*} [CommRing R] [IsDomain R]
    (a b c d : R) (center : a+b+c+d = 0)
    (cubic : a*b*c + a*b*d + a*c*d + b*c*d = 0) :
    (a = -b ∧ c = -d) ∨ (a = -c ∧ b = -d) ∨ (a = -d ∧ b = -c) := by
  have prod : (a+b)*(a+c)*(b+c) = 0 := by
    linear_combination (a*b+a*c+b*c)*center - cubic
  rcases mul_eq_zero.mp prod with habac | hbc
  · rcases mul_eq_zero.mp habac with hab | hac
    · left
      constructor <;> first | linear_combination hab | linear_combination center - hab
    · right; left
      constructor <;> first | linear_combination hac | linear_combination center - hac
  · right; right
    constructor <;> first | linear_combination center - hbc | linear_combination hbc

private theorem direction_of_constant_cubic {K : Type*} [Field K] [CharZero K]
    (a b m r : K) (identity : ∀ s : K, (a+s*b)*((a+s*b)^2+m) = r) : b = 0 := by
  by_contra hb
  have all_values (x : K) : x*(x^2+m) = r := by
    have reach : a + ((x-a)/b)*b = x := by field_simp; ring
    simpa only [reach] using identity ((x-a)/b)
  have absurd : (6 : K) = 0 := by
    linear_combination all_values 2 - 2 * all_values 1 + all_values 0
  exact (by norm_num : (6 : K) ≠ 0) absurd

/-- In the zero-family case, two coordinates in one orientation
determine the whole space if their weighted difference and the common
cubic are simultaneously nonzero, and the other orientation has a
nonzero weight. The two moments need only be functions. -/
theorem two_coordinates_determine {K E ι : Type*} [Field K] [CharZero K]
    [AddCommGroup E] [Module K E]
    (coord : ι → E →ₗ[K] K) (block : ι → Bool) (weight : ι → K)
    (moment : Bool → E → K) (cubic : E → K)
    (cofactor : ∀ i x, coord i x * ((coord i x)^2 + moment (block i) x) =
      weight i * cubic x)
    (separates : ∀ v, (∀ i, coord i v = 0) → v = 0)
    (p q k : ι) (hp : block p = false) (hq : block q = false)
    (hk : block k = true) (wp : weight p ≠ 0) (wk : weight k ≠ 0)
    (base : E) (nonzero : cubic base ≠ 0)
    (different : weight q * coord p base - weight p * coord q base ≠ 0) :
    Module.finrank K E ≤ 2 := by
  have inj : Function.Injective ((coord p).prod (coord q)) := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have pv : coord p v = 0 := congrArg Prod.fst hv
    have qv : coord q v = 0 := congrArg Prod.snd hv
    let line := fun s : K => base + s • v
    have along (i : ι) (s : K) : coord i (line s) = coord i base + s * coord i v := by
      simp [line]
    have fixed (s : K) : moment false (line s) = moment false base ∧
        cubic (line s) = cubic base := by
      have h₁ := cofactor p (line s)
      have h₂ := cofactor q (line s)
      have h₃ := cofactor p base
      have h₄ := cofactor q base
      simp only [along, hp, hq, pv, qv, mul_zero, add_zero] at h₁ h₂ h₃ h₄
      have zero : (weight q * coord p base - weight p * coord q base) *
          (moment false (line s) - moment false base) = 0 := by
        linear_combination weight q*(h₁-h₃) - weight p*(h₂-h₄)
      have hm := sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left different)
      rw [hm] at h₁
      exact ⟨hm, mul_left_cancel₀ wp (h₁.symm.trans h₃)⟩
    have never (s : K) : coord k (line s) ≠ 0 := by
      intro h
      have eqn := cofactor k (line s)
      rw [h, zero_mul, (fixed s).2] at eqn
      exact (mul_ne_zero wk nonzero) eqn.symm
    have kv : coord k v = 0 := by
      by_contra h
      apply never (-(coord k base / coord k v))
      rw [along]
      field_simp
      ring
    have both (b : Bool) (s : K) : moment b (line s) = moment b base := by
      cases b with
      | false => exact (fixed s).1
      | true =>
        have h := cofactor k (line s)
        have hb := cofactor k base
        simp only [hk, along, kv, mul_zero, add_zero, (fixed s).2] at h hb
        have kb : coord k base ≠ 0 := by simpa [line] using never 0
        exact add_left_cancel (mul_left_cancel₀ kb (h.trans hb.symm))
    apply separates
    intro i
    apply direction_of_constant_cubic (coord i base) (coord i v) (moment (block i) base)
      (weight i * cubic base)
    intro s
    simpa only [along, both, (fixed s).2] using cofactor i (line s)
  simpa [Module.finrank_prod] using
    ((coord p).prod (coord q)).finrank_le_finrank_of_injective inj

end GctFrontier.CofactorConic
