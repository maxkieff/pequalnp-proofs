import Mathlib.Algebra.Ring.Commute
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace GctFrontier

/-- The coefficient of two copies of one cube-root orientation and one
copy of the opposite orientation in the three-column permanent. -/
theorem cubic_mixed_orientations {A : Type*} [CommRing A] (w : A)
    (hw : w^2 + w + 1 = 0) (a b c d e f : A) :
    let second := fun (u v : A) => w*u + w^2*v
    let third := fun (u v : A) => w^2*u + w*v
    (a+b) * (second c d * third e f + second e f * third c d) +
      (c+d) * (second a b * third e f + second e f * third a b) +
      (e+f) * (second a b * third c d + second c d * third a b) =
      6 * (a*c*e + b*d*f) := by
  dsimp
  linear_combination
    (6*(w-1)*(a*c*e+b*d*f) +
      2*w^2*(b*c*e+a*d*e+a*c*f+a*d*f+b*c*f+b*d*e)) * hw

/-- If the product of two linear forms is constant and nonzero on a line,
both factors are constant there. -/
theorem factor_vanishes_on_direction {K E : Type*} [Field K]
    [AddCommGroup E] [Module K E] (f g U V : E →ₗ[K] K)
    (product_eq : ∀ x, f x * g x = U x * V x)
    {base dir : E} (nonzero : U base * V base ≠ 0)
    (hU : U dir = 0) (hV : V dir = 0) : f dir = 0 := by
  by_contra hd
  let c := -(f base / f dir)
  have zero : f base + c * f dir = 0 := by simp [c, hd]
  have h := product_eq (base + c • dir)
  simp only [map_add, map_smul, smul_eq_mul, hU, hV, mul_zero, add_zero, zero, zero_mul] at h
  exact nonzero h.symm

/-- The two totals determine the whole space if the factorizations
separate points and the totals are simultaneously nonzero somewhere. -/
theorem dimension_of_product_identities {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] (f g : ι → E →ₗ[K] K) (U V : E →ₗ[K] K)
    (product_eq : ∀ j x, f j x * g j x = U x * V x)
    (separates : ∀ x, U x = 0 → V x = 0 → (∀ j, f j x = 0) → (∀ j, g j x = 0) → x = 0)
    (nonzero : ∃ y, U y * V y ≠ 0) : Module.finrank K E ≤ 2 := by
  obtain ⟨y, hy⟩ := nonzero
  have inj : Function.Injective (U.prod V) := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hu : U x = 0 := congrArg Prod.fst hx
    have hv : V x = 0 := congrArg Prod.snd hx
    apply separates x hu hv
    · intro j
      exact factor_vanishes_on_direction _ _ _ _ (product_eq j) hy hu hv
    · intro j
      exact factor_vanishes_on_direction (g j) (f j) U V
        (fun t => (mul_comm ..).trans (product_eq j t)) hy hu hv
  simpa [Module.finrank_prod] using (U.prod V).finrank_le_finrank_of_injective inj

/-- For a fixed cube-root orientation, the cubic cofactor equation
forces every active coordinate to be one fixed form up to sign. -/
theorem signed_generator {A ι : Type*} [CommRing A] [IsDomain A]
    (t : ι → A) (moment : A) (two : (2 : A) ≠ 0)
    (cofactor : ∀ j, t j * (moment - 2 * t j ^ 2) = 0) :
    ∃ u : A, ∀ j, t j = 0 ∨ t j = u ∨ t j = -u := by
  by_cases h : ∃ k, t k ≠ 0
  · obtain ⟨k, hk⟩ := h
    refine ⟨t k, fun j => ?_⟩
    by_cases hj : t j = 0
    · exact Or.inl hj
    · have coeff (i) (hi : t i ≠ 0) : moment = 2 * t i ^ 2 :=
        sub_eq_zero.mp ((mul_eq_zero.mp (cofactor i)).resolve_left hi)
      exact Or.inr (sq_eq_sq_iff_eq_or_eq_neg.mp (mul_left_cancel₀ two
        ((coeff j hj).symm.trans (coeff k hk))))
  · exact ⟨0, fun j => Or.inl (by by_contra hj; exact h ⟨j, hj⟩)⟩

end GctFrontier
