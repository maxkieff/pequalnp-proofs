import OrbitSeparation
import DetPencilCircuit

/-! Specialization of the November 24 border-circuit lower bound to L-gct-011. -/

namespace GctFrontier.BorderCircuitTransfer

open MvPolynomial PEqualNP.Gct OrbitSeparation DetPencilCircuit Filter Topology

/-- The characteristic-zero permanent instance of Theorem 1.1, with binary
arithmetic gates and only the degree-m output coefficients observed. -/
def PermanentBorderCircuitBound : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∃ M : ℕ, ∀ m ≥ M, ∀ s : ℕ,
    InDegreeClosure m (binaryOutputs (Fin m × Fin m) s) (permPoly ℂ m) →
    Real.exp (a * Real.log m ^ 2 / Real.log (Real.log m) ^ 2) ≤ s

private theorem pencil_hasDetExpression {σ : Type} [Fintype σ] (N : ℕ)
    (a : Fin N → Fin N → Option σ → ℂ) : HasDetExpression (pencilDet N a) N := by
  refine ⟨Matrix.of fun i j => C (a i j none) + ∑ v, C (a i j (some v)) * X v, ?_, rfl⟩
  intro i j
  apply (totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply totalDegree_finsetSum_le
    intro v _
    exact (totalDegree_mul _ _).trans (by simp)

/-- An equation valid on the larger binary-circuit model holds throughout
the Zariski closure of degree-m observations of the affine pencil family. -/
theorem circuitClosure_of_pencilClosure {m N : ℕ}
    (h : InDegreeClosure m (Set.range (pencilDet (σ := Fin m × Fin m) N)) (permPoly ℂ m)) :
    InDegreeClosure m (binaryOutputs (Fin m × Fin m) (pencilCost (m^2) N)) (permPoly ℂ m) := by
  intro F hF
  apply h F
  rintro _ ⟨a, rfl⟩
  apply hF
  simpa [pow_two] using hasDetExpression_binaryOutputs (pencil_hasDetExpression N a)

private theorem cost_le {v N t : ℕ} (hv : v ≤ t) (hN : N ≤ t) (ht : 1 ≤ t) :
    pencilCost v N ≤ 9*t^4 := by
  calc
    pencilCost v N ≤ pencilCost t t := by unfold pencilCost; gcongr
    _ = 2*t^4 + 3*t^3 + 3*t^2 + t := by unfold pencilCost; ring
    _ ≤ _ := by
      have h₁ : t ≤ t^4 := Nat.le_self_pow (by decide) _
      have h₂ : t^2 ≤ t^4 := Nat.pow_le_pow_right ht (by decide)
      have h₃ : t^3 ≤ t^4 := Nat.pow_le_pow_right ht (by decide)
      omega

/-- All constants are uniform in matrix order. Passing from the binary gate
lower bound to matrix order loses only an absolute factor in the exponent. -/
theorem pencil_bound_of_circuit_bound (h : PermanentBorderCircuitBound) : QuantitativePencilBound := by
  obtain ⟨a, ha, M, hbound⟩ := h
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_pow_le_bound ha 9)
  obtain ⟨V, hV⟩ := eventually_atTop.mp
    (eventually_pow_le_bound (show 0 < a/2 by positivity) 1)
  refine ⟨a/8, by positivity, max (max M T) (max V 10), ?_⟩
  intro m hm N hclosure
  have hmM : M ≤ m := le_trans (le_trans (le_max_left M T) (le_max_left _ _)) hm
  have hmT : T ≤ m := le_trans (le_trans (le_max_right M T) (le_max_left _ _)) hm
  have hmV : V ≤ m := le_trans (le_trans (le_max_left V 10) (le_max_right _ _)) hm
  have hm₁₀ : 10 ≤ m := le_trans (le_trans (le_max_right V 10) (le_max_right _ _)) hm
  have hm₂ : 1 ≤ m^2 := Nat.one_le_pow _ _ (by omega)
  have hgate := hbound m hmM _ (circuitClosure_of_pencilClosure hclosure)
  have hsize : m^2 ≤ N := by
    by_contra! hlt
    have h₉ : m^9 ≤ pencilCost (m^2) N := by exact_mod_cast (hT m hmT).trans hgate
    have hnat := h₉.trans (cost_le (le_refl (m^2)) hlt.le hm₂)
    have hpos : 0 < m^8 := by positivity
    rw [← pow_mul] at hnat
    change m^9 ≤ 9*m^8 at hnat
    rw [show (9 : ℕ) = 8+1 from rfl, pow_succ, Nat.mul_comm (m^8) m] at hnat
    nlinarith
  have hcost : (pencilCost (m^2) N : ℝ) ≤ 9*(N : ℝ)^4 := by
    exact_mod_cast cost_le hsize (le_refl N) (hm₂.trans hsize)
  let y := Real.exp (a/8 * Real.log m^2 / Real.log (Real.log m)^2)
  have hfour : y^4 = Real.exp (a/2 * Real.log m^2 / Real.log (Real.log m)^2) := by
    dsimp [y]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have height : y^8 = Real.exp (a * Real.log m^2 / Real.log (Real.log m)^2) := by
    dsimp [y]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hlarge : (9 : ℝ) ≤ y^4 := by
    rw [hfour]
    have hvm := hV m hmV
    simp only [pow_one] at hvm
    exact le_trans (by exact_mod_cast (show 9 ≤ m by omega)) hvm
  change y ≤ N
  by_contra! hsmall
  have hstrict : 9*(N : ℝ)^4 < 9*y^4 := by gcongr
  have himpossible : y^8 < y^8 := calc
    y^8 ≤ 9*(N : ℝ)^4 := height ▸ hgate.trans hcost
    _ < 9*y^4 := hstrict
    _ ≤ y^4*y^4 := by gcongr
    _ = y^8 := by ring
  exact lt_irrefl _ himpossible

/-- The exact mathematical statement listed by pequalnp, with Theorem 1.1
as its sole external mathematical input. -/
theorem L_gct_011_of_border_circuit_bound (h : PermanentBorderCircuitBound) :
    ∀ c : ℕ, 1 ≤ c → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      paddedPerm ℂ m (m^c) ∉ orbitClosure (detPoly ℂ (m^c+1)) :=
  L_gct_011_of_pencil_bound (pencil_bound_of_circuit_bound h)

end GctFrontier.BorderCircuitTransfer
