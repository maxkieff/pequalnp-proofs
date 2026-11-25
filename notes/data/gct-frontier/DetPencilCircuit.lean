import PEqualNP.Gct.Helpers.PolarLift1
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! A division-free straight-line computation of an affine determinant over ℂ. -/

namespace GctFrontier.DetPencilCircuit

open Matrix Polynomial

section Coefficients

variable {R : Type} [CommRing R] {N : ℕ}

private noncomputable def pencil (A : Matrix (Fin N) (Fin N) R) :=
  (1 : Matrix (Fin N) (Fin N) R[X]) + (X : R[X]) • A.map C

private noncomputable def d (A : Matrix (Fin N) (Fin N) R) (k : ℕ) : R :=
  (pencil A).det.coeff k

private noncomputable def B (A : Matrix (Fin N) (Fin N) R) (k : ℕ) :=
  (pencil A).adjugate.map (fun p => p.coeff k)

private theorem coeff_product (Q : Matrix (Fin N) (Fin N) R[X])
    (A : Matrix (Fin N) (Fin N) R) (k : ℕ) (i j : Fin N) :
    ((Q * A.map C) i j).coeff k = (Q.map (fun p => p.coeff k) * A) i j := by
  simp [Matrix.mul_apply, coeff_mul_C]

private theorem scaled_d (A : Matrix (Fin N) (Fin N) R) (k : ℕ) :
    d A (k+1) * (k + 1 : R) = (B A k * A).trace := by
  have hder : (pencil A).map (Polynomial.derivative' : Derivation R R[X] R[X]) = A.map C := by
    ext i j : 1
    by_cases h : i = j <;> simp [pencil, h, Polynomial.derivative'_apply]
  have h := PEqualNP.Gct.Helpers.derivation_det Polynomial.derivative' (pencil A)
  rw [hder] at h
  have hc := congrArg (fun p : R[X] => p.coeff k) h
  simpa [Polynomial.derivative'_apply, coeff_derivative, Matrix.trace, finsetSum_coeff,
    Matrix.diag_apply, coeff_product, B, d] using hc

private theorem B_zero (A : Matrix (Fin N) (Fin N) R) : B A 0 = 1 := by
  let ev : R[X] →+* R := Polynomial.evalRingHom 0
  have he : (pencil A).map ev = 1 := by
    ext i j : 1
    by_cases h : i = j <;> simp [pencil, ev, Matrix.one_apply, h]
  have h := RingHom.map_adjugate ev (pencil A)
  change (pencil A).adjugate.map ev = ((pencil A).map ev).adjugate at h
  rw [he, Matrix.adjugate_one] at h
  simpa [B, ev, coeff_zero_eq_eval_zero] using h

private theorem B_succ (A : Matrix (Fin N) (Fin N) R) (k : ℕ) :
    B A (k+1) = d A (k+1) • (1 : Matrix (Fin N) (Fin N) R) - B A k * A := by
  have h := Matrix.adjugate_mul (pencil A)
  change (pencil A).adjugate * (1 + (X : R[X]) • A.map C) = (pencil A).det • 1 at h
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul] at h
  ext i j : 1
  have hc := congrArg (fun Q : Matrix (Fin N) (Fin N) R[X] => (Q i j).coeff (k+1)) h
  apply eq_sub_of_add_eq
  by_cases hij : i = j <;>
    simpa [Matrix.one_apply, hij, coeff_X_mul, coeff_product, B, d] using hc

private theorem d_top [IsDomain R] (A : Matrix (Fin N) (Fin N) R) :
    d A N = A.det := by
  have he : (pencil A).det = (-A).charpolyRev := by
    rw [Matrix.charpolyRev, Matrix.map_neg C (map_neg C), smul_neg, sub_neg_eq_add]
    rfl
  have h := (-A).det_eq_sign_charpoly_coeff
  rw [Matrix.det_neg, Fintype.card_fin] at h
  have hc : d A N = (-A).charpoly.coeff 0 := by
    simp [d, he, ← Matrix.reverse_charpoly, Polynomial.coeff_reverse]
  exact hc.trans ((mul_left_cancel₀ (by simp : (-1 : R)^N ≠ 0) h).symm)

end Coefficients

section Gates

variable {R : Type} [Ring R]

/-- A binary arithmetic gate can use any value already computed. -/
inductive Gate (S : Set R) : R → Prop
  | add {x y} (hx : x ∈ S) (hy : y ∈ S) : Gate S (x+y)
  | sub {x y} (hx : x ∈ S) (hy : y ∈ S) : Gate S (x-y)
  | mul {x y} (hx : x ∈ S) (hy : y ∈ S) : Gate S (x*y)

/-- The register set after a straight-line program of exactly k binary gates. -/
inductive Steps (S : Set R) : ℕ → Set R → Prop
  | nil : Steps S 0 S
  | cons {k T x} (prev : Steps S k T) (gate : Gate T x) : Steps S (k+1) (insert x T)

private theorem Steps.keep {S T : Set R} {k : ℕ} (h : Steps S k T) : S ⊆ T := by
  induction h with
  | nil => exact Set.Subset.rfl
  | cons _ _ ih => exact ih.trans (Set.subset_insert _ _)

private theorem Steps.append {S T U : Set R} {k j : ℕ}
    (h : Steps S k T) (h' : Steps T j U) : Steps S (k+j) U := by
  induction h' with
  | nil => exact h
  | cons _ gate ih => exact ih.cons gate

/-- A program within budget whose final register set has the stated property. -/
def Within (S : Set R) (b : ℕ) (P : Set R → Prop) : Prop :=
  ∃ k ≤ b, ∃ T, Steps S k T ∧ P T

private theorem ready {S : Set R} {P : Set R → Prop} (h : P S) : Within S 0 P :=
  ⟨0, le_rfl, S, Steps.nil, h⟩

private theorem oneGate {S : Set R} {x : R} (h : Gate S x) :
    Within S 1 (fun T => x ∈ T) :=
  ⟨1, le_rfl, insert x S, Steps.nil.cons h, Set.mem_insert _ _⟩

private theorem Within.map {S : Set R} {P Q : Set R → Prop} {a b : ℕ}
    (h : Within S a P) (hab : a ≤ b) (hq : ∀ T, S ⊆ T → P T → Q T) : Within S b Q := by
  obtain ⟨k, hk, T, ht, hp⟩ := h
  exact ⟨k, hk.trans hab, T, ht, hq T ht.keep hp⟩

private theorem Within.bind {S : Set R} {P Q : Set R → Prop} {a b : ℕ}
    (h : Within S a P) (hq : ∀ T, S ⊆ T → P T → Within T b Q) : Within S (a+b) Q := by
  obtain ⟨k, hk, T, ht, hp⟩ := h
  obtain ⟨j, hj, U, hu, hU⟩ := hq T ht.keep hp
  exact ⟨k+j, Nat.add_le_add hk hj, U, ht.append hu, hU⟩

private theorem gather {ι : Type} [DecidableEq ι] (S : Set R) (s : Finset ι)
    (f : ι → R) (b : ℕ)
    (op : ∀ T, S ⊆ T → ∀ i ∈ s, Within T b (fun U => f i ∈ U)) :
    Within S (s.card*b) (fun U => ∀ i ∈ s, f i ∈ U) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.card_empty, Nat.zero_mul]; exact ready (by simp)
  | insert i s hi ih =>
    have tail := ih (fun T hST j hj => op T hST j (Finset.mem_insert_of_mem hj))
    rw [Finset.card_insert_of_notMem hi, Nat.succ_mul]
    apply tail.bind
    intro T hST ht
    apply (op T hST i (Finset.mem_insert_self _ _)).map le_rfl
    intro U hTU hui j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hui
    · exact hTU (ht _ hj)

private theorem dot {ι : Type} [DecidableEq ι] (S : Set R) (s : Finset ι)
    (x y : ι → R) (h0 : 0 ∈ S) (hx : ∀ i, x i ∈ S) (hy : ∀ i, y i ∈ S) :
    Within S (s.card*2) (fun T => ∑ i ∈ s, x i*y i ∈ T) := by
  induction s using Finset.induction_on with
  | empty => simpa using (ready (S := S) (P := fun T => 0 ∈ T) h0)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.succ_mul]
    apply ih.bind
    intro T hST hsum
    apply (oneGate (Gate.mul (hST (hx i)) (hST (hy i)))).bind (b := 1)
    intro U hTU hprod
    exact oneGate (Gate.add hprod (hTU hsum))

end Gates

open MvPolynomial

/-- The source model gives every scalar and variable as a free input. -/
noncomputable def freeInputs (σ : Type) : Set (MvPolynomial σ ℂ) :=
  Set.range MvPolynomial.C ∪ Set.range MvPolynomial.X

/-- Outputs of circuits with at most s binary additions, subtractions and products. -/
def binaryOutputs (σ : Type) (s : ℕ) : Set (MvPolynomial σ ℂ) :=
  {p | Within (freeInputs σ) s (fun T => p ∈ T)}

private noncomputable def roundCost (N : ℕ) := N^2 * (N*2) + (N*2 + (1 + N^2))

/-- Counts affine-entry gates once and allows all later gates to reuse their values. -/
def pencilCost (v N : ℕ) := N^2 * (v*2 + 1) + N * (N^2 * (N*2) + (N*2 + (1 + N^2)))

private theorem constant_mem {σ : Type} {S : Set (MvPolynomial σ ℂ)}
    (h : freeInputs σ ⊆ S) (c : ℂ) : MvPolynomial.C c ∈ S := h (Or.inl ⟨c, rfl⟩)

private theorem zero_mem {σ : Type} {S : Set (MvPolynomial σ ℂ)}
    (h : freeInputs σ ⊆ S) : 0 ∈ S := by simpa using constant_mem h 0

private theorem one_mem {σ : Type} {S : Set (MvPolynomial σ ℂ)}
    (h : freeInputs σ ⊆ S) : 1 ∈ S := by simpa using constant_mem h 1

private theorem affine_entry {σ : Type} [Fintype σ] [DecidableEq σ]
    {S : Set (MvPolynomial σ ℂ)} (hS : freeInputs σ ⊆ S) (p : MvPolynomial σ ℂ)
    (hp : p.totalDegree ≤ 1) : Within S (Fintype.card σ*2+1) (fun T => p ∈ T) := by
  rw [PEqualNP.Gct.Helpers.affine_normal_form p hp]
  have h := dot S Finset.univ (fun v => MvPolynomial.C (p.coeff (Finsupp.single v 1)))
    MvPolynomial.X (zero_mem hS) (fun _ => constant_mem hS _) (fun v => hS (Or.inr ⟨v,rfl⟩))
  rw [Finset.card_univ] at h
  exact h.bind fun _ hST hsum => oneGate (Gate.add (hST (constant_mem hS _)) hsum)

private theorem unscale_d {σ : Type} {N : ℕ} (A : Matrix (Fin N) (Fin N) (MvPolynomial σ ℂ))
    (k : ℕ) : d A (k+1) = (B A k * A).trace * MvPolynomial.C (((k : ℂ)+1)⁻¹) := by
  have hc : (MvPolynomial.C ((k : ℂ)+1) : MvPolynomial σ ℂ) = k+1 := by simp
  have hn : (k : ℂ)+1 ≠ 0 := by exact_mod_cast (show k+1 ≠ 0 by omega)
  rw [← scaled_d, mul_assoc, ← hc, ← map_mul, mul_inv_cancel₀ hn, map_one, mul_one]

private theorem round_program {σ : Type} {N : ℕ} (A : Matrix (Fin N) (Fin N) (MvPolynomial σ ℂ))
    (k : ℕ) {S : Set (MvPolynomial σ ℂ)} (hS : freeInputs σ ⊆ S)
    (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B A k i j ∈ S) :
    Within S (roundCost N) (fun T => d A (k+1) ∈ T ∧ ∀ i j, B A (k+1) i j ∈ T) := by
  classical
  let U := B A k * A
  have hu : Within S (N^2*(N*2)) (fun T => ∀ i j, U i j ∈ T) := by
    have h := gather S (Finset.univ : Finset (Fin N × Fin N)) (fun ij => U ij.1 ij.2) (N*2)
      (fun T hST ij _ => by
        simpa [U, Matrix.mul_apply] using dot T Finset.univ (B A k ij.1) (fun j => A j ij.2)
          (hST (zero_mem hS)) (fun i => hST (hB _ i)) (fun i => hST (hA i _)))
    simpa [pow_two, Prod.forall] using h
  apply hu.bind
  intro T hST hU
  have htr : Within T (N*2) (fun W => U.trace ∈ W) := by
    simpa [Matrix.trace, Matrix.diag_apply] using dot T (Finset.univ : Finset (Fin N))
      (fun i => U i i) (fun _ => 1) (hST (zero_mem hS)) (fun _ => hU _ _) (fun _ => hST (one_mem hS))
  apply htr.bind
  intro W hTW ht
  have hd : Within W 1 (fun Z => d A (k+1) ∈ Z) := by
    rw [unscale_d]
    exact oneGate (Gate.mul ht (hTW (hST (constant_mem hS _))))
  apply hd.bind
  intro Z hWZ hdz
  have h := gather Z (Finset.univ : Finset (Fin N × Fin N)) (fun ij => B A (k+1) ij.1 ij.2) 1
    (fun Y hZY ij _ => by
      have huij := hZY (hWZ (hTW (hU ij.1 ij.2)))
      rw [B_succ]
      by_cases hij : ij.1 = ij.2
      · simpa [Matrix.one_apply, hij, U] using
          oneGate (Gate.sub (hZY hdz) huij)
      · simpa [Matrix.one_apply, hij, U] using
          oneGate (Gate.sub (hZY (hWZ (hTW (hST (zero_mem hS))))) huij))
  apply h.map (by simp [pow_two])
  exact fun Y hZY hBY => ⟨hZY hdz, fun i j => hBY (i,j) (Finset.mem_univ _)⟩

private theorem det_program {σ : Type} {N : ℕ} (A : Matrix (Fin N) (Fin N) (MvPolynomial σ ℂ))
    {S : Set (MvPolynomial σ ℂ)} (hS : freeInputs σ ⊆ S) (hA : ∀ i j, A i j ∈ S) :
    Within S (N*roundCost N) (fun T => A.det ∈ T) := by
  have h (k : ℕ) : Within S (k*roundCost N)
      (fun T => d A k ∈ T ∧ ∀ i j, B A k i j ∈ T) := by
    induction k with
    | zero =>
      rw [Nat.zero_mul]
      apply ready
      constructor
      · have he : (pencil A).map (Polynomial.evalRingHom 0) = 1 := by
          ext i j : 1
          by_cases hij : i = j <;> simp [pencil, Matrix.one_apply, hij]
        have hd : d A 0 = 1 := by
          rw [d, Polynomial.coeff_zero_eq_eval_zero]
          change Polynomial.evalRingHom 0 _ = _
          rw [RingHom.map_det, RingHom.mapMatrix_apply, he, Matrix.det_one]
        exact hd ▸ one_mem hS
      · intro i j
        rw [B_zero, Matrix.one_apply]
        split <;> first | exact one_mem hS | exact zero_mem hS
    | succ k ih =>
      rw [Nat.succ_mul]
      exact ih.bind fun _ hST hB => round_program A k (hS.trans hST) (fun i j => hST (hA i j)) hB.2
  exact (h N).map le_rfl fun _ _ hresult => d_top A ▸ hresult.1

/-- An affine N by N determinant in v variables has a binary circuit with
N²(2v+1) gates for its entries and N rounds of polynomial cost for the determinant. -/
theorem hasDetExpression_binaryOutputs {σ : Type} [Fintype σ] [DecidableEq σ]
    {p : MvPolynomial σ ℂ} {N : ℕ} (hp : PEqualNP.Gct.HasDetExpression p N) :
    p ∈ binaryOutputs σ (pencilCost (Fintype.card σ) N) := by
  classical
  obtain ⟨A, hA, rfl⟩ := hp
  have h := gather (freeInputs σ) (Finset.univ : Finset (Fin N × Fin N))
    (fun ij => A ij.1 ij.2) (Fintype.card σ*2+1)
    (fun _ hST ij _ => affine_entry hST _ (hA ij.1 ij.2))
  have ha : Within (freeInputs σ) (N^2*(Fintype.card σ*2+1)) (fun T => ∀ i j, A i j ∈ T) := by
    simpa [pow_two, Prod.forall] using h
  exact ha.bind fun _ hST hAT => det_program A hST hAT

end GctFrontier.DetPencilCircuit
