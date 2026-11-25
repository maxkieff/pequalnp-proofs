import Mathlib

/-! Rank tests for ordered coefficients of a corank-one pencil. -/

namespace GctFrontier.MomentRank

open Filter Topology

private theorem fibre_bound {m : ℕ} (S T : Finset (Fin m)) (F : Finset (Equiv.Perm (Fin m)))
    (hmap : ∀ σ ∈ F, S.map σ.toEmbedding = T) :
    F.card ≤ S.card.factorial * (m-S.card).factorial := by
  classical
  by_cases hn : F.Nonempty
  · obtain ⟨τ,hτ⟩ := hn
    have hmem (σ : ↥F) (x : Fin m) : x ∈ S ↔ σ.val x ∈ T := by
      rw [← hmap σ σ.property]
      simp
    let part (σ : ↥F) : (↥S ≃ ↥T) × (↥(Sᶜ) ≃ ↥(Tᶜ)) :=
      (σ.val.subtypeEquiv (hmem σ), σ.val.subtypeEquiv (fun x => by
        simpa only [Finset.mem_compl] using not_congr (hmem σ x)))
    have hinj : Function.Injective part := by
      intro σ ρ he
      apply Subtype.ext
      apply Equiv.ext
      intro x
      by_cases hx : x ∈ S
      · exact congrArg (fun z : (↥S ≃ ↥T) × (↥(Sᶜ) ≃ ↥(Tᶜ)) => (z.1 ⟨x,hx⟩).val) he
      · exact congrArg (fun z : (↥S ≃ ↥T) × (↥(Sᶜ) ≃ ↥(Tᶜ)) =>
          (z.2 ⟨x,Finset.mem_compl.mpr hx⟩).val) he
    have bound := Fintype.card_le_of_injective part hinj
    rw [Fintype.card_prod, Fintype.card_equiv (part ⟨τ,hτ⟩).1,
      Fintype.card_equiv (part ⟨τ,hτ⟩).2] at bound
    simpa [Finset.card_compl] using bound
  · simp [Finset.not_nonempty_iff_eq_empty.mp hn]

/-- Every matching may choose its own row order. A prefix of length k still
    requires at least (m choose k) distinct pairs of used row and column sets. -/
theorem matching_cut_count {m k : ℕ} (hk : k ≤ m)
    (rows : Equiv.Perm (Fin m) → Finset (Fin m)) (hrows : ∀ σ, (rows σ).card = k) :
    m.choose k ≤ (Finset.univ.image (fun σ => (rows σ, (rows σ).map σ.toEmbedding))).card := by
  classical
  let f (σ : Equiv.Perm (Fin m)) := (rows σ, (rows σ).map σ.toEmbedding)
  let pairs := Finset.univ.image f
  let cap := k.factorial * (m-k).factorial
  have hcap : 0 < cap := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have hb (v : Finset (Fin m) × Finset (Fin m)) (hv : v ∈ pairs) :
      (Finset.univ.filter (fun σ => f σ = v)).card ≤ cap := by
    obtain ⟨σ,_,rfl⟩ := Finset.mem_image.mp hv
    apply (fibre_bound (rows σ) ((rows σ).map σ.toEmbedding) _ ?_).trans
    · simp [cap,hrows]
    · intro ρ hρ
      obtain he := (Finset.mem_filter.mp hρ).2
      have h₁ : rows ρ = rows σ := congrArg Prod.fst he
      have h₂ : (rows ρ).map ρ.toEmbedding = (rows σ).map σ.toEmbedding := congrArg Prod.snd he
      exact (congrArg (fun s : Finset (Fin m) => s.map ρ.toEmbedding) h₁.symm).trans h₂
  have hs : m.factorial ≤ pairs.card * cap := calc
    _ = (Finset.univ : Finset (Equiv.Perm (Fin m))).card := by simp [Fintype.card_perm]
    _ = _ := Finset.card_eq_sum_card_image f _
    _ ≤ ∑ _ ∈ pairs, cap := Finset.sum_le_sum hb
    _ = _ := by simp
  have he : m.choose k * cap = m.factorial := by
    simpa [cap, Nat.mul_assoc] using Nat.choose_mul_factorial_mul_factorial hk
  apply (Nat.mul_le_mul_right_iff hcap).mp
  rw [he]
  exact hs

def strictUpper {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if i < j then H i j else 0

/-- Once the selected matching words are placed on the diagonal, every
    upper entry is a shorter word or a degree-m word with a repeated row or
    column. The part of the matrix on these entries has a forced rank. -/
theorem defect_rank {n r : ℕ} (L : Matrix (Fin n) (Fin r) ℂ) (R : Matrix (Fin r) (Fin n) ℂ)
    (hdiag : ∀ i, (L*R) i i ≠ 0) : n ≤ r + (strictUpper (L*R)).rank := by
  let H := L*R
  let U := strictUpper H
  let D := H-U
  have htri : D.IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    simp [D, U, strictUpper, Matrix.sub_apply, hij]
  have hdet : D.det ≠ 0 := by
    rw [D.det_of_isLowerTriangular htri]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    simpa [D,U,H,strictUpper,Matrix.sub_apply] using hdiag i
  have hle : LinearMap.range D.mulVecLin ≤ LinearMap.range H.mulVecLin ⊔
      LinearMap.range U.mulVecLin := by
    rintro y ⟨x,rfl⟩
    change (H-U).mulVec x ∈ _
    rw [Matrix.sub_mulVec]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨x,rfl⟩) (Submodule.mem_sup_right ⟨x,rfl⟩)
  have hr : D.rank ≤ H.rank + U.rank := (Submodule.finrank_mono hle).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
  rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin] at hr
  have hH : H.rank ≤ r := (Matrix.rank_mul_le_left L R).trans (by simpa using L.rank_le_card_width)
  exact hr.trans (Nat.add_le_add_right hH _)

theorem ten_row_defect (L : Matrix (Fin 1022) (Fin 1000) ℂ) (R : Matrix (Fin 1000) (Fin 1022) ℂ)
    (hdiag : ∀ i, (L*R) i i ≠ 0) : 22 ≤ (strictUpper (L*R)).rank := by
  have h := defect_rank L R hdiag
  omega

/-- A shared cut state with q channels cannot converge to identity data on
    more than q compatible histories, even when the factors diverge. -/
theorem border_history_width {n q : ℕ}
    (A : ℕ → Matrix (Fin n) (Fin q) ℂ) (B : ℕ → Matrix (Fin q) (Fin n) ℂ)
    (h : ∀ i j, Tendsto (fun t => (A t * B t) i j) atTop
      (𝓝 ((1 : Matrix (Fin n) (Fin n) ℂ) i j))) : n ≤ q := by
  have hl : Tendsto (fun t => A t * B t) atTop (𝓝 1) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => h i j
  have hd := (continuous_id.matrix_det.tendsto _).comp hl
  obtain ⟨t,ht⟩ := (hd.eventually_ne (by simp : (1 : Matrix (Fin n) (Fin n) ℂ).det ≠ 0)).exists
  change (A t * B t).det ≠ 0 at ht
  have hn := (Matrix.rank_mul_le_left (A t) (B t)).trans (A t).rank_le_card_width
  rw [Matrix.rank_of_det_ne_zero ht] at hn
  simpa using hn

end GctFrontier.MomentRank
