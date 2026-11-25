import PEqualNP.Research.HallSupport

/-! The zero-matching case requested in the project discussion for L-gct-229. -/

theorem PEqualNP.Research.SupportedMatching (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hd : Module.finrank ℂ L = 6)
    (h : ∀ t ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      (if i = j then (2 : ℂ) else 1) + t (i,j)) = 65) :
    ∃ σ : Equiv.Perm (Fin 4), ∀ i, ∃ x ∈ L, x (i,σ i) ≠ 0 := by
  obtain ⟨M, hM, hs⟩ := (PEqualNP.Research.HallSupport L h hd.ge).2
  have hpos : 0 < M.card := by omega
  obtain ⟨σ, hσ⟩ := Finset.card_pos.mp hpos
  exact ⟨σ, hs σ hσ⟩
