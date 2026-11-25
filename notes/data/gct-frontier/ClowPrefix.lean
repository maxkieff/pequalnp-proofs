import Mathlib

set_option autoImplicit false

/-! Squarefree multiplication and the first two transitions of a closed-walk program.
    All the coefficient arguments work over the complex numbers. -/

namespace GctFrontier.ClowPrefix

variable {ι : Type*} [DecidableEq ι]

/-- Multiplication by a linear form in the algebra in which each variable squares to zero. -/
def up (w : ι → ℂ) (f : Finset ι → ℂ) (T : Finset ι) : ℂ :=
  ∑ a ∈ T, w a * f (T.erase a)

private theorem up_insert (w : ι → ℂ) (f : Finset ι → ℂ) (T : Finset ι)
    {i : ι} (hi : i ∉ T) :
    up w f (insert i T) = w i * f T + ∑ a ∈ T, w a * f (insert i (T.erase a)) := by
  classical
  rw [up, Finset.sum_insert hi, Finset.erase_insert hi]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.erase_insert_of_ne (ne_of_mem_of_not_mem ha hi).symm]

private theorem up_cross (w : ι → ℂ) (f : Finset ι → ℂ) (T : Finset ι)
    {i j : ι} (hi : i ∉ T) (hj : j ∉ T) :
    up w (fun S => w j * f (insert i S) - w i * f (insert j S)) T =
      w j * up w f (insert i T) - w i * up w f (insert j T) := by
  classical
  rw [up_insert w f T hi, up_insert w f T hj, up]
  simp only [mul_add, Finset.mul_sum]
  have h := Finset.sum_congr (s₁ := T) (s₂ := T) rfl (fun a _ =>
    show w a * (w j * f (insert i (T.erase a)) - w i * f (insert j (T.erase a))) =
      w j * (w a * f (insert i (T.erase a))) - w i * (w a * f (insert j (T.erase a))) by ring)
  rw [h, Finset.sum_sub_distrib]
  ring

/-- A linear form with more than 2d nonzero coordinates acts injectively from degree d.
    The comparison between two distinguished indices lowers the degree by one. -/
theorem up_injective_degree (d : ℕ) (C G : Finset ι) (w : ι → ℂ) (f : Finset ι → ℂ)
    (hGC : G ⊆ C) (hw : ∀ a ∈ G, w a ≠ 0) (hsize : 2*d < G.card)
    (hker : ∀ T ⊆ C, T.card = d+1 → up w f T = 0) :
    ∀ T ⊆ C, T.card = d → f T = 0 := by
  classical
  induction d generalizing C G f with
  | zero =>
    intro T _ hT
    have he := Finset.card_eq_zero.mp hT
    subst T
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < G.card)
    have hz := hker {a} (Finset.singleton_subset_iff.mpr (hGC ha)) (by simp)
    simpa [up, hw a ha] using hz
  | succ k ih =>
    intro T hTC hT
    obtain ⟨i,hi,hiT⟩ : ∃ i ∈ G, i ∉ T := by
      by_contra! hn
      have hle := Finset.card_le_card (show G ⊆ T from hn)
      omega
    have hiC := hGC hi
    have hwi := hw i hi
    have pair (j : ι) (hj : j ∈ T) :
        w j * f (insert i (T.erase j)) = w i * f T := by
      let C' := (C.erase i).erase j
      let G' := (G.erase i).erase j
      have hG' : G' ⊆ C' := Finset.erase_subset_erase _ (Finset.erase_subset_erase _ hGC)
      have hsub : G' ⊆ G := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have hc₁ := Finset.pred_card_le_card_erase (a := i) (s := G)
      have hc₂ := Finset.pred_card_le_card_erase (a := j) (s := G.erase i)
      have hc : 2*k < G'.card := by dsimp [G']; omega
      let diff (S : Finset ι) := w j * f (insert i S) - w i * f (insert j S)
      have hd (U : Finset ι) (hU : U ⊆ C') (hcard : U.card = k+1) : up w diff U = 0 := by
        have hiU : i ∉ U := fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp (hU h)).2).1 rfl
        have hjU : j ∉ U := fun h => (Finset.mem_erase.mp (hU h)).1 rfl
        have hUC : U ⊆ C := hU.trans ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
        rw [show up w diff U = _ from up_cross w f U hiU hjU,
          hker _ (Finset.insert_subset hiC hUC) (by simp [hiU,hcard]),
          hker _ (Finset.insert_subset (hTC hj) hUC) (by simp [hjU,hcard])]
        ring
      have he : T.erase j ⊆ C' := by
        intro a ha
        obtain ⟨haj,haT⟩ := Finset.mem_erase.mp ha
        exact Finset.mem_erase.mpr ⟨haj, Finset.mem_erase.mpr
          ⟨ne_of_mem_of_not_mem haT hiT, hTC haT⟩⟩
      have hcard : (T.erase j).card = k := by
        have hh := Finset.card_erase_add_one hj
        omega
      have hzero := ih C' G' diff hG' (fun a ha => hw a (hsub ha)) hc hd _ he hcard
      simpa [diff,Finset.insert_erase hj,sub_eq_zero] using hzero
    have hz := hker (insert i T) (Finset.insert_subset hiC hTC) (by simp [hiT,hT])
    rw [up_insert w f T hiT] at hz
    rw [Finset.sum_congr rfl pair] at hz
    have hcalc : ((T.card : ℂ) + 1) * (w i * f T) = 0 := by
      simpa [add_mul, add_comm, nsmul_eq_mul] using hz
    have hpos : (T.card : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : T.card + 1 ≠ 0)
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hcalc).resolve_left hpos)).resolve_left hwi

/-- Coefficients of the squarefree product of the first n row forms. -/
def productCoeff (w : ℕ → ι → ℂ) : ℕ → Finset ι → ℂ
  | 0, T => if T = ∅ then 1 else 0
  | n+1, T => up (w n) (productCoeff w n) T

/-- If row i (starting at zero) has at least 2i+1 nonzero entries, some maximal
    squarefree coefficient of the rectangular matrix is nonzero. -/
theorem exists_nonzero_productCoeff (n : ℕ) (C : Finset ι) (w : ℕ → ι → ℂ)
    (hsupp : ∀ i < n, ∃ G ⊆ C, 2*i < G.card ∧ ∀ a ∈ G, w i a ≠ 0) :
    ∃ T ⊆ C, T.card = n ∧ productCoeff w n T ≠ 0 := by
  classical
  induction n with
  | zero => exact ⟨∅, Finset.empty_subset _, by simp, by simp [productCoeff]⟩
  | succ n ih =>
    obtain ⟨S,hSC,hS,hn⟩ := ih (fun i hi => hsupp i (by omega))
    obtain ⟨G,hGC,hsize,hG⟩ := hsupp n (by omega)
    by_contra! hvan
    exact hn (up_injective_degree n C G (w n) (productCoeff w n)
      hGC hG hsize hvan S hSC hS)

private theorem continuous_productCoeff {P : Type*} [TopologicalSpace P]
    (w : P → ℕ → ι → ℂ) (hw : ∀ i j, Continuous (fun x => w x i j)) (n : ℕ) (T : Finset ι) :
    Continuous (fun x => productCoeff (w x) n T) := by
  induction n generalizing T with
  | zero => exact continuous_const
  | succ k ih =>
    exact continuous_finsetSum _ (fun j _ => (hw k j).mul (ih _))

/-- Compactness gives a common positive margin on every compact family with
    the stipulated row supports. No bounds on downstream program weights enter. -/
theorem uniform_product_gap {P : Type*} [TopologicalSpace P]
    (K : Set P) (hK : IsCompact K) (hne : K.Nonempty) (C : Finset ι) (n : ℕ)
    (w : P → ℕ → ι → ℂ) (hw : ∀ i j, Continuous (fun x => w x i j))
    (hs : ∀ x ∈ K, ∀ i < n, ∃ G ⊆ C, 2*i < G.card ∧ ∀ a ∈ G, w x i a ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ ∑ T ∈ C.powersetCard n, ‖productCoeff (w x) n T‖ := by
  classical
  let total (x : P) := ∑ T ∈ C.powersetCard n, ‖productCoeff (w x) n T‖
  have hcont : Continuous total := continuous_finsetSum _ (fun T _ =>
    (continuous_productCoeff w hw n T).norm)
  obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  obtain ⟨T,hTC,hcard,hT⟩ := exists_nonzero_productCoeff n C (w x) (hs x hx)
  have hle : ‖productCoeff (w x) n T‖ ≤ total x :=
    Finset.single_le_sum (f := fun S => ‖productCoeff (w x) n S‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_powersetCard.mpr ⟨hTC,hcard⟩)
  exact ⟨total x, (norm_pos_iff.mpr hT).trans_le hle, fun y hy => hmin hy⟩

/-- Bounded witnesses survive passage from dense generic prefix data to all
    prefix data as soon as their defining relation is closed. -/
theorem extend_compact_witness {P W : Type*} [TopologicalSpace P] [TopologicalSpace W]
    [CompactSpace W] (D : Set P) (hd : Dense D) (R : Set (P × W)) (hr : IsClosed R)
    (hg : ∀ p ∈ D, ∃ w, (p,w) ∈ R) : ∀ p, ∃ w, (p,w) ∈ R := by
  intro p
  have hsub : D ⊆ Prod.fst '' R := by
    intro x hx
    obtain ⟨w,hw⟩ := hg x hx
    exact ⟨(x,w),hw,rfl⟩
  have hclosed := isClosedMap_fst_of_compactSpace R hr
  obtain ⟨⟨x,w⟩,hw,he⟩ := (hclosed.closure_subset_iff.mpr hsub) (hd p)
  change x = p at he
  exact he ▸ ⟨w,hw⟩

/-- Arbitrary position-dependent suffixes annihilate the same two-step kernel. -/
theorem zero_cut {r b q : ℕ} (p : Fin r → Fin b → Fin q → ℂ)
    (root : Fin r → ℂ) (x : Fin r → Fin b → ℂ) (tail : Fin b → Fin q → ℂ)
    (h : ∀ j k, ∑ i, root i * x i j * p i j k = 0) :
    ∑ j, ∑ k, (∑ i, root i * x i j * p i j k) * tail j k = 0 := by
  simp [h]

/-- A row rescaling of a kernel vector can be paid for in the root row.
    Column rescalings are independent. -/
theorem rescaled_kernel {r b q : ℕ} (p : Fin r → Fin b → Fin q → ℂ)
    (z : Fin r → Fin b → ℂ) (a root : Fin r → ℂ) (v : Fin b → ℂ) (c : ℂ)
    (ha : ∀ i, root i * a i = c) (hz : ∀ j k, ∑ i, z i j * p i j k = 0) :
    ∀ j k, ∑ i, root i * (a i * z i j * v j) * p i j k = 0 := by
  intro j k
  calc
    _ = ∑ i, (c * v j) * (z i j * p i j k) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← ha i]
      ring
    _ = 0 := by rw [← Finset.mul_sum, hz, mul_zero]

/-- A witness may depend on t. Bounded features make coefficientwise convergence
    incompatible with a common positive evaluation gap. -/
theorem no_border_with_gap {n : ℕ} (a : ℕ → Fin n → ℂ) (limit : Fin n → ℂ)
    (feature : ℕ → Fin n → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (converges : ∀ i, Filter.Tendsto (fun t => a t i) Filter.atTop (nhds (limit i)))
    (hb : ∀ t i, ‖feature t i‖ ≤ 1) (hz : ∀ t, ∑ i, a t i * feature t i = 0)
    (hg : ∀ t, δ ≤ ‖∑ i, limit i * feature t i‖) : False := by
  classical
  have hfun : Continuous (fun v : Fin n → ℂ => ∑ i, ‖limit i - v i‖) :=
    continuous_finsetSum _ (fun i _ => (continuous_const.sub (continuous_apply i)).norm)
  have hv : Filter.Tendsto a Filter.atTop (nhds limit) := tendsto_pi_nhds.mpr converges
  have hc := (hfun.tendsto limit).comp hv
  have hsmall := hc.eventually (Iio_mem_nhds (show (∑ i, ‖limit i - limit i‖) < δ by simpa using hδ))
  obtain ⟨t,ht⟩ := hsmall.exists
  change (∑ i, ‖limit i - a t i‖) < δ at ht
  have he : (∑ i, limit i * feature t i) = ∑ i, (limit i - a t i) * feature t i := by
    simp only [sub_mul, Finset.sum_sub_distrib, hz, sub_zero]
  have hle : ‖∑ i, limit i * feature t i‖ ≤ ∑ i, ‖limit i - a t i‖ := by
    rw [he]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hb t i)
  exact (not_lt_of_ge ((hg t).trans hle)) ht

private theorem head_sum (n : ℕ) (M : ℤ) :
    2 * (∑ h ∈ Finset.range n, (M - ((h:ℤ)+1))) = (n:ℤ)*(2*M-n-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    linear_combination ih

/-- Sum the lower bound M-h over all 1 ≤ h ≤ t ≤ T. -/
theorem positive_pairs_count (T : ℕ) (M : ℤ) :
    6 * (∑ t ∈ Finset.range T, ∑ h ∈ Finset.range (t+1), (M - ((h:ℤ)+1))) =
      (T:ℤ)*(T+1)*(3*M-T-2) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ]
    have hh := head_sum (T+1) M
    push_cast at hh ⊢
    linear_combination ih + 3*hh

/-- Six times the contribution from positive forced-prefix lengths for width level s.
    The polynomial expression applies when s²+s+1 ≤ m. -/
def sixTimesCount (m s : ℤ) : ℤ :=
  (m-s^2-s-1) * (m-s^2-s) * (2*m-2*s^2+s-1)

private def sevenLevels (m : ℤ) : ℤ :=
  sixTimesCount m 1 + sixTimesCount m 2 + sixTimesCount m 3 +
  sixTimesCount m 4 + sixTimesCount m 5 + sixTimesCount m 6 + sixTimesCount m 7

/-- The seven width levels already exceed the cubic budget for every m ≥ 71. -/
theorem count_above_cubic {m : ℤ} (hm : 71 ≤ m) : 6*m^3 < sevenLevels m := by
  let x := m-71
  have hx : 0 ≤ x := by dsimp [x]; omega
  have he : sevenLevels m - 6*m^3 = 19176 + 20485*x + 759*x^2 + 8*x^3 := by
    dsimp [sevenLevels,sixTimesCount,x]
    ring
  have hpos : 0 < 19176 + 20485*x + 759*x^2 + 8*x^3 := by positivity
  omega

/-- At seventy include the original root layer, with contribution 350. -/
theorem count_at_seventy :
    sevenLevels 70 = 6*342907 ∧
    (∑ i ∈ Finset.Icc 1 7, (70 - (i:ℤ)^2)) = 350 ∧
    342907 + 350 > (70:ℤ)^3 := by decide

private def sixInput : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0,1,1,1,1,0; 0,0,-1,-1,-1,-1; 0,0,3,3,3,3;
     0,0,-3,-3,-3,-3; 0,0,1,1,1,1; 1,0,0,0,0,0]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 65536 in
theorem six_witness :
    sixInput.permanent = 216 ∧ ∀ b : Fin 6, ∀ k : Fin 3,
      ∑ i : Fin 6, sixInput 0 i * sixInput i b * (i.val : ℤ)^k.val = 0 := by
  decide

end GctFrontier.ClowPrefix
