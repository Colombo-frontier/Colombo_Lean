import Bilevel.ChiBoundedChainIncomingJets

/-! All actual residual jets through order three have bounds independent of
chain length, proved using the revised incoming-only sources. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiBoundedChain
open ZeroChainPotential
open ZeroChainResidualBounds (jet_mul_bound jet_mul_zero_left jet_mul_zero_right)

def maskedIncoming {n : ℕ} (i : Fin (n+1)) (z : Space n) : ℝ := incoming n i z*tailMask i z

theorem maskedIncoming_contDiff {n : ℕ} (i : Fin (n+1)) : ContDiff ℝ 3 (maskedIncoming i) :=
  (incoming_contDiff n 3 i).mul (tailMask_contDiff i 3)

theorem coordinate_energy_le {n : ℕ} (i j : Fin (n+1)) (z : Space n) (hij : i≤j) :
    coordinateCutoff (z j)^2≤tailEnergy i z := by
  have h := Finset.single_le_sum (f:=fun k : Fin (n+1) =>
    if i≤k then coordinateCutoff (z k)^2 else 0)
    (fun _ _ => by dsimp only;split_ifs <;> positivity) (Finset.mem_univ j)
  simpa only [if_pos hij] using h

theorem masked_jet_flat_small_predecessor {n : ℕ} (i : Fin n) (z : Space n)
    (hz : |z i.castSucc| ≤ 1/2) (k : ℕ) (hk : k ≤ 3) :
    iteratedFDeriv ℝ k (maskedIncoming i.succ) z = 0 :=
  jet_mul_zero_left (incoming_contDiff n 3 i.succ) (tailMask_contDiff i.succ 3) z k hk
    (fun j hj => incoming_succ_flat_jet i z hz j (by omega))

theorem masked_jet_flat_large_tail {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (hij : i ≤ j) (hz : 1/2 ≤ |z j|) (k : ℕ) (hk : k ≤ 3) :
    iteratedFDeriv ℝ k (maskedIncoming i) z = 0 := by
  have he : 1 ≤ tailEnergy i z := by
    have hh := coordinate_energy_le i j z hij
    simpa only [coordinateCutoff_one hz, one_pow] using hh
  exact jet_mul_zero_right (incoming_contDiff n 3 i) (tailMask_contDiff i 3) z k hk
    (fun l hl => tailMask_flat_jet i z he l (by omega))

theorem jet_before_nonzero_later {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (k : ℕ) (hk : k ≤ 3) (hij : i < j)
    (hj : iteratedFDeriv ℝ k (maskedIncoming j) z ≠ 0) :
    iteratedFDeriv ℝ k (maskedIncoming i) z = 0 := by
  revert hij hj
  refine Fin.cases ?_ (fun l => ?_) j
  · intro hij _
    exact (Fin.not_lt_zero i hij).elim
  · intro hij hj
    have hl : 1/2 < |z l.castSucc| := by
      by_contra! hh
      exact hj (masked_jet_flat_small_predecessor l z hh k hk)
    apply masked_jet_flat_large_tail i l.castSucc z ?_ hl.le k hk
    change i.val ≤ l.val
    have hh : i.val < l.val+1 := hij
    omega

/-- The single-active-term property holds for every actual jet through order
three, including the boundaries of the cutoffs. -/
theorem masked_jets_exclusive {n : ℕ} (z : Space n) (k : ℕ) (hk : k ≤ 3)
    (i j : Fin (n+1)) (hij : i ≠ j)
    (hi : iteratedFDeriv ℝ k (maskedIncoming i) z ≠ 0) :
    iteratedFDeriv ℝ k (maskedIncoming j) z = 0 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · by_contra hj
    exact hi (jet_before_nonzero_later i j z k hk hlt hj)
  · exact jet_before_nonzero_later j i z k hk hgt hi

def maskJetBound (C : ℝ) (k : ℕ) : ℝ := (k.factorial:ℝ)*C*(2*C)^k
def residualJetBound (K C : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k+1), (k.choose j:ℝ)*incomingJetBound K j*maskJetBound C (k-j)

theorem maskJetBound_nonneg {C : ℝ} (hC : 0 ≤ C) (k : ℕ) : 0 ≤ maskJetBound C k := by
  dsimp [maskJetBound]
  positivity

theorem residualJetBound_nonneg {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (k : ℕ) :
    0 ≤ residualJetBound K C k := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (incomingJetBound_nonneg hK j))
    (maskJetBound_nonneg hC _)

theorem maskedIncoming_jet_bound {K C : ℝ} (hK : 0 ≤ K) (hC : MaskControl C)
    (hb : ∀ j : Fin 4, ∀ t, |iteratedDeriv j.val psi t| ≤ K ∧ |iteratedDeriv j.val phi t| ≤ K)
    {n : ℕ} (i : Fin (n+1)) (z : Space n) (k : ℕ) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (maskedIncoming i) z‖ ≤ residualJetBound K C k :=
  jet_mul_bound (incoming_contDiff n 3 i) (tailMask_contDiff i 3) z k hk
    (incomingJetBound K) (maskJetBound C) (incomingJetBound_nonneg hK)
    (fun j hj => incoming_jet_bound hK hb n i z j (by omega))
    (fun j hj => tailMask_jet_bound hC i z j (by omega))

theorem norm_sum_le_of_exclusive {ι F : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup F]
    (f : ι → F) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ i, ‖f i‖ ≤ B)
    (he : ∀ i j, i ≠ j → f i ≠ 0 → f j = 0) : ‖∑ i, f i‖ ≤ B := by
  by_cases hf : ∃ i, f i ≠ 0
  · obtain ⟨i,hi⟩ := hf
    rw [Finset.sum_eq_single i]
    · exact hb i
    · intro j _ hji
      exact he i j hji.symm hi
    · simp
  · have hz : ∀ i, f i = 0 := by simpa only [not_exists, not_not] using hf
    simp only [hz, Finset.sum_const_zero, norm_zero]
    exact hB

theorem residual_jet_bound {K C : ℝ} (hK : 0 ≤ K) (hC : MaskControl C)
    (hb : ∀ j : Fin 4, ∀ t, |iteratedDeriv j.val psi t| ≤ K ∧ |iteratedDeriv j.val phi t| ≤ K)
    (n : ℕ) (z : Space n) (k : ℕ) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (residual n) z‖ ≤ residualJetBound K C k := by
  have he : residual n=fun w => ∑ i : Fin (n+1),maskedIncoming i w := by
    funext w
    simp only [residual,residualTerm_eq_incoming,maskedIncoming]
  rw [he]
  rw [iteratedFDeriv_sum (fun i _ => (maskedIncoming_contDiff i).of_le
    (show (k:WithTop ℕ∞) ≤ 3 by exact_mod_cast hk))]
  simp only [Finset.sum_apply]
  exact norm_sum_le_of_exclusive _ _ (residualJetBound_nonneg hK (by linarith [hC.one_le]) k)
    (fun i => maskedIncoming_jet_bound hK hC hb i z k hk) (masked_jets_exclusive z k hk)


theorem residual_uniform_jet_bound : ∃ B : Fin 4 → ℝ,(∀ j,0≤B j) ∧
    ∀ (j : Fin 4) (n : ℕ) (z : Space n),‖iteratedFDeriv ℝ j.val (residual n) z‖≤B j := by
  obtain ⟨K,hK,hb⟩ := chain_profile_bound
  obtain ⟨C,hC⟩ := mask_control_exists
  refine ⟨fun j => residualJetBound K C j.val,fun j => ?_,fun j n z => ?_⟩
  · exact residualJetBound_nonneg (by linarith) (by linarith [hC.one_le]) _
  · exact residual_jet_bound (by linarith) hC hb n z j.val (by omega)

end Bilevel.ChiBoundedChain
