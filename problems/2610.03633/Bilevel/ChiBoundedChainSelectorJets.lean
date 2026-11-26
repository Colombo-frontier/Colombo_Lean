import Bilevel.ChiBoundedChainResidualJets

/-! Higher-jet disjointness and numerical selector bounds for the revised
construction, including cutoff boundaries and distinct derivative orders. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiBoundedChain
open ZeroChainResidualBounds (projection_norm_le jet_mul_bound jet_mul_zero_left jet_mul_zero_right)

theorem selector_succ_flat_jet {n : ℕ} (i : Fin n) (z : Space n)
    (hz : |z i.castSucc|≤1/2) (k : ℕ) (hk : k≤3) :
    iteratedFDeriv ℝ k (selector n i.succ) z=0 :=
  jet_mul_zero_left ((evenGate_contDiff 3).comp (EuclideanSpace.proj (𝕜:=ℝ) i.castSucc).contDiff)
    (tailMask_contDiff i.succ 3) z k hk (fun j hj =>
      evenGate_linear_flat _ (projection_norm_le _) z hz j (by omega))

theorem selector_flat_large_tail {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (hij : i≤j) (hz : 1/2≤|z j|) (k : ℕ) (hk : k≤3) :
    iteratedFDeriv ℝ k (selector n i) z=0 := by
  have he : 1≤tailEnergy i z := by
    have hh := coordinate_energy_le i j z hij
    simpa only [coordinateCutoff_one hz,one_pow] using hh
  revert he
  refine Fin.cases (fun he => tailMask_flat_jet 0 z he k hk) (fun l he => ?_) i
  exact jet_mul_zero_right ((evenGate_contDiff 3).comp (EuclideanSpace.proj (𝕜:=ℝ) l.castSucc).contDiff)
    (tailMask_contDiff l.succ 3) z k hk (fun j hj => tailMask_flat_jet l.succ z he j (by omega))

theorem selector_jet_before_later {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (k l : ℕ) (hk : k≤3) (hl : l≤3) (hij : i<j)
    (hj : iteratedFDeriv ℝ l (selector n j) z≠0) :
    iteratedFDeriv ℝ k (selector n i) z=0 := by
  revert hij hj
  refine Fin.cases (by intro h;exact False.elim (Fin.not_lt_zero i h)) (fun m => ?_) j
  intro him hm
  have hp : 1/2 < |z m.castSucc| := by
    by_contra! hp
    exact hm (selector_succ_flat_jet m z hp l hl)
  apply selector_flat_large_tail i m.castSucc z _ hp.le k hk
  change i.val≤m.val
  change i.val<m.val+1 at him
  omega

theorem selector_jets_unique {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (k l : ℕ) (hk : k≤3) (hl : l≤3)
    (hi : iteratedFDeriv ℝ k (selector n i) z≠0)
    (hj : iteratedFDeriv ℝ l (selector n j) z≠0) : i=j := by
  rcases lt_trichotomy i j with hij|hij|hji
  · exact False.elim (hi (selector_jet_before_later i j z k l hk hl hij hj))
  · exact hij
  · exact False.elim (hj (selector_jet_before_later j i z l k hl hk hji hi))

theorem selector_active_jet_tail_small {n : ℕ} (i : Fin (n+1)) (z : Space n)
    (k : ℕ) (hk : k≤3) (hi : iteratedFDeriv ℝ k (selector n i) z≠0)
    (j : Fin (n+1)) (hij : i≤j) : |z j|<1/2 := by
  by_contra hb
  exact hi (selector_flat_large_tail i j z hij (le_of_not_gt hb) k hk)

def selectorJetBound (K C : ℝ) (k : ℕ) : ℝ := maskJetBound C k+
  ∑ j ∈ Finset.range (k+1),(k.choose j:ℝ)*(2*K)*maskJetBound C (k-j)

theorem selectorJetBound_nonneg {K C : ℝ} (hK : 0≤K) (hC : 0≤C) (k : ℕ) :
    0≤selectorJetBound K C k := by
  unfold selectorJetBound
  apply add_nonneg (maskJetBound_nonneg hC k)
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (by positivity) (maskJetBound_nonneg hC _)

theorem selector_jet_bound {K C : ℝ} (hK : 0≤K) (hC : MaskControl C)
    (hb : ∀ j : Fin 4,∀ t,|iteratedDeriv j.val psi t|≤K)
    (n : ℕ) (i : Fin (n+1)) (z : Space n) (k : ℕ) (hk : k≤3) :
    ‖iteratedFDeriv ℝ k (selector n i) z‖≤selectorJetBound K C k := by
  have hC0 : 0≤C := by linarith [hC.one_le]
  have hs : 0≤∑ j ∈ Finset.range (k+1),(k.choose j:ℝ)*(2*K)*maskJetBound C (k-j) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (maskJetBound_nonneg hC0 _))
  refine Fin.cases ?_ (fun m => ?_) i
  · exact (tailMask_jet_bound hC 0 z k hk).trans (le_add_of_nonneg_right hs)
  · have hh := jet_mul_bound ((evenGate_contDiff 3).comp (EuclideanSpace.proj (𝕜:=ℝ) m.castSucc).contDiff)
      (tailMask_contDiff m.succ 3) z k hk (fun _ => 2*K) (maskJetBound C)
      (fun _ => by positivity)
      (fun j hj => evenGate_linear_jet_bound _ (projection_norm_le _) z j (by omega) K hK (hb ⟨j,by omega⟩))
      (fun j hj => tailMask_jet_bound hC m.succ z j (by omega))
    exact hh.trans (le_add_of_nonneg_left (maskJetBound_nonneg hC0 k))

theorem selector_uniform_jet_bound : ∃ B : Fin 4 → ℝ,(∀ j,0≤B j) ∧
    ∀ (j : Fin 4) (n : ℕ) (i : Fin (n+1)) (z : Space n),
      ‖iteratedFDeriv ℝ j.val (selector n i) z‖≤B j := by
  obtain ⟨K,hK,hb⟩ := chain_profile_bound
  obtain ⟨C,hC⟩ := mask_control_exists
  refine ⟨fun j => selectorJetBound K C j.val,fun j => ?_,fun j n i z => ?_⟩
  · exact selectorJetBound_nonneg (by linarith) (by linarith [hC.one_le]) _
  · exact selector_jet_bound (by linarith) hC (fun j t => (hb j t).1) n i z j.val (by omega)

theorem R_uniform_jet_bound : ∃ B : Fin 4 → ℝ,(∀ j,0≤B j) ∧
    ∀ (j : Fin 4) (n : ℕ) (ℓ h : ℝ),0≤ℓ → 0<h → ∀ z : Space n,
      ‖iteratedFDeriv ℝ j.val (R n ℓ h) z‖≤B j*(ℓ*h^2)/h^j.val := by
  obtain ⟨B,hB,hb⟩ := residual_uniform_jet_bound
  refine ⟨B,hB,fun j n ℓ h hℓ hh z => ?_⟩
  exact ZeroChainResidualScaled.scaled_jet_bound (residual_contDiff n 3) (ℓ*h^2) h
    (B j) (by positivity) hh j.val (by omega) (hb j n) z

end Bilevel.ChiBoundedChain
