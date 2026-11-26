import Bilevel.ChiBoundedChainReceiverJetBounds
import Bilevel.ChiBoundedChainJets

/-! Actual higher derivatives of the complete unwrapped local payload. -/
noncomputable section
namespace Bilevel.ChiBoundedChain

theorem payload_jet_sum_bound (n k : ℕ) (hk : k≤3) (ℓ h A ν g hp T B P N : ℝ)
    (hP : 0≤P) (hN : 0≤N) (z : Space n)
    (hchain : ‖iteratedFDeriv ℝ k (chain n ℓ h) z‖≤B)
    (hpos : |iteratedDeriv k (positiveReceiver A ν g h hp) (z (Fin.last n))|≤P)
    (hneg : |iteratedDeriv k (negativeReceiver A g h T) (z (Fin.last n))|≤N) :
    ‖iteratedFDeriv ℝ k (payload n ℓ h A ν g hp T) z‖≤B+P+N := by
  let p := EuclideanSpace.proj (𝕜:=ℝ) (Fin.last n)
  have hcp := (positiveReceiver_contDiff A ν g h hp 3).comp p.contDiff
  have hcn := (negativeReceiver_contDiff A g h T 3).comp p.contDiff
  have hbpos := ZeroChainResidualBounds.scalar_linear_jet_bound (positiveReceiver_contDiff A ν g h hp 3)
    p (ZeroChainResidualBounds.projection_norm_le _) z k hk P hP hpos
  have hbneg := ZeroChainResidualBounds.scalar_linear_jet_bound (negativeReceiver_contDiff A g h T 3)
    p (ZeroChainResidualBounds.projection_norm_le _) z k hk N hN hneg
  have hc := Jets.chain_contDiff n 3 ℓ h
  have hk' : (k : WithTop ℕ∞)≤3 := by exact_mod_cast hk
  change ‖iteratedFDeriv ℝ k (fun w => (chain n ℓ h w+(positiveReceiver A ν g h hp ∘ p) w)+
    (negativeReceiver A g h T ∘ p) w) z‖≤_
  rw [iteratedFDeriv_add_apply' (((hc.add hcp).of_le hk').contDiffAt) ((hcn.of_le hk').contDiffAt),
    iteratedFDeriv_add_apply' ((hc.of_le hk').contDiffAt) ((hcp.of_le hk').contDiffAt)]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hchain hbpos)) hbneg)

theorem payload_source_jets : ∃ C : ℝ,0≤C ∧
    ∀ (n : ℕ) (A ν ℓ h hp T : ℝ),0≤A → 0≤ν → 0<ℓ → 0<h → 0<hp → 0<T →
      ν≤ℓ → h≤hp → h≤T → ∀ z : Space n,
      ‖iteratedFDeriv ℝ 2 (payload n ℓ h A ν (ℓ*h) hp T) z‖≤C*(A+1)*ℓ ∧
      ‖iteratedFDeriv ℝ 3 (payload n ℓ h A ν (ℓ*h) hp T) z‖≤C*(A+1)*ℓ/h := by
  obtain ⟨C₂,hC₂,hb₂⟩ := Jets.chain_jet_two_uniform
  obtain ⟨C₃,hC₃,hb₃⟩ := Jets.chain_jet_three_uniform
  obtain ⟨D,hD,hd⟩ := ReceiverJets.receiver_source_derivatives
  let C := C₂+C₃+2*D
  have hC : 0≤C := by unfold C;positivity
  refine ⟨C,hC,fun n A ν ℓ h hp T hA hν hℓ hh hhp hT hνℓ hhp' hT' z => ?_⟩
  have hreceiver := hd A ν ℓ h hp T hA hν hℓ hh hhp hT hνℓ hhp' hT' (z (Fin.last n))
  have hbsecond := payload_jet_sum_bound n 2 (by norm_num) ℓ h A ν (ℓ*h) hp T (C₂*ℓ) (D*A*ℓ) (D*A*ℓ)
    (by positivity) (by positivity) z (hb₂ n ℓ h hℓ.le hh z) hreceiver.1 hreceiver.2.2.1
  have hbthird := payload_jet_sum_bound n 3 (by norm_num) ℓ h A ν (ℓ*h) hp T (C₃*ℓ/h) (D*A*ℓ/h) (D*A*ℓ/h)
    (by positivity) (by positivity) z (hb₃ n ℓ h hℓ.le hh z) hreceiver.2.1 hreceiver.2.2.2
  have hconst₂ : C₂+2*D*A≤C*(A+1) := by
    unfold C
    nlinarith only [hC₃,hD,mul_nonneg hC₂ hA,mul_nonneg hC₃ hA]
  have hconst₃ : C₃+2*D*A≤C*(A+1) := by
    unfold C
    nlinarith only [hC₂,hD,mul_nonneg hC₂ hA,mul_nonneg hC₃ hA]
  constructor
  · exact hbsecond.trans (by nlinarith only [mul_le_mul_of_nonneg_right hconst₂ hℓ.le])
  · have hs := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hconst₃ hℓ.le) hh.le
    exact hbthird.trans (by convert hs using 1; ring)

end Bilevel.ChiBoundedChain
