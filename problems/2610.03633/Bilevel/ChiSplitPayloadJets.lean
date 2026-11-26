import Bilevel.ChiSplitPayload
import Bilevel.ChiSplitChainSize
import Bilevel.ChiSplitChainThird
import Bilevel.ChiBoundedChainPayloadJets

/-! Actual complete split-payload derivatives, with both receivers read at the
predecessor endpoint and uniform constants through order three. -/
noncomputable section
namespace Bilevel.ChiSplitChain
open ChiBoundedChain

theorem target_projection_norm {n : ℕ} (i : Fin (n+1)) :
    ‖(targetProjection i : Latent n →L[ℝ] ℝ)‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa only [targetProjection_apply,Real.norm_eq_abs,one_mul] using (split_coordinate_bound z i).2

theorem payload_jet_sum_bound (n k : ℕ) (hk : k≤3) (ℓ h A ν g hp T B P N : ℝ)
    (hP : 0≤P) (hN : 0≤N) (z : Latent n)
    (hchain : ‖iteratedFDeriv ℝ k (chain n ℓ h) z‖≤B)
    (hpos : |iteratedDeriv k (positiveReceiver A ν g h hp) (z.snd (Fin.last n))|≤P)
    (hneg : |iteratedDeriv k (negativeReceiver A g h T) (z.snd (Fin.last n))|≤N) :
    ‖iteratedFDeriv ℝ k (payload n ℓ h A ν g hp T) z‖≤B+P+N := by
  let p : Latent n →L[ℝ] ℝ := targetProjection (Fin.last n)
  have hcp := (positiveReceiver_contDiff A ν g h hp 3).comp p.contDiff
  have hcn := (negativeReceiver_contDiff A g h T 3).comp p.contDiff
  have hbpos := ZeroChainResidualBounds.scalar_linear_jet_bound (positiveReceiver_contDiff A ν g h hp 3)
    p (target_projection_norm _) z k hk P hP hpos
  have hbneg := ZeroChainResidualBounds.scalar_linear_jet_bound (negativeReceiver_contDiff A g h T 3)
    p (target_projection_norm _) z k hk N hN hneg
  have hc := chain_contDiff n 3 ℓ h
  have hk' : (k : WithTop ℕ∞)≤3 := by exact_mod_cast hk
  change ‖iteratedFDeriv ℝ k (fun w => (chain n ℓ h w+(positiveReceiver A ν g h hp ∘ p) w)+
    (negativeReceiver A g h T ∘ p) w) z‖≤_
  rw [iteratedFDeriv_add_apply' (((hc.add hcp).of_le hk').contDiffAt) ((hcn.of_le hk').contDiffAt),
    iteratedFDeriv_add_apply' ((hc.of_le hk').contDiffAt) ((hcp.of_le hk').contDiffAt)]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hchain hbpos)) hbneg)

theorem payload_source_jets : ∃ C : ℝ,0≤C ∧
    ∀ (n : ℕ) (A ν ℓ h hp T : ℝ),0≤A → 0≤ν → 0<ℓ → 0<h → 0<hp → 0<T →
      ν≤ℓ → h≤hp → h≤T → ∀ z : Latent n,
      ‖iteratedFDeriv ℝ 2 (payload n ℓ h A ν (ℓ*h) hp T) z‖≤C*(A+1)*ℓ ∧
      ‖iteratedFDeriv ℝ 3 (payload n ℓ h A ν (ℓ*h) hp T) z‖≤C*(A+1)*ℓ/h := by
  obtain ⟨C₂,hC₂,hb₂⟩ := chain_jet_two_uniform
  obtain ⟨C₃,hC₃,hb₃⟩ := chain_jet_three_uniform
  obtain ⟨D,hD,hd⟩ := ReceiverJets.receiver_source_derivatives
  let C := C₂+C₃+2*D
  have hC : 0≤C := by unfold C;positivity
  refine ⟨C,hC,fun n A ν ℓ h hp T hA hν hℓ hh hhp hT hνℓ hhp' hT' z => ?_⟩
  have hreceiver := hd A ν ℓ h hp T hA hν hℓ hh hhp hT hνℓ hhp' hT' (z.snd (Fin.last n))
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


theorem payload_first_bound (n : ℕ) (ell h A ν g hp T G : ℝ)
    (hA : 0≤A) (hν : 0≤ν) (hg : 0≤g) (hh : 0<h) (hhp : 0<hp) (z : Latent n)
    (hG : ‖iteratedFDeriv ℝ 1 (chain n ell h) z‖≤G) :
    ‖iteratedFDeriv ℝ 1 (payload n ell h A ν g hp T) z‖≤G+A*(3*ν*hp+g)+A*g := by
  apply payload_jet_sum_bound n 1 (by norm_num) ell h A ν g hp T G (A*(3*ν*hp+g)) (A*g)
    (by positivity) (by positivity) z hG
  · rw [iteratedDeriv_one,(positiveReceiver_hasDerivAt A ν g h hp _).deriv]
    exact positiveReceiverSlope_abs_bound A ν g h hp _ hA hν hg hh hhp
  · rw [iteratedDeriv_one,(negativeReceiver_hasDerivAt A g h T _).deriv]
    exact negativeReceiverSlope_abs_bound A g h T _ hA hg

theorem payload_first_uniform : ∃ C : ℝ,0≤C ∧ ∀ (n : ℕ) (ell h A ν g hp T : ℝ),
    0≤ell → 0≤A → 0≤ν → 0≤g → 0<h → 0<hp → ∀ z : Latent n,
    ‖iteratedFDeriv ℝ 1 (payload n ell h A ν g hp T) z‖≤
      C*(ell*h)*Real.sqrt ((n:ℝ)+1)+A*(3*ν*hp+g)+A*g := by
  obtain ⟨C,hC,hb⟩ := chain_first_uniform
  exact ⟨C,hC,fun n ell h A ν g hp T hell hA hν hg hh hhp z =>
    payload_first_bound n ell h A ν g hp T _ hA hν hg hh hhp z (hb n ell h hell hh z)⟩

end Bilevel.ChiSplitChain
