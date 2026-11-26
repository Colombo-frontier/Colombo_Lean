import Bilevel.EndpointTransportPayloadBudgets
import Bilevel.ChiSplitSourceSize

/-! Actual physical payload size and the complete four-order source ledger.
Neither the transport length nor the ambient dimension enters the constant. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier RadialWrapper

theorem physical_payload_contDiff {n D : ℕ} (Q : Rotations n D) (N : Node (Block D)) (k : ℕ) :
    ContDiff ℝ k (physicalPayload Q N) :=
  (ChiSplitChain.payload_contDiff N.n k N.ell N.width N.receiver N.nu N.force N.parentWidth N.tailRadius).comp
    ((ChiSplitChain.readout (sourceReadout Q N.frame) (targetReadout Q N.frame)).contDiff.comp
      (compress_contDiff (gamma n*N.radius) k))

theorem physical_source_payload_size : ∃ Cg : ℝ,0≤Cg ∧
    ∀ (n D : ℕ) (Q : Rotations n D) (A K ζ cn η CR lp hp r b : ℝ),
      0≤A → 0<K → 0<ζ → 0<cn → 0<η → η≤1 → 128≤cn/η^2 →
      0<CR → 0<lp → 0<hp → 1≤r → 0<b →
      ∀ (U : Space (sourceChainIndex cn r η) →ₗᵢ[ℝ] Block D) (Y : Physical n D),
      |physicalPayload Q (sourceNode A K ζ cn η CR lp hp r b U) Y|≤
        valueConstant A K ζ cn*(((sourceChainIndex cn r η:ℕ):ℝ)+1)*((r*lp)*(η*hp/r)^2) ∧
      ‖iteratedFDeriv ℝ 1 (physicalPayload Q (sourceNode A K ζ cn η CR lp hp r b U)) Y‖≤
        (3*gradientConstant Cg A ζ cn)*((r*lp)*(η*hp/r))*Real.sqrt (((sourceChainIndex cn r η:ℕ):ℝ)+1) := by
  obtain ⟨Cg,hCg,hfirst⟩ := ChiSplitChain.source_payload_first_normalized
  refine ⟨Cg,hCg,fun n D Q A K ζ cn η CR lp hp r b hA hK hζ hcn hη hη1 hlen hCR hlp hhp hr hb U Y => ?_⟩
  let N := sourceNode A K ζ cn η CR lp hp r b U
  let P := ChiSplitChain.readout (sourceReadout Q U) (targetReadout Q U)
  let R := gamma n*sourceLocalRadius CR lp hp r b ζ
  let f := ChiSplitChain.payload (sourceChainIndex cn r η) (r*lp) (η*hp/r) A (ζ*lp)
    (η*(lp*hp)) hp (K*(η*(lp*hp))/(ζ*lp))
  have hr0 : 0<r := by linarith only [hr]
  have hR : 0<R := by dsimp [R,sourceLocalRadius]; have hg := gamma_positive n; positivity
  have hc : ContDiff ℝ 3 (P ∘ compress R) := P.contDiff.comp (compress_contDiff R 3)
  have hf : ContDiff ℝ 3 f := ChiSplitChain.payload_contDiff _ _ _ _ _ _ _ _ _
  constructor
  · exact ChiSplitChain.source_payload_value_normalized A K ζ cn η lp hp r hA hK hζ hcn hη hη1 hlp hhp hr hlen _
  · have hj := Composition.first_comp_bound (g:=f) Y (hc.differentiable (by norm_num) Y)
      (hf.differentiable (by norm_num) _)
    have hcoord := (ChiSplitChain.readout_compress_jets P (readout_norm Q U).2.2 R hR Y).1
    have hraw := hfirst A K ζ cn η lp hp r hA hK hζ hcn hη hη1 hlen hlp hhp hr (P (compress R Y))
    have hconst : 0≤gradientConstant Cg A ζ cn := by unfold gradientConstant; positivity
    change ‖iteratedFDeriv ℝ 1 (physicalPayload Q N) Y‖≤_ at hj
    apply hj.trans
    calc
      _≤(gradientConstant Cg A ζ cn*((r*lp)*(η*hp/r))*
        Real.sqrt (((sourceChainIndex cn r η:ℕ):ℝ)+1))*3 := by gcongr; exact hraw
      _=_ := by ring

theorem physical_source_ledger (A K ζ cn : ℝ) (hA : 0≤A) (hK : 1≤K)
    (hζ : 0<ζ) (hζ1 : ζ≤1) (hcn : 0<cn) : ∃ C : ℝ,1≤C ∧
    ∀ (n D : ℕ) (Q : Rotations n D) (η CR lp hp r b : ℝ),0<η → η≤1 → 128≤cn/η^2 →
      1≤CR → ζ*Real.sqrt cn≤CR → 0<lp → 0<hp → 1≤r → 0<b → b≤1 →
      ∀ (U : Space (sourceChainIndex cn r η) →ₗᵢ[ℝ] Block D) (Y : Physical n D) (k : ℕ),k≤3 →
      ‖iteratedFDeriv ℝ k (physicalPayload Q (sourceNode A K ζ cn η CR lp hp r b U)) Y‖≤
        C*ledgerScale (((sourceChainIndex cn r η:ℕ):ℝ)+1) (r*lp) (η*hp/r) k := by
  obtain ⟨Cg,hCg,hsize⟩ := physical_source_payload_size
  obtain ⟨Cp,hCp,hjets⟩ := physical_source_payload_jets
  have hK0 : 0<K := by linarith only [hK]
  have hV : 0≤valueConstant A K ζ cn := by
    unfold valueConstant
    have := gaussianBound_nonneg
    positivity
  have hG : 0≤3*gradientConstant Cg A ζ cn := by unfold gradientConstant; positivity
  let C := 1+valueConstant A K ζ cn+3*gradientConstant Cg A ζ cn+Cp*(A+1)
  have hC : 1≤C := by unfold C; nlinarith
  have hVC : valueConstant A K ζ cn≤C := by unfold C; nlinarith
  have hGC : 3*gradientConstant Cg A ζ cn≤C := by unfold C; nlinarith
  have hPC : Cp*(A+1)≤C := by unfold C; nlinarith
  refine ⟨C,hC,fun n D Q η CR lp hp r b hη hη1 hlen hCR hCRcn hlp hhp hr hb hb1 U Y k hk => ?_⟩
  have hr0 : 0<r := by linarith only [hr]
  have hh : 0<η*hp/r := by positivity
  have hs := hsize n D Q A K ζ cn η CR lp hp r b hA hK0 hζ hcn hη hη1 hlen (by linarith only [hCR]) hlp hhp hr hb U Y
  have hj := hjets n D Q A K ζ cn η CR lp hp r b hA hK hζ hζ1 hcn hη hη1 hlen hCR hCRcn hlp hhp hr hb hb1 U Y
  interval_cases k
  · rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs]
    apply hs.1.trans
    have hv := mul_le_mul_of_nonneg_right hVC
      (show 0≤(((sourceChainIndex cn r η:ℕ):ℝ)+1)*(r*lp)*(η*hp/r)^2 by positivity)
    simpa only [ledgerScale,mul_assoc] using hv
  · apply hs.2.trans
    have hg := mul_le_mul_of_nonneg_right hGC
      (show 0≤(r*lp)*(η*hp/r)*Real.sqrt (((sourceChainIndex cn r η:ℕ):ℝ)+1) by positivity)
    simpa only [ledgerScale,mul_assoc] using hg
  · exact hj.1.trans (mul_le_mul_of_nonneg_right hPC (by positivity))
  · have hh' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hPC (show 0≤r*lp by positivity)) hh.le
    exact hj.2.trans (by simpa only [ledgerScale,mul_div_assoc] using hh')

end Bilevel.EndpointTransportResponse
