import Bilevel.EndpointTransportPayload
import Bilevel.ChiSplitWrappedPayload
import Bilevel.ChiCarrierSourceNode

/-! Actual full-vector physical leaf budgets. The source radius conditions
are inherited without a factor depending on the transport length. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier RadialWrapper

theorem gamma_range (n : ℕ) : 1≤gamma n ∧ gamma n≤2 := by
  have h0 := gamma_positive n
  have hb := gamma_sq_bounds n
  constructor <;> nlinarith only [h0,hb.1,hb.2]

theorem physical_payload_jets : ∃ C : ℝ,0≤C ∧ ∀ (n D : ℕ) (Q : Rotations n D)
    (N : Node (Block D)),0≤N.receiver → 0≤N.nu → 0<N.ell → 0<N.width →
    0<N.parentWidth → 0<N.tailRadius → N.nu≤N.ell → N.width≤N.parentWidth →
    N.width≤N.tailRadius → N.parentWidth≤N.radius →
    N.width*Real.sqrt ((N.n:ℝ)+1)≤N.radius → N.force=N.ell*N.width →
    ∀ Y : Physical n D,
      ‖iteratedFDeriv ℝ 1 (physicalPayload Q N) Y‖≤C*(N.receiver+1)*N.ell*(gamma n*N.radius) ∧
      ‖iteratedFDeriv ℝ 2 (physicalPayload Q N) Y‖≤C*(N.receiver+1)*N.ell ∧
      ‖iteratedFDeriv ℝ 3 (physicalPayload Q N) Y‖≤C*(N.receiver+1)*N.ell/N.width := by
  obtain ⟨C,hC,hb⟩ := ChiSplitChain.wrapped_payload_source_jets
  refine ⟨C,hC,fun n D Q N hA hν hell hh hhp hT hνell hhp' hT' hpR hwidth hforce Y => ?_⟩
  have hR : 0<N.radius := hhp.trans_le hpR
  have hRph : N.radius≤gamma n*N.radius := by nlinarith only [(gamma_range n).1,mul_le_mul_of_nonneg_right (gamma_range n).1 hR.le]
  have hj := hb (Physical n D) N.n N.receiver N.nu N.ell N.width N.parentWidth N.tailRadius
    (gamma n*N.radius) hA hν hell hh hhp hT hνell hhp' hT' (hpR.trans hRph) (hwidth.trans hRph)
    (ChiSplitChain.readout (sourceReadout Q N.frame) (targetReadout Q N.frame)) (readout_norm Q N.frame).2.2 Y
  have he : physicalPayload Q N=ChiSplitChain.payload N.n N.ell N.width N.receiver N.nu (N.ell*N.width)
      N.parentWidth N.tailRadius ∘
      ChiSplitChain.readout (sourceReadout Q N.frame) (targetReadout Q N.frame) ∘ compress (gamma n*N.radius) := by
    funext y
    simp only [physicalPayload,physicalCoordinates,hforce,Function.comp_apply]
  rw [he]
  exact hj

theorem physical_source_payload_jets : ∃ C : ℝ,0≤C ∧
    ∀ (n D : ℕ) (Q : Rotations n D) (A K ζ cn η CR lp hp r b : ℝ),
      0≤A → 1≤K → 0<ζ → ζ≤1 → 0<cn → 0<η → η≤1 → 128≤cn/η^2 →
      1≤CR → ζ*Real.sqrt cn≤CR → 0<lp → 0<hp → 1≤r → 0<b → b≤1 →
      ∀ (U : Space (sourceChainIndex cn r η) →ₗᵢ[ℝ] Block D) (Y : Physical n D),
      ‖iteratedFDeriv ℝ 2 (physicalPayload Q (sourceNode A K ζ cn η CR lp hp r b U)) Y‖≤C*(A+1)*(r*lp) ∧
      ‖iteratedFDeriv ℝ 3 (physicalPayload Q (sourceNode A K ζ cn η CR lp hp r b U)) Y‖≤
        C*(A+1)*(r*lp)/(η*hp/r) := by
  obtain ⟨C,hC,hb⟩ := physical_payload_jets
  refine ⟨C,hC,fun n D Q A K ζ cn η CR lp hp r b hA hK hζ hζ1 hcn hη hη1 hlen hCR hCRcn
    hlp hhp hr hb0 hb1 U Y => ?_⟩
  have hr0 : 0<r := by linarith only [hr]
  have hK0 : 0<K := by linarith only [hK]
  have hs := source_receiver_scales hlp hhp hr hζ hζ1 hη hη1 hK
  have hpR := source_radius_ge_parent_width hCR hlp hhp hr hb0 hb1 hζ hζ1
  have hwR := source_radius_ge_chain_width hCR hCRcn hlp hhp hr hb0 hb1 hζ hcn hη
    (sourceChainIndex cn r η) (sourceChainIndex_length hcn hr hη hlen).2
  have hf : η*(lp*hp)=(r*lp)*(η*hp/r) := by field_simp; ring
  have hνell : ζ*lp≤r*lp := mul_le_mul_of_nonneg_right (hζ1.trans hr) hlp.le
  have hj := hb n D Q (sourceNode A K ζ cn η CR lp hp r b U) hA
    (by dsimp [sourceNode]; positivity) (by dsimp [sourceNode]; positivity)
    (by dsimp [sourceNode]; positivity) hhp (by dsimp [sourceNode]; positivity)
    hνell hs.2.1 hs.2.2 hpR hwR hf Y
  exact hj.2

end Bilevel.EndpointTransportResponse
