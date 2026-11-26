import Bilevel.ChiCarrierLocalBudgets
import Bilevel.ChiCarrierNodeJets

/-! An actual recursive Node made from the manuscript's source scales, with
the complete four-order local joint ledger. No local jet bounds are assumed. -/
noncomputable section
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive

def ledgerScale (N ℓ h : ℝ) : ℕ → ℝ
  | 0 => N*ℓ*h^2
  | 1 => ℓ*h*Real.sqrt N
  | 2 => ℓ
  | _+3 => ℓ/h

theorem ledgerScale_nonneg {N ℓ h : ℝ} (hN : 0≤N) (hℓ : 0≤ℓ) (hh : 0≤h) (k : ℕ) :
    0≤ledgerScale N ℓ h k := by
  rcases k with _|_|_|k <;> simp only [ledgerScale] <;> positivity

def sourceNode {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A K ζ cn η CR lp hp r b : ℝ)
    (U : Space (sourceChainIndex cn r η) →ₗᵢ[ℝ] F) : Node F where
  n := sourceChainIndex cn r η
  ell := r*lp
  width := η*hp/r
  receiver := A
  nu := ζ*lp
  force := η*(lp*hp)
  parentWidth := hp
  tailRadius := K*(η*(lp*hp))/(ζ*lp)
  radius := sourceLocalRadius CR lp hp r b ζ
  frame := U

theorem sourceNode_H {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A K ζ cn η CR lp hp r b : ℝ) (U : Space (sourceChainIndex cn r η) →ₗᵢ[ℝ] F) :
    (sourceNode A K ζ cn η CR lp hp r b U).H=sourceLocalPayload A K ζ cn η CR lp hp r b U := rfl

theorem sourceNode_admissible {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A K ζ cn η CR lp hp r b : ℝ) (U : Space (sourceChainIndex cn r η) →ₗᵢ[ℝ] F)
    (hK : 1≤K) (hζ : 0<ζ) (hζ1 : ζ≤1) (hη : 0<η) (hη1 : η≤1)
    (hCR : 1≤CR) (hlp : 0<lp) (hhp : 0<hp) (hr : 1≤r) (hb : 0<b) (hb1 : b≤1) :
    let D := sourceNode A K ζ cn η CR lp hp r b U
    0≤D.ell ∧ 0<D.width ∧ D.width≤D.radius ∧ 0<D.parentWidth ∧ D.parentWidth≤D.radius := by
  have hr0 : 0<r := by linarith
  have hs := source_receiver_scales hlp hhp hr hζ hζ1 hη hη1 hK
  have hrad := source_radius_ge_parent_width hCR hlp hhp hr hb hb1 hζ hζ1
  exact ⟨by dsimp [sourceNode];positivity,by dsimp [sourceNode];positivity,hs.2.1.trans hrad,hhp,hrad⟩

/-- With the source geometry constants fixed, all four actual local joint
derivative orders have one numerical coefficient, uniformly over eta and
therefore also over every sufficiently large base parameter K. -/
theorem sourceNode_joint_ledger (A K ζ cn : ℝ) (hA : 0≤A) (hK : 1≤K)
    (hζ : 0<ζ) (hζ1 : ζ≤1) (hcn : 0<cn) :
    ∃ C : ℝ,1≤C ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F],
    ∀ (η CR lp hp r b : ℝ),0<η → η≤1 → 128≤cn/η^2 →
      1≤CR → ζ*Real.sqrt cn≤CR → 0<lp → 0<hp → 1≤r → 0<b → b≤1 →
      ∀ (U : Space (sourceChainIndex cn r η) →ₗᵢ[ℝ] F) (m j : ℕ) (x : Blocks m F) (k : ℕ),k≤3 →
      ‖iteratedFDeriv ℝ k (jointH m j (sourceNode A K ζ cn η CR lp hp r b U)) x‖≤
        C*ledgerScale (((sourceChainIndex cn r η:ℕ):ℝ)+1) (r*lp) (η*hp/r) k := by
  obtain ⟨Cg,hCg,hsize⟩ := source_local_payload_size
  obtain ⟨Cp,hCp,hjets⟩ := source_local_payload_jets
  have hK0 : 0<K := by linarith
  have hV : 0≤valueConstant A K ζ cn := by
    unfold valueConstant
    have := gaussianBound_nonneg
    positivity
  have hG : 0≤gradientConstant Cg A ζ cn := by unfold gradientConstant;positivity
  let C := 1+valueConstant A K ζ cn+gradientConstant Cg A ζ cn+Cp*(A+1)
  have hC : 1≤C := by unfold C;nlinarith
  have hVC : valueConstant A K ζ cn≤C := by unfold C;nlinarith
  have hGC : gradientConstant Cg A ζ cn≤C := by unfold C;nlinarith
  have hPC : Cp*(A+1)≤C := by unfold C;nlinarith
  refine ⟨C,hC,fun F _ _ _ η CR lp hp r b hη hη1 hlen hCR hCRcn hlp hhp hr hb hb1 U m j x k hk => ?_⟩
  let D := sourceNode A K ζ cn η CR lp hp r b U
  have hr0 : 0<r := by linarith
  have hh : 0<η*hp/r := by positivity
  have hs := hsize F A K ζ cn η CR lp hp r b hA hK0 hζ hcn hη hη1 hlen (by linarith)
    hlp hhp hr hb U (block m j x)
  have hj := hjets F A K ζ cn η CR lp hp r b hA hK hζ hζ1 hcn hη hη1 hlen hCR hCRcn
    hlp hhp hr hb hb1 U (block m j x)
  have hc := block_jet_contraction m j (D.H_contDiff 3) x k hk
  apply hc.trans
  change ‖iteratedFDeriv ℝ k (sourceLocalPayload A K ζ cn η CR lp hp r b U) (block m j x)‖≤_
  interval_cases k
  · rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs]
    apply hs.1.trans
    have hh' := mul_le_mul_of_nonneg_right hVC
      (show 0≤(((sourceChainIndex cn r η:ℕ):ℝ)+1)*(r*lp)*(η*hp/r)^2 by positivity)
    simpa only [ledgerScale,mul_assoc] using hh'
  · rw [Composition.norm_first,← GradientJetBounds.gradient_norm_eq]
    apply hs.2.trans
    have hh' := mul_le_mul_of_nonneg_right hGC
      (show 0≤(r*lp)*(η*hp/r)*Real.sqrt (((sourceChainIndex cn r η:ℕ):ℝ)+1) by positivity)
    simpa only [ledgerScale,mul_assoc] using hh'
  · exact hj.1.trans (mul_le_mul_of_nonneg_right hPC (by positivity))
  · have hh' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hPC
      (show 0≤r*lp by positivity)) hh.le
    exact hj.2.trans (by simpa only [ledgerScale,mul_div_assoc] using hh')

end Bilevel.ChiCarrier
