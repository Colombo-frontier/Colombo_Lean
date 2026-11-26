import Bilevel.ChiBoundedChainWrappedJets
import Bilevel.ChiBoundedChainSourceRadius

/-! Source-scale radial payload and its uniform Hessian/third derivative.
The radius hypotheses are purely numerical, independent of the lower weight. -/
noncomputable section
namespace Bilevel.ChiBoundedChain

def sourceLocalPayload {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] (A K ζ cn η CR lp hp r b : ℝ)
    (U : Space (sourceChainIndex cn r η) →ₗᵢ[ℝ] F) : F → ℝ :=
  payload (sourceChainIndex cn r η) (r*lp) (η*hp/r) A (ζ*lp) (η*(lp*hp)) hp
    (K*(η*(lp*hp))/(ζ*lp)) ∘
      WrappedChain.coordinates (sourceChainIndex cn r η) (sourceLocalRadius CR lp hp r b ζ) U

theorem source_radius_ge_parent_width {CR lp hp r b ζ : ℝ}
    (hCR : 1≤CR) (hlp : 0<lp) (hhp : 0<hp) (hr : 1≤r)
    (hb : 0<b) (hb1 : b≤1) (hζ : 0<ζ) (hζ1 : ζ≤1) :
    hp≤sourceLocalRadius CR lp hp r b ζ := by
  have hr0 : 0<r := by linarith
  have hsr : 1≤Real.sqrt r := (Real.le_sqrt (by norm_num) hr0.le).mpr (by nlinarith)
  have hbζ : b*ζ≤1 := by nlinarith
  have hCRsr : 1≤CR*Real.sqrt r := by nlinarith
  have hleft := mul_le_mul_of_nonneg_right hbζ (mul_nonneg hlp.le hhp.le)
  have hright := mul_le_mul_of_nonneg_right hCRsr (mul_nonneg hlp.le hhp.le)
  unfold sourceLocalRadius
  apply (le_div_iff₀ (mul_pos hb (mul_pos hζ hlp))).mpr
  nlinarith only [hleft,hright]

theorem source_radius_ge_chain_width {CR lp hp r b ζ cn η : ℝ}
    (hCR : 1≤CR) (hCRcn : ζ*Real.sqrt cn≤CR)
    (hlp : 0<lp) (hhp : 0<hp) (hr : 1≤r)
    (hb : 0<b) (hb1 : b≤1) (hζ : 0<ζ) (hcn : 0<cn) (hη : 0<η)
    (n : ℕ) (hn : (n:ℝ)+1≤cn*r/η^2) :
    (η*hp/r)*Real.sqrt ((n:ℝ)+1)≤sourceLocalRadius CR lp hp r b ζ := by
  have hr0 : 0<r := by linarith
  have hCR0 : 0≤CR := by linarith
  have hden : 0<b*ζ*Real.sqrt cn := by positivity
  have hbprod := mul_le_mul_of_nonneg_right hb1 (mul_nonneg hζ.le (Real.sqrt_nonneg cn))
  have hCRr := mul_le_mul_of_nonneg_left hr hCR0
  have hquot : 1≤CR*r/(b*ζ*Real.sqrt cn) := (one_le_div hden).mpr (by nlinarith)
  have hratio := source_radius_width_ratio hCR0 hlp hhp hr hb hζ hcn hη n hn
  have hwidth0 : 0<(η*hp/r)*Real.sqrt ((n:ℝ)+1) := by positivity
  simpa only [one_mul] using (le_div_iff₀ hwidth0).mp (hquot.trans hratio)

/-- The actual source payload satisfies the advertised second/third derivative
orders with a single numerical constant independent of lower weight, ratio,
chain length, ambient Hilbert space, and source smallness parameters. -/
theorem source_local_payload_jets : ∃ C : ℝ,0≤C ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F],
    ∀ (A K ζ cn η CR lp hp r b : ℝ),
      0≤A → 1≤K → 0<ζ → ζ≤1 → 0<cn → 0<η → η≤1 → 128≤cn/η^2 →
      1≤CR → ζ*Real.sqrt cn≤CR → 0<lp → 0<hp → 1≤r → 0<b → b≤1 →
      ∀ (U : Space (sourceChainIndex cn r η) →ₗᵢ[ℝ] F) (u : F),
      ‖iteratedFDeriv ℝ 2 (sourceLocalPayload A K ζ cn η CR lp hp r b U) u‖≤C*(A+1)*(r*lp) ∧
      ‖iteratedFDeriv ℝ 3 (sourceLocalPayload A K ζ cn η CR lp hp r b U) u‖≤
        C*(A+1)*(r*lp)/(η*hp/r) := by
  obtain ⟨C,hC,hb⟩ := wrapped_payload_source_jets
  refine ⟨C,hC,fun F _ _ _ A K ζ cn η CR lp hp r b hA hK hζ hζ1 hcn hη hη1 hlen hCR hCRcn
    hlp hhp hr hb0 hb1 U u => ?_⟩
  have hr0 : 0<r := by linarith
  have hK0 : 0<K := by linarith
  have hscales := source_receiver_scales hlp hhp hr hζ hζ1 hη hη1 hK
  have hνℓ : ζ*lp≤r*lp := mul_le_mul_of_nonneg_right (hζ1.trans hr) hlp.le
  have hpR := source_radius_ge_parent_width hCR hlp hhp hr hb0 hb1 hζ hζ1
  have hwidth := source_radius_ge_chain_width hCR hCRcn hlp hhp hr hb0 hb1 hζ hcn hη _
    (sourceChainIndex_length hcn hr hη hlen).2
  have hscale : (r*lp)*(η*hp/r)=η*(lp*hp) := by field_simp;ring
  have hs := hb F (sourceChainIndex cn r η) A (ζ*lp) (r*lp) (η*hp/r) hp
    (K*(η*(lp*hp))/(ζ*lp)) (sourceLocalRadius CR lp hp r b ζ)
    hA (by positivity) (by positivity) (by positivity) hhp (by positivity)
    hνℓ hscales.2.1 hscales.2.2 hpR hwidth U u
  simpa only [hscale,sourceLocalPayload] using hs

end Bilevel.ChiBoundedChain
