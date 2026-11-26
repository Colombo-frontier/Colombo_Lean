import Bilevel.ChiBoundedChainSourceJets
import Bilevel.ChiBoundedChainSourceAmplitude

/-! The actual source local payload in the value/gradient normalization used
by the selected-carrier ledger. Constants are uniform in the source eta. -/
noncomputable section
namespace Bilevel.ChiCarrier
open ChiBoundedChain

theorem source_length_lower {cn r η : ℝ} (hcn : 0<cn) (hr : 1≤r) (hη : 0<η)
    (hlen : 128≤cn/η^2) :
    (cn*r/η^2)/2≤((sourceChainIndex cn r η:ℕ):ℝ)+1 := by
  have hr0 : 0<r := by linarith
  have hx0 : 0≤cn*r/η^2 := by positivity
  have hx : 128≤cn*r/η^2 := hlen.trans (by
    apply div_le_div_of_nonneg_right _ (sq_nonneg η)
    nlinarith)
  have hf : 128≤Nat.floor (cn*r/η^2) := (Nat.le_floor_iff hx0).mpr (by exact_mod_cast hx)
  have he : sourceChainIndex cn r η+1=Nat.floor (cn*r/η^2) := by
    unfold sourceChainIndex
    omega
  have hnext := Nat.lt_floor_add_one (cn*r/η^2)
  have hfreal : (128:ℝ)≤(Nat.floor (cn*r/η^2):ℝ) := by exact_mod_cast hf
  have hcount : ((sourceChainIndex cn r η:ℕ):ℝ)+1=(Nat.floor (cn*r/η^2):ℝ) := by exact_mod_cast he
  rw [hcount]
  linarith

theorem source_sqrt_length_lower {cn r η : ℝ} (hcn : 0<cn) (hr : 1≤r) (hη : 0<η)
    (hlen : 128≤cn/η^2) :
    Real.sqrt (cn/2)*Real.sqrt r≤η*Real.sqrt (((sourceChainIndex cn r η:ℕ):ℝ)+1) := by
  have hn := source_length_lower hcn hr hη hlen
  have hr0 : 0≤r := by linarith
  have hn0 : 0≤((sourceChainIndex cn r η:ℕ):ℝ)+1 := by positivity
  have hc0 : 0≤cn/2 := by positivity
  have hsqn := Real.sq_sqrt hn0
  have hsqr := Real.sq_sqrt hr0
  have hsqc := Real.sq_sqrt hc0
  have hcn0 := Real.sqrt_nonneg (cn/2)
  have hrn0 := Real.sqrt_nonneg r
  have hnn0 := Real.sqrt_nonneg (((sourceChainIndex cn r η:ℕ):ℝ)+1)
  have hn' : cn*r/2≤(((sourceChainIndex cn r η:ℕ):ℝ)+1)*η^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hη)).mp
    convert hn using 1
    ring
  apply (sq_le_sq₀ (mul_nonneg hcn0 hrn0) (mul_nonneg hη.le hnn0)).mp
  rw [mul_pow,mul_pow,hsqc,hsqr,hsqn]
  nlinarith only [hn']

def valueConstant (A K ζ cn : ℝ) : ℝ :=
  2*(gaussianBound*cn+3*A*(3*ζ+1)+2*A*K/ζ)/cn

def gradientConstant (Cg A ζ cn : ℝ) : ℝ :=
  (Cg*Real.sqrt cn+A*(3*ζ+2))/Real.sqrt (cn/2)

theorem amplitude_uniform_eta {A K ζ cn η : ℝ} (hA : 0≤A) (hK : 0≤K)
    (hζ : 0<ζ) (hη : 0≤η) (hη1 : η≤1) :
    sourceAmplitudeConstant A K ζ cn η≤gaussianBound*cn+3*A*(3*ζ+1)+2*A*K/ζ := by
  have hηsq : η^2≤1 := by nlinarith
  have hfirst := mul_le_mul_of_nonneg_left hη1 (show 0≤3*A by positivity)
  have hsecond := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hηsq (show 0≤2*A*K by positivity)) hζ.le
  simp only [mul_one] at hsecond
  unfold sourceAmplitudeConstant
  nlinarith only [hfirst,hsecond]

theorem source_payload_value_normalized (A K ζ cn η lp hp r : ℝ)
    (hA : 0≤A) (hK : 0<K) (hζ : 0<ζ) (hcn : 0<cn) (hη : 0<η) (hη1 : η≤1)
    (hlp : 0<lp) (hhp : 0<hp) (hr : 1≤r) (hlen : 128≤cn/η^2)
    (z : Space (sourceChainIndex cn r η)) :
    |payload (sourceChainIndex cn r η) (r*lp) (η*hp/r) A (ζ*lp) (η*(lp*hp)) hp
      (K*(η*(lp*hp))/(ζ*lp)) z|≤
      valueConstant A K ζ cn*(((sourceChainIndex cn r η:ℕ):ℝ)+1)*((r*lp)*(η*hp/r)^2) := by
  have hr0 : 0<r := by linarith
  have hb := source_payload_amplitude A K ζ cn η lp hp r _ hA hK hζ hcn hη hlp hhp hr
    (sourceChainIndex_length hcn hr hη hlen).2 z
  have hmax := mul_le_mul_of_nonneg_right (amplitude_uniform_eta (cn:=cn) hA hK.le hζ hη.le hη1)
    (show 0≤lp*hp^2 by positivity)
  have hconstant : 0≤valueConstant A K ζ cn := by
    unfold valueConstant
    have := gaussianBound_nonneg
    positivity
  have he := mul_le_mul_of_nonneg_right (source_length_lower hcn hr hη hlen)
    (show 0≤(r*lp)*(η*hp/r)^2 by positivity)
  have heq : (cn*r/η^2/2)*((r*lp)*(η*hp/r)^2)=(cn/2)*(lp*hp^2) := by field_simp;ring
  rw [heq] at he
  have henergy := mul_le_mul_of_nonneg_left he hconstant
  have hcancel : valueConstant A K ζ cn*((cn/2)*(lp*hp^2))=
      (gaussianBound*cn+3*A*(3*ζ+1)+2*A*K/ζ)*(lp*hp^2) := by
    unfold valueConstant
    field_simp
    ring
  rw [hcancel] at henergy
  exact hb.trans (hmax.trans (by convert henergy using 1;ring))

theorem carried_gradient_contraction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (n : ℕ) (f : Space n → ℝ) (hf : ContDiff ℝ 1 f)
    (R : ℝ) (hR : 0<R) (U : Space n →ₗᵢ[ℝ] E) (u : E) :
    ‖gradient (f ∘ WrappedChain.coordinates n R U) u‖≤
      ‖gradient f (WrappedChain.coordinates n R U u)‖ := by
  have hc := ZeroChainWrappedResidual.coordinates_contDiff n R U
  have hz := (frame_coordinates_jets n R hR U u).1
  calc
    _ = ‖iteratedFDeriv ℝ 1 (f ∘ WrappedChain.coordinates n R U) u‖ := by
      rw [Composition.norm_first,GradientJetBounds.gradient_norm_eq]
    _ ≤ ‖iteratedFDeriv ℝ 1 f (WrappedChain.coordinates n R U u)‖*
        ‖iteratedFDeriv ℝ 1 (WrappedChain.coordinates n R U) u‖ :=
      Composition.first_comp_bound u (hc.differentiable (by norm_num) u) (hf.differentiable (by norm_num) _)
    _ ≤ ‖iteratedFDeriv ℝ 1 f (WrappedChain.coordinates n R U u)‖*1 :=
      mul_le_mul_of_nonneg_left hz (norm_nonneg _)
    _ = _ := by rw [mul_one,Composition.norm_first,GradientJetBounds.gradient_norm_eq]

theorem source_local_payload_size : ∃ Cg : ℝ,0≤Cg ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F],
    ∀ (A K ζ cn η CR lp hp r b : ℝ),
      0≤A → 0<K → 0<ζ → 0<cn → 0<η → η≤1 → 128≤cn/η^2 →
      0<CR → 0<lp → 0<hp → 1≤r → 0<b →
      ∀ (U : Space (sourceChainIndex cn r η) →ₗᵢ[ℝ] F) (u : F),
      |sourceLocalPayload A K ζ cn η CR lp hp r b U u|≤
        valueConstant A K ζ cn*(((sourceChainIndex cn r η:ℕ):ℝ)+1)*((r*lp)*(η*hp/r)^2) ∧
      ‖gradient (sourceLocalPayload A K ζ cn η CR lp hp r b U) u‖≤
        gradientConstant Cg A ζ cn*((r*lp)*(η*hp/r))*
          Real.sqrt (((sourceChainIndex cn r η:ℕ):ℝ)+1) := by
  obtain ⟨Cg,hCg,hchain⟩ := Size.chain_gradient_norm_uniform
  refine ⟨Cg,hCg,fun F _ _ _ A K ζ cn η CR lp hp r b hA hK hζ hcn hη hη1 hlen hCR
    hlp hhp hr hb U u => ?_⟩
  let n := sourceChainIndex cn r η
  let R := sourceLocalRadius CR lp hp r b ζ
  have hr0 : 0<r := by linarith
  have hR : 0<R := by dsimp [R,sourceLocalRadius];positivity
  have hh : 0<η*hp/r := by positivity
  have he : (r*lp)*(η*hp/r)=η*(lp*hp) := by field_simp;ring
  constructor
  · exact source_payload_value_normalized A K ζ cn η lp hp r hA hK hζ hcn hη hη1 hlp hhp hr hlen _
  · have hcon := carried_gradient_contraction n
      (payload n (r*lp) (η*hp/r) A (ζ*lp) (η*(lp*hp)) hp (K*(η*(lp*hp))/(ζ*lp)))
      (payload_contDiff n _ _ _ _ _ _ _ 1) R hR U u
    have hgrad := payload_gradient_norm_le n (r*lp) (η*hp/r) A (ζ*lp) (η*(lp*hp)) hp
      (K*(η*(lp*hp))/(ζ*lp)) _ hA (by positivity) (by positivity) hh hhp
      (WrappedChain.coordinates n R U u) (hchain n _ _ (by positivity) hh _)
    have hbudget := source_normBudget_bound Cg 0 A ζ cn η 0 lp hp r 1 0 n
      hCg (by norm_num) hA hζ hcn hη (by norm_num) hlp hhp hr (by norm_num) (by norm_num)
      (by simp) (sourceChainIndex_length hcn hr hη hlen).2
    simp only [normBudget,one_mul,abs_zero,zero_mul,zero_div,add_zero] at hbudget
    have hN : sourceNormConstant Cg 0 A ζ cn η 0≤Cg*Real.sqrt cn+A*(3*ζ+2) := by
      unfold sourceNormConstant
      nlinarith only [mul_le_mul_of_nonneg_left hη1 hA]
    have hN0 : 0≤Cg*Real.sqrt cn+A*(3*ζ+2) := by positivity
    have hs := mul_le_mul_of_nonneg_left (source_sqrt_length_lower hcn hr hη hlen)
      (show 0≤lp*hp by positivity)
    have hsqrt : 0<Real.sqrt (cn/2) := by positivity
    have hnorm : (lp*hp*Real.sqrt r)≤
        (((r*lp)*(η*hp/r))*Real.sqrt ((n:ℝ)+1))/Real.sqrt (cn/2) := by
      apply (le_div_iff₀ hsqrt).mpr
      rw [he]
      dsimp [n]
      nlinarith only [hs]
    have hb₁ := mul_le_mul_of_nonneg_right hN (show 0≤lp*hp*Real.sqrt r by positivity)
    have hb₂ := mul_le_mul_of_nonneg_left hnorm hN0
    have hfinal := hcon.trans (hgrad.trans (hbudget.trans (hb₁.trans hb₂)))
    convert hfinal using 1
    unfold gradientConstant
    ring

end Bilevel.ChiCarrier
