import Bilevel.ChiBoundedChainActiveCertificate

/-! Uniform scalar calibration of the constructed local weighted certificate.
The radius constant is numerical and independent of the scale ratio, lower
weight, ambient dimension, and query. The Lean chain index is length minus one. -/
noncomputable section
namespace Bilevel.ChiBoundedChain

def sourceNormConstant (Cg J A ζ cn η Cp : ℝ) : ℝ :=
  Cg*Real.sqrt cn+A*(3*ζ+2*η)+Cp*J

def sourceRadialConstant (Cr A K ζ cn η : ℝ) : ℝ :=
  Cr*cn+2*A*K*η^2/ζ

def sourceRadiusConstant (Cg Cr J A K ζ cn η Cp : ℝ) : ℝ :=
  1+η+4*sourceNormConstant Cg J A ζ cn η Cp+2*ζ*sourceRadialConstant Cr A K ζ cn η

def sourceChainIndex (cn r η : ℝ) : ℕ := Nat.floor (cn*r/η^2)-1

theorem sourceChainIndex_length {cn r η : ℝ} (hcn : 0<cn) (hr : 1≤r) (hη : 0<η)
    (hlen : 128≤cn/η^2) :
    128≤sourceChainIndex cn r η+1 ∧
      ((sourceChainIndex cn r η:ℕ):ℝ)+1≤cn*r/η^2 := by
  have hr0 : 0<r := by linarith
  have hx0 : 0≤cn*r/η^2 := by positivity
  have hx : 128≤cn*r/η^2 := hlen.trans (by
    apply div_le_div_of_nonneg_right _ (sq_nonneg η)
    nlinarith)
  have hf : 128≤Nat.floor (cn*r/η^2) := (Nat.le_floor_iff hx0).mpr (by exact_mod_cast hx)
  have he : sourceChainIndex cn r η+1=Nat.floor (cn*r/η^2) := by
    unfold sourceChainIndex
    omega
  constructor
  · omega
  · have hh := Nat.floor_le hx0
    rw [← he,Nat.cast_add,Nat.cast_one] at hh
    exact hh

theorem scaled_sqrt_chain_length {cn r η : ℝ} (hcn : 0≤cn) (hr : 0≤r) (hη : 0<η)
    (n : ℕ) (hn : (n:ℝ)+1≤cn*r/η^2) :
    η*Real.sqrt ((n:ℝ)+1)≤Real.sqrt cn*Real.sqrt r := by
  have hs := (le_div_iff₀ (sq_pos_of_pos hη)).mp hn
  have hn0 : 0≤(n:ℝ)+1 := by positivity
  have hsqn := Real.sq_sqrt hn0
  have hsqc := Real.sq_sqrt hcn
  have hsqr := Real.sq_sqrt hr
  have hc0 := Real.sqrt_nonneg cn
  have hr0 := Real.sqrt_nonneg r
  have hn0' := Real.sqrt_nonneg ((n:ℝ)+1)
  nlinarith [mul_nonneg hc0 hr0]

theorem source_normBudget_bound (Cg J A ζ cn η Cp lp hp r w Rp : ℝ) (n : ℕ)
    (hCg : 0≤Cg) (hJ : 0≤J) (hA : 0≤A) (hζ : 0<ζ) (hcn : 0<cn) (hη : 0<η)
    (hCp : 0≤Cp) (hlp : 0<lp) (hhp : 0<hp) (hr : 1≤r) (_hw0 : 0≤w) (hw1 : w≤1)
    (hRp : |Rp|≤Cp*lp*hp^2) (hn : (n:ℝ)+1≤cn*r/η^2) :
    normBudget Cg J n (r*lp) (η*hp/r) A (ζ*lp) (η*(lp*hp)) hp w Rp≤
      sourceNormConstant Cg J A ζ cn η Cp*(lp*hp*Real.sqrt r) := by
  have hr0 : 0<r := by linarith
  have hsr : 1≤Real.sqrt r := by exact (Real.le_sqrt (by norm_num) hr0.le).mpr (by nlinarith)
  have hlen := scaled_sqrt_chain_length hcn.le hr0.le hη n hn
  have hchain : Cg*((r*lp)*(η*hp/r))*Real.sqrt ((n:ℝ)+1)≤
      (Cg*Real.sqrt cn)*(lp*hp*Real.sqrt r) := by
    calc
      _ = (Cg*(lp*hp))*(η*Real.sqrt ((n:ℝ)+1)) := by field_simp;ring
      _ ≤ (Cg*(lp*hp))*(Real.sqrt cn*Real.sqrt r) :=
        mul_le_mul_of_nonneg_left hlen (by positivity)
      _ = _ := by ring
  have hrecv : A*(3*(ζ*lp)*hp+η*(lp*hp))+A*(η*(lp*hp))≤
      (A*(3*ζ+2*η))*(lp*hp*Real.sqrt r) := by
    have hh := mul_le_mul_of_nonneg_left hsr (show 0≤A*(3*ζ+2*η)*(lp*hp) by positivity)
    nlinarith only [hh]
  have hrelease : |Rp| * J/hp≤(Cp*J)*(lp*hp*Real.sqrt r) := by
    calc
      _ ≤ (Cp*lp*hp^2)*J/hp := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hRp hJ) hhp.le
      _ = (Cp*J)*(lp*hp) := by field_simp;ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hsr (show 0≤(Cp*J)*(lp*hp) by positivity)
        nlinarith only [hh]
  have hpay : 0≤Cg*((r*lp)*(η*hp/r))*Real.sqrt ((n:ℝ)+1)+
      A*(3*(ζ*lp)*hp+η*(lp*hp))+A*(η*(lp*hp)) := by positivity
  have hw := mul_le_mul_of_nonneg_right hw1 hpay
  unfold normBudget sourceNormConstant
  nlinarith only [hchain,hrecv,hrelease,hw]

theorem source_radialBudget_bound (Cr A K ζ cn η lp hp r w : ℝ) (n : ℕ)
    (hCr : 0≤Cr) (hA : 0≤A) (hK : 0≤K) (hζ : 0<ζ) (_hcn : 0<cn) (hη : 0<η)
    (hlp : 0<lp) (hhp : 0<hp) (hr : 1≤r) (_hw0 : 0≤w) (hw1 : w≤1)
    (hn : (n:ℝ)+1≤cn*r/η^2) :
    radialBudget Cr n (r*lp) (η*hp/r) A (η*(lp*hp)) (K*(η*(lp*hp))/(ζ*lp)) w≤
      sourceRadialConstant Cr A K ζ cn η*(lp*hp^2) := by
  have hr0 : 0<r := by linarith
  have he : (cn*r/η^2)*((r*lp)*(η*hp/r)^2)=cn*(lp*hp^2) := by
    field_simp;ring
  have hchain : ((n:ℝ)+1)*((r*lp)*(η*hp/r)^2)≤cn*(lp*hp^2) := by
    rw [← he]
    exact mul_le_mul_of_nonneg_right hn (by positivity)
  have hchain' := mul_le_mul_of_nonneg_left hchain hCr
  have hrecv : 2*A*(η*(lp*hp))*(K*(η*(lp*hp))/(ζ*lp))=
      (2*A*K*η^2/ζ)*(lp*hp^2) := by field_simp;ring
  have hpay : 0≤Cr*((n:ℝ)+1)*((r*lp)*(η*hp/r)^2)+
      2*A*(η*(lp*hp))*(K*(η*(lp*hp))/(ζ*lp)) := by positivity
  have hw := mul_le_mul_of_nonneg_right hw1 hpay
  unfold radialBudget sourceRadialConstant
  rw [hrecv] at hw ⊢
  nlinarith only [hchain',hw]

theorem sourceRadiusConstant_bounds (Cg Cr J A K ζ cn η Cp : ℝ)
    (hCg : 0≤Cg) (hCr : 0≤Cr) (hJ : 0≤J) (hA : 0≤A) (hK : 0≤K)
    (hζ : 0<ζ) (hcn : 0≤cn) (hη : 0≤η) (hCp : 0≤Cp) :
    let N := sourceNormConstant Cg J A ζ cn η Cp
    let D := sourceRadialConstant Cr A K ζ cn η
    let R := sourceRadiusConstant Cg Cr J A K ζ cn η Cp
    0<R ∧ 4*N≤R ∧ 2*ζ*D≤R^2 ∧ η/2≤2*R/3-N := by
  have hN : 0≤sourceNormConstant Cg J A ζ cn η Cp := by unfold sourceNormConstant;positivity
  have hD : 0≤sourceRadialConstant Cr A K ζ cn η := by unfold sourceRadialConstant;positivity
  dsimp only
  have hR : 1≤sourceRadiusConstant Cg Cr J A K ζ cn η Cp := by
    unfold sourceRadiusConstant
    nlinarith [mul_nonneg hζ.le hD]
  have hsq : sourceRadiusConstant Cg Cr J A K ζ cn η Cp≤
      (sourceRadiusConstant Cg Cr J A K ζ cn η Cp)^2 := by
    nlinarith [sq_nonneg (sourceRadiusConstant Cg Cr J A K ζ cn η Cp-1)]
  refine ⟨by linarith,?_,?_,?_⟩
  · unfold sourceRadiusConstant
    nlinarith
  · apply le_trans _ hsq
    unfold sourceRadiusConstant
    nlinarith
  · unfold sourceRadiusConstant
    nlinarith

def sourceLocalRadius (CR lp hp r b ζ : ℝ) : ℝ :=
  CR*(lp*hp)*Real.sqrt r/(b*(ζ*lp))

theorem scalar_radius_calibration {N D η CR lp hp r b ζ : ℝ}
    (_hN : 0≤N) (hD : 0≤D) (hη : 0≤η) (hCR : 0<CR)
    (hlp : 0<lp) (hhp : 0<hp) (hr : 1≤r) (hb : 0<b) (hb1 : b≤1) (hζ : 0<ζ)
    (hG : 4*N≤CR) (hR : 2*ζ*D≤CR^2) (hex : η/2≤2*CR/3-N) :
    let R := sourceLocalRadius CR lp hp r b ζ
    0<R ∧ 2*(D*(lp*hp^2))≤(b*(ζ*lp))*R^2 ∧
      4*(N*(lp*hp*Real.sqrt r))≤(b*(ζ*lp))*R ∧
      (η*(lp*hp))/2≤2*(b*(ζ*lp))*R/3-N*(lp*hp*Real.sqrt r) := by
  have hr0 : 0<r := by linarith
  have hsr : 1≤Real.sqrt r := (Real.le_sqrt (by norm_num) hr0.le).mpr (by nlinarith)
  have hsqr := Real.sq_sqrt hr0.le
  have hprod : (b*(ζ*lp))*sourceLocalRadius CR lp hp r b ζ=CR*(lp*hp*Real.sqrt r) := by
    unfold sourceLocalRadius
    field_simp
    ring
  have hprod2 : (b*(ζ*lp))*(sourceLocalRadius CR lp hp r b ζ)^2=
      CR^2*(lp*hp^2)*r/(b*ζ) := by
    unfold sourceLocalRadius
    field_simp
    simp only [mul_pow,hsqr]
    ring
  dsimp only
  refine ⟨by unfold sourceLocalRadius;positivity,?_,?_,?_⟩
  · rw [hprod2]
    apply (le_div_iff₀ (mul_pos hb hζ)).mpr
    have hbD : 2*ζ*D*b≤2*ζ*D := by nlinarith [mul_nonneg hζ.le hD]
    have hrr : CR^2≤CR^2*r := by nlinarith [sq_nonneg CR]
    have hh := mul_le_mul_of_nonneg_right (hbD.trans (hR.trans hrr)) (show 0≤lp*hp^2 by positivity)
    nlinarith only [hh]
  · rw [hprod]
    nlinarith only [mul_le_mul_of_nonneg_right hG (show 0≤lp*hp*Real.sqrt r by positivity)]
  · have he := mul_le_mul_of_nonneg_right hex (show 0≤lp*hp*Real.sqrt r by positivity)
    have hlo := mul_le_mul_of_nonneg_left hsr (show 0≤η*(lp*hp)/2 by positivity)
    have hp' : 2*(b*(ζ*lp))*sourceLocalRadius CR lp hp r b ζ=2*(CR*(lp*hp*Real.sqrt r)) := by
      nlinarith only [hprod]
    rw [hp']
    nlinarith only [he,hlo]

end Bilevel.ChiBoundedChain
