import Bilevel.ChiBoundedChainWeightedLatent

/-! Interior weighted-margin algebra for the actual constructed latent
objective. Radial-coefficient estimates are explicit premises here; this file
does not claim that the full weighted local certificate has been discharged. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiBoundedChain

theorem weightedLatent_terminal_le_receivers (n : ℕ) (ℓ h A ν g hp T w Rp : ℝ)
    (hℓ : 0≤ℓ) (hh : 0<h) (hhp : 0<hp) (hw : 0≤w) (hRp : Rp≤0) (z : Space n) :
    gradient (weightedLatent n ℓ h A ν g hp T w Rp) z (Fin.last n)≤
      w*(positiveReceiverSlope A ν g h hp (z (Fin.last n))+
        negativeReceiverSlope A g h T (z (Fin.last n))) := by
  have hh₀ := weightedLatent_coord_le_payload n ℓ h A ν g hp T w Rp hhp hRp z (Fin.last n)
  rw [payload_gradient,PiLp.add_apply,PiLp.smul_apply] at hh₀
  have hb : basis (Fin.last n) (Fin.last n)=1 := by simp [basis]
  rw [hb,smul_eq_mul,mul_one] at hh₀
  have hc := mul_nonpos_of_nonneg_of_nonpos hw (chain_gradient_nonpos n ℓ h hℓ hh z (Fin.last n))
  nlinarith

theorem negative_coordinate_norm_margin {n : ℕ} (v : Space n) (j : Fin (n+1))
    (m : ℝ) (hj : v j≤-m) : m≤‖v‖ := by
  have hn : |v j|≤‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v j
  linarith [neg_abs_le (v j)]

theorem weighted_interior_active_margin (n : ℕ) (ℓ h A ν g hp T w Rp c q : ℝ)
    (hℓ : 0≤ℓ) (hA : 0≤A) (hν : 0≤ν) (hg : g=ℓ*h) (hh : 0<h) (hhp : 0<hp)
    (hw : 0≤w) (hRp : Rp≤0) (hc : 0≤c) (hq : 2/3≤q) (hwidth : c*h≤w*g/6)
    (z : Space n) (hz : |z (Fin.last n)|<h) :
    w*g/2≤‖c • z+q • gradient (weightedLatent n ℓ h A ν g hp T w Rp) z‖ := by
  have hg0 : 0≤g := by rw [hg];positivity
  obtain ⟨j,hj,hgrad⟩ := weightedLatent_frontier n ℓ h A ν g hp T w Rp hℓ hA hν hg0 hh hhp hw hRp z hz
  rw [← hg] at hgrad
  apply negative_coordinate_norm_margin _ j
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  have hzj : z j≤h := (le_abs_self _).trans hj.le
  have hrad := mul_le_mul_of_nonneg_left hzj hc
  have hgrad0 : gradient (weightedLatent n ℓ h A ν g hp T w Rp) z j≤0 := by nlinarith
  have hqg := mul_le_mul_of_nonpos_right hq hgrad0
  nlinarith

theorem weighted_interior_global_margin (n : ℕ) (ℓ h A ν g hp T w b Rp c q K : ℝ)
    (hℓ : 0≤ℓ) (hA : 3≤A) (hν : 0<ν) (hg : g=ℓ*h) (hh : 0<h) (hhp : 0<hp)
    (hT : 0<T) (hb : 0≤b) (hbw : b≤w) (hRp : Rp≤0) (hK : 1≤K)
    (hTscale : ν*T=K*g) (hclow : b*ν/2≤c) (hcup : c≤5*b*ν/4)
    (hq : 2/3≤q) (hwidth : c*h≤w*g/6) (z : Space n)
    (hQ : releaseGate (z (Fin.last n)/hp)<1) :
    b*g/2≤‖c • z+q • gradient (weightedLatent n ℓ h A ν g hp T w Rp) z‖ := by
  have hw : 0≤w := hb.trans hbw
  have hg0 : 0≤g := by rw [hg];positivity
  have hA0 : 0≤A := by linarith
  have hc0 : 0≤c := le_trans (by positivity) hclow
  have hq0 : 0≤q := by linarith
  by_cases hsmall : |z (Fin.last n)|<h
  · exact (by nlinarith [mul_le_mul_of_nonneg_right hbw hg0] : b*g/2≤w*g/2).trans
      (weighted_interior_active_margin n ℓ h A ν g hp T w Rp c q hℓ hA0 hν.le hg hh hhp hw hRp hc0 hq hwidth z hsmall)
  let t := z (Fin.last n)
  let p := gradient (weightedLatent n ℓ h A ν g hp T w Rp) z (Fin.last n)
  have hp0 : p≤0 := weightedLatent_gradient_nonpos n ℓ h A ν g hp T w Rp hℓ hA0 hν.le hg0 hh hhp hw hRp z (Fin.last n)
  have hpbound := weightedLatent_terminal_le_receivers n ℓ h A ν g hp T w Rp hℓ hh hhp hw hRp z
  change p≤w*(positiveReceiverSlope A ν g h hp t+negativeReceiverSlope A g h T t) at hpbound
  have hqbound := mul_le_mul_of_nonpos_right hq hp0
  have htupper : t<2*hp := by
    by_contra hu
    have he : releaseGate (t/hp)=1 := releaseGate_one ((le_div_iff₀ hhp).mpr (le_of_not_gt hu))
    change releaseGate (t/hp)<1 at hQ
    rw [he] at hQ
    exact lt_irrefl _ hQ
  apply negative_coordinate_norm_margin _ (Fin.last n)
  change c*t+q*p≤-(b*g/2)
  by_cases htpos : 0≤t
  · have hth : h≤t := by
      change ¬|t|<h at hsmall
      rw [abs_of_nonneg htpos] at hsmall
      exact le_of_not_gt hsmall
    have hact := positiveReceiverSlope_active A ν g h hp t hh hhp (by linarith) htupper.le
    have hn := negativeReceiverSlope_nonpos A g h T t hA0 hg0
    have hp₁ : p≤-w*A*(ν*t+g) := by
      rw [hact] at hpbound
      nlinarith only [hpbound,mul_nonpos_of_nonneg_of_nonpos hw hn]
    have harg : 0≤ν*t+g := by positivity
    have hAw := mul_le_mul_of_nonneg_right hA hw
    have hp₂ : p≤-3*w*(ν*t+g) := by
      nlinarith only [hp₁,mul_le_mul_of_nonneg_right hAw harg]
    have hcw : c≤5*w*ν/4 := by nlinarith only [hcup,mul_le_mul_of_nonneg_right hbw hν.le]
    have hrad := mul_le_mul_of_nonneg_right hcw htpos
    have hbg := mul_le_mul_of_nonneg_right hbw hg0
    have hvt : 0≤w*ν*t := by positivity
    nlinarith only [hp₂,hqbound,hrad,hbg,hvt,mul_nonneg hb hg0]
  · have htn : t≤-h := by
      change ¬|t|<h at hsmall
      rw [abs_of_nonpos (le_of_not_ge htpos)] at hsmall
      linarith
    by_cases hmiddle : -T≤t
    · have hact := negativeReceiverSlope_active A g h T t hh hT (by linarith) hmiddle
      have hpplus := positiveReceiverSlope_nonpos A ν g h hp t hA0 hν.le hg0 hh
      have hp₁ : p≤-w*A*g := by
        rw [hact] at hpbound
        nlinarith only [hpbound,mul_nonpos_of_nonneg_of_nonpos hw hpplus]
      have hp₂ : p≤-3*w*g := by
        nlinarith only [hp₁,mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hw) hg0]
      have hrad : c*t≤0 := mul_nonpos_of_nonneg_of_nonpos hc0 (by linarith)
      nlinarith only [hp₂,hqbound,hrad,mul_le_mul_of_nonneg_right hbw hg0,mul_nonneg hb hg0]
    · have htt : t≤-T := le_of_lt (lt_of_not_ge hmiddle)
      have hrad₁ := mul_le_mul_of_nonneg_left htt hc0
      have hrad₂ := mul_le_mul_of_nonneg_right hclow hT.le
      have hscale := congrArg (fun x : ℝ => b*x) hTscale
      dsimp only at hscale
      have hKbg := mul_le_mul_of_nonneg_right hK (mul_nonneg hb hg0)
      have hqp := mul_nonpos_of_nonneg_of_nonpos hq0 hp0
      nlinarith only [hrad₁,hrad₂,hscale,hKbg,hqp]

end Bilevel.ChiBoundedChain
