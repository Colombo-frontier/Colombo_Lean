import Bilevel.ChiBoundedChainReceiverBounds

/-! The actual bounded receiver-augmented local payload. Its gradient,
coordinate signs, endgame and robust carrier support are derived from its formula. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiBoundedChain

theorem terminal_hasGradientAt {n : ℕ} {f : ℝ → ℝ} {d : ℝ} (z : Space n)
    (hf : HasDerivAt f d (z (Fin.last n))) :
    HasGradientAt (fun w : Space n => f (w (Fin.last n))) (d • basis (Fin.last n)) z := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hf.hasFDerivAt.comp z (EuclideanSpace.proj (𝕜:=ℝ) (Fin.last n)).hasFDerivAt using 1
  ext v
  simp [InnerProductSpace.toDual_apply,inner_basis,ContinuousLinearMap.comp_apply,basis,mul_comm]

theorem chain_differentiable (n : ℕ) (ℓ h : ℝ) : Differentiable ℝ (chain n ℓ h) :=
  (ZeroChainResidualScaled.scaled_contDiff (value_contDiff n 3) (ℓ*h^2) h).differentiable (by norm_num)

def payload (n : ℕ) (ℓ h A ν g hp T : ℝ) (z : Space n) : ℝ :=
  chain n ℓ h z+positiveReceiver A ν g h hp (z (Fin.last n))+
    negativeReceiver A g h T (z (Fin.last n))

def payloadCarrier (n : ℕ) (ℓ h A ν g hp T : ℝ) (z : Space n) : ℝ :=
  payload n ℓ h A ν g hp T z-R n ℓ h z

theorem payload_contDiff (n : ℕ) (ℓ h A ν g hp T : ℝ) (k : ℕ) :
    ContDiff ℝ k (payload n ℓ h A ν g hp T) := by
  have hc : ContDiff ℝ k (chain n ℓ h) :=
    contDiff_const.mul ((value_contDiff n k).comp (contDiff_id.const_smul h⁻¹))
  exact (hc.add ((positiveReceiver_contDiff A ν g h hp k).comp
    (EuclideanSpace.proj (𝕜:=ℝ) (Fin.last n)).contDiff)).add
    ((negativeReceiver_contDiff A g h T k).comp (EuclideanSpace.proj (𝕜:=ℝ) (Fin.last n)).contDiff)

theorem payload_abs_bound (n : ℕ) (ℓ h A ν g hp T : ℝ)
    (hℓ : 0≤ℓ) (hA : 0≤A) (hν : 0≤ν) (hg : 0≤g) (hh : 0<h) (hhp : 0<hp) (hT : 0<T)
    (z : Space n) : |payload n ℓ h A ν g hp T z|≤
      (n+1)*gaussianBound*(ℓ*h^2)+(A*(3*ν*hp+g))*(3*hp)+(A*g)*(2*T) := by
  have hc := chain_abs_bound n ℓ h hℓ z
  have hpbound := positiveReceiver_abs_bound A ν g h hp (z (Fin.last n)) hA hν hg hh hhp
  have hn := negativeReceiver_abs_bound A g h T (z (Fin.last n)) hA hg hh hT
  have ht₀ := abs_add (chain n ℓ h z) (positiveReceiver A ν g h hp (z (Fin.last n)))
  have ht₁ := abs_add (chain n ℓ h z+positiveReceiver A ν g h hp (z (Fin.last n)))
    (negativeReceiver A g h T (z (Fin.last n)))
  unfold payload
  linarith

theorem payload_hasGradientAt (n : ℕ) (ℓ h A ν g hp T : ℝ) (z : Space n) :
    HasGradientAt (payload n ℓ h A ν g hp T)
      (gradient (chain n ℓ h) z+
        (positiveReceiverSlope A ν g h hp (z (Fin.last n))+
          negativeReceiverSlope A g h T (z (Fin.last n))) • basis (Fin.last n)) z := by
  have h₀ := (chain_differentiable n ℓ h z).hasGradientAt
  have h₁ := terminal_hasGradientAt z (positiveReceiver_hasDerivAt A ν g h hp (z (Fin.last n)))
  have h₂ := terminal_hasGradientAt z (negativeReceiver_hasDerivAt A g h T (z (Fin.last n)))
  apply hasGradientAt_iff_hasFDerivAt.mpr
  change HasFDerivAt (fun x => chain n ℓ h x+positiveReceiver A ν g h hp (x (Fin.last n))+
    negativeReceiver A g h T (x (Fin.last n))) _ z
  simpa only [payload,map_add,map_smul,add_smul,add_assoc] using
    (h₀.hasFDerivAt.add h₁.hasFDerivAt).add h₂.hasFDerivAt

theorem payload_gradient (n : ℕ) (ℓ h A ν g hp T : ℝ) (z : Space n) :
    gradient (payload n ℓ h A ν g hp T) z=gradient (chain n ℓ h) z+
      (positiveReceiverSlope A ν g h hp (z (Fin.last n))+
        negativeReceiverSlope A g h T (z (Fin.last n))) • basis (Fin.last n) :=
  (payload_hasGradientAt n ℓ h A ν g hp T z).gradient

theorem receiver_slopes_flat (A ν g h hp T t : ℝ) (hh : 0<h) (ht : |t|≤h/4) :
    positiveReceiverSlope A ν g h hp t=0 ∧ negativeReceiverSlope A g h T t=0 := by
  have h₁ : receiverGate (t/h)=0 := receiverGate_zero ((div_le_iff₀ hh).mpr (by linarith [(abs_le.mp ht).2]))
  have h₂ : receiverGate (-t/h)=0 := receiverGate_zero ((div_le_iff₀ hh).mpr (by linarith [(abs_le.mp ht).1]))
  simp [positiveReceiverSlope,negativeReceiverSlope,h₁,h₂]

theorem payload_gradient_eq_chain (n : ℕ) (ℓ h A ν g hp T : ℝ) (hh : 0<h) (z : Space n)
    (hz : |z (Fin.last n)|≤h/4) :
    gradient (payload n ℓ h A ν g hp T) z=gradient (chain n ℓ h) z := by
  obtain ⟨h₁,h₂⟩ := receiver_slopes_flat A ν g h hp T _ hh hz
  rw [payload_gradient,h₁,h₂,zero_add,zero_smul,add_zero]

theorem payload_gradient_coord_le_chain (n : ℕ) (ℓ h A ν g hp T : ℝ)
    (hA : 0≤A) (hν : 0≤ν) (hg : 0≤g) (hh : 0<h) (z : Space n) (j : Fin (n+1)) :
    gradient (payload n ℓ h A ν g hp T) z j≤gradient (chain n ℓ h) z j := by
  rw [payload_gradient,PiLp.add_apply,PiLp.smul_apply]
  have h₁ := positiveReceiverSlope_nonpos A ν g h hp (z (Fin.last n)) hA hν hg hh
  have h₂ := negativeReceiverSlope_nonpos A g h T (z (Fin.last n)) hA hg
  have hb : 0≤basis (Fin.last n) j := by simp [basis];split_ifs <;> norm_num
  have hm := mul_nonpos_of_nonpos_of_nonneg (add_nonpos h₁ h₂) hb
  simpa only [smul_eq_mul] using add_le_of_nonpos_right hm

theorem payload_gradient_nonpos (n : ℕ) (ℓ h A ν g hp T : ℝ)
    (hℓ : 0≤ℓ) (hA : 0≤A) (hν : 0≤ν) (hg : 0≤g) (hh : 0<h)
    (z : Space n) (j : Fin (n+1)) : gradient (payload n ℓ h A ν g hp T) z j≤0 :=
  (payload_gradient_coord_le_chain n ℓ h A ν g hp T hA hν hg hh z j).trans
    (chain_gradient_nonpos n ℓ h hℓ hh z j)

theorem payload_endgame (n : ℕ) (ℓ h A ν g hp T : ℝ)
    (hℓ : 0≤ℓ) (hA : 0≤A) (hν : 0≤ν) (hg : 0≤g) (hh : 0<h)
    (z : Space n) (hz : |z (Fin.last n)|<h) :
    ℓ*h≤‖gradient (payload n ℓ h A ν g hp T) z‖ := by
  have hz' : |(h⁻¹ • z) (Fin.last n)|<1 := by
    simp only [PiLp.smul_apply,smul_eq_mul,abs_mul,abs_of_pos (inv_pos.mpr hh)]
    exact (inv_mul_lt_iff₀ hh).mpr (by simpa using hz)
  obtain ⟨j,hj⟩ := exists_gradient_coord_le_neg_one n (h⁻¹ • z) hz'
  have hc : gradient (chain n ℓ h) z j≤-(ℓ*h) := by
    rw [chain_gradient n ℓ h hh,PiLp.smul_apply,smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hj (mul_nonneg hℓ hh.le)]
  have hcoord := payload_gradient_coord_le_chain n ℓ h A ν g hp T hA hν hg hh z j
  have hnorm : |gradient (payload n ℓ h A ν g hp T) z j|≤‖gradient (payload n ℓ h A ν g hp T) z‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (gradient (payload n ℓ h A ν g hp T) z) j
  linarith [neg_abs_le (gradient (payload n ℓ h A ν g hp T) z j)]

theorem payloadCarrier_gradient_support (n r : ℕ) (ℓ h A ν g hp T : ℝ) (hh : 0<h)
    (z : Space n) (hz : ∀ j : Fin (n+1),r≤j.val → |z j|≤h/4)
    (j : Fin (n+1)) (hj : r≤j.val) : gradient (payloadCarrier n ℓ h A ν g hp T) z j=0 := by
  have hlast : |z (Fin.last n)|≤h/4 := hz (Fin.last n) (by have := j.isLt;simp;omega)
  have hgrad := payload_gradient_eq_chain n ℓ h A ν g hp T hh z hlast
  have hr := (ZeroChainResidualScaled.scaled_contDiff (residual_contDiff n 3) (ℓ*h^2) h).differentiable (by norm_num)
  change Differentiable ℝ (R n ℓ h) at hr
  have hd : HasGradientAt (payloadCarrier n ℓ h A ν g hp T)
      (gradient (payload n ℓ h A ν g hp T) z-gradient (R n ℓ h) z) z := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    simpa only [payloadCarrier,map_sub] using
      ((payload_hasGradientAt n ℓ h A ν g hp T z).differentiableAt.hasGradientAt.hasFDerivAt).sub
        (hr z).hasGradientAt.hasFDerivAt
  have he : gradient (payloadCarrier n ℓ h A ν g hp T) z=
      gradient (chain n ℓ h) z-gradient (R n ℓ h) z := by
    rw [hgrad] at hd
    exact hd.gradient
  have hbase : HasGradientAt (fun w => chain n ℓ h w-R n ℓ h w)
      (gradient (chain n ℓ h) z-gradient (R n ℓ h) z) z := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    simpa only [map_sub] using (chain_differentiable n ℓ h z).hasGradientAt.hasFDerivAt.sub
      (hr z).hasGradientAt.hasFDerivAt
  have heq : (fun w => chain n ℓ h w-R n ℓ h w)=Bilevel.ChiBoundedChain.A n ℓ h := by
    funext w
    linarith [scaled_exact_split n ℓ h w]
  rw [heq] at hbase
  rw [he,← hbase.gradient]
  exact A_gradient_support n r ℓ h hh z hz j hj

end Bilevel.ChiBoundedChain
