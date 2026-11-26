import Bilevel.ChiBoundedChainReceiverJets

/-! Scale-uniform second and third derivatives of the actual receivers.
The common constant is independent of both width ratios hp/h and T/h. -/
noncomputable section
namespace Bilevel.ChiBoundedChain.ReceiverJets

theorem negative_scaled_bound (X B A g h : ℝ) (p : ℕ) (hX : |X|≤B)
    (hA : 0≤A) (hg : 0≤g) (hh : 0<h) : |(-A*g/h^p)*X|≤B*A*g/h^p := by
  rw [abs_mul,abs_div,abs_mul,abs_neg,abs_of_nonneg hA,abs_of_nonneg hg,abs_of_pos (pow_pos hh p)]
  calc
    _ ≤ (A*g/h^p)*B := mul_le_mul_of_nonneg_left hX (by positivity)
    _ = _ := by ring

theorem positive_scaled_bound (X B A g h : ℝ) (p : ℕ) (hX : |X|≤B)
    (hA : 0≤A) (hg : 0≤g) (hh : 0<h) : |(A*g/h^p)*X|≤B*A*g/h^p := by
  simpa only [neg_mul,neg_div,abs_neg] using negative_scaled_bound X B A g h p hX hA hg hh

theorem receiver_uniform_derivatives : ∃ C : ℝ,0≤C ∧
    ∀ (A ν g h hp T : ℝ),0≤A → 0≤ν → 0<g → 0<h → 0<hp → 0<T →
      ν*h≤g → h≤hp → h≤T → ∀ t : ℝ,
      |iteratedDeriv 2 (positiveReceiver A ν g h hp) t|≤C*A*g/h ∧
      |iteratedDeriv 3 (positiveReceiver A ν g h hp) t|≤C*A*g/h^2 ∧
      |iteratedDeriv 2 (negativeReceiver A g h T) t|≤C*A*g/h ∧
      |iteratedDeriv 3 (negativeReceiver A g h T) t|≤C*A*g/h^2 := by
  obtain ⟨B,hB⟩ := profile_control_exists
  have hB0 : 0≤B := by linarith [hB.one_le]
  refine ⟨20*B^2,by positivity,fun A ν g h hp T hA hν hg hh hhp hT hνh hhp' hT' t => ?_⟩
  have ha0 : 0≤ν*h/g := by positivity
  have ha1 : ν*h/g≤1 := (div_le_one hg).mpr hνh
  have hδ0 : 0≤h/hp := by positivity
  have hδ1 : h/hp≤1 := (div_le_one hhp).mpr hhp'
  have hτ0 : 0≤h/T := by positivity
  have hτ1 : h/T≤1 := (div_le_one hT).mpr hT'
  have hp₁ := positiveShapeFirst_bound hB (ν*h/g) (h/hp) (t/h) ha0 ha1 hδ0 hδ1
  have hp₂ := positiveShapeSecond_bound hB (ν*h/g) (h/hp) (t/h) ha0 ha1 hδ0 hδ1
  have hn₁ := negativeShapeFirst_bound hB (h/T) (-t/h) hτ0 hτ1
  have hn₂ := negativeShapeSecond_bound hB (h/T) (-t/h) hτ0 hτ1
  refine ⟨?_,?_,?_,?_⟩
  · rw [positiveReceiver_second A ν g h hp t hg.ne' hh.ne' hhp.ne']
    simpa only [pow_one] using negative_scaled_bound _ (20*B^2) A g h 1
      (hp₁.trans (by nlinarith [sq_nonneg B])) hA hg.le hh
  · rw [positiveReceiver_third A ν g h hp t hg.ne' hh.ne' hhp.ne']
    exact negative_scaled_bound _ _ A g h 2 hp₂ hA hg.le hh
  · rw [negativeReceiver_second A g h T t hh.ne' hT.ne']
    simpa only [pow_one] using positive_scaled_bound _ (20*B^2) A g h 1
      (hn₁.trans (by nlinarith [sq_nonneg B])) hA hg.le hh
  · rw [negativeReceiver_third A g h T t hh.ne' hT.ne']
    exact negative_scaled_bound _ (20*B^2) A g h 2
      (hn₂.trans (by nlinarith [sq_nonneg B])) hA hg.le hh

theorem receiver_source_derivatives : ∃ C : ℝ,0≤C ∧
    ∀ (A ν ℓ h hp T : ℝ),0≤A → 0≤ν → 0<ℓ → 0<h → 0<hp → 0<T →
      ν≤ℓ → h≤hp → h≤T → ∀ t : ℝ,
      |iteratedDeriv 2 (positiveReceiver A ν (ℓ*h) h hp) t|≤C*A*ℓ ∧
      |iteratedDeriv 3 (positiveReceiver A ν (ℓ*h) h hp) t|≤C*A*ℓ/h ∧
      |iteratedDeriv 2 (negativeReceiver A (ℓ*h) h T) t|≤C*A*ℓ ∧
      |iteratedDeriv 3 (negativeReceiver A (ℓ*h) h T) t|≤C*A*ℓ/h := by
  obtain ⟨C,hC,hb⟩ := receiver_uniform_derivatives
  refine ⟨C,hC,fun A ν ℓ h hp T hA hν hℓ hh hhp hT hνℓ hhp' hT' t => ?_⟩
  have hs := hb A ν (ℓ*h) h hp T hA hν (mul_pos hℓ hh) hh hhp hT
    (mul_le_mul_of_nonneg_right hνℓ hh.le) hhp' hT' t
  have he₁ : C*A*(ℓ*h)/h=C*A*ℓ := by field_simp;ring
  have he₂ : C*A*(ℓ*h)/h^2=C*A*ℓ/h := by field_simp;ring
  simpa only [he₁,he₂] using hs

end Bilevel.ChiBoundedChain.ReceiverJets
