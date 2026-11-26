import Bilevel.ChiSplitWrappedJets

/-! Numerical radius calibration for the complete physical split payload.
All three derivative bounds use the same fixed dimension-independent constant. -/
noncomputable section
namespace Bilevel.ChiSplitChain
open ChiBoundedChain RadialWrapper

theorem wrapped_payload_source_jets : ∃ C : ℝ,0≤C ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    ∀ (n : ℕ) (A ν ell h hp T R : ℝ),0≤A → 0≤ν → 0<ell → 0<h → 0<hp → 0<T →
      ν≤ell → h≤hp → h≤T → hp≤R → h*Real.sqrt ((n:ℝ)+1)≤R →
      ∀ (P : E →L[ℝ] Latent n),‖P‖≤3 → ∀ u : E,
      ‖iteratedFDeriv ℝ 1 (payload n ell h A ν (ell*h) hp T ∘ P ∘ compress R) u‖≤C*(A+1)*ell*R ∧
      ‖iteratedFDeriv ℝ 2 (payload n ell h A ν (ell*h) hp T ∘ P ∘ compress R) u‖≤C*(A+1)*ell ∧
      ‖iteratedFDeriv ℝ 3 (payload n ell h A ν (ell*h) hp T ∘ P ∘ compress R) u‖≤C*(A+1)*ell/h := by
  obtain ⟨Cp,hCp,hpjet⟩ := payload_source_jets
  obtain ⟨Cg,hCg,hpfirst⟩ := payload_first_uniform
  let C := 135*Cp+72*Cg+360
  have hC : 0≤C := by unfold C; positivity
  refine ⟨C,hC,fun E _ _ n A ν ell h hp T R hA hν hell hh hhp hT hνell hhp' hT' hpR hwidth P hP u => ?_⟩
  let G := Cg*(ell*h)*Real.sqrt ((n:ℝ)+1)+A*(3*ν*hp+ell*h)+A*(ell*h)
  let M₂ := Cp*(A+1)*ell
  let M₃ := Cp*(A+1)*ell/h
  have hG : 0≤G := by unfold G; positivity
  have hM₂ : 0≤M₂ := by unfold M₂; positivity
  have hM₃ : 0≤M₃ := by unfold M₃; positivity
  have hR : 0<R := hhp.trans_le hpR
  have hhr : h≤R := hhp'.trans hpR
  have hfirst : ∀ z,‖iteratedFDeriv ℝ 1 (payload n ell h A ν (ell*h) hp T) z‖≤G :=
    hpfirst n ell h A ν (ell*h) hp T hell.le hA hν (by positivity) hh hhp
  have hsecond : ∀ z,‖iteratedFDeriv ℝ 2 (payload n ell h A ν (ell*h) hp T) z‖≤M₂ := fun z =>
    (hpjet n A ν ell h hp T hA hν hell hh hhp hT hνell hhp' hT' z).1
  have hthird : ∀ z,‖iteratedFDeriv ℝ 3 (payload n ell h A ν (ell*h) hp T) z‖≤M₃ := fun z =>
    (hpjet n A ν ell h hp T hA hν hell hh hhp hT hνell hhp' hT' z).2
  have hb := carried_split_jets _ (payload_contDiff n 3 ell h A ν (ell*h) hp T)
    P hP G M₂ M₃ R hG hM₂ hM₃ hR hfirst hsecond hthird u
  have hGR : G≤(Cg+5*A)*ell*R :=
    payload_norm_budget_le_radius hCg hA hν hell.le hh hhp' hνell hpR hwidth
  have hGradR : G/R≤(Cg+5*A)*ell := (div_le_iff₀ hR).mpr hGR
  have hGradR₂ : G/R^2≤(Cg+5*A)*ell/h := by
    calc
      _=(G/R)/R := by ring
      _≤((Cg+5*A)*ell)/R := div_le_div_of_nonneg_right hGradR hR.le
      _≤_ := div_le_div_of_nonneg_left (by positivity) hh hhr
  have hHessR : M₂/R≤M₂/h := div_le_div_of_nonneg_left hM₂ hh hhr
  have hc₁ : 3*(Cg+5*A)≤C*(A+1) := by
    unfold C
    nlinarith only [hCp,hCg,hA,mul_nonneg hCp hA,mul_nonneg hCg hA]
  have hc₂ : 9*Cp*(A+1)+12*(Cg+5*A)≤C*(A+1) := by
    unfold C
    nlinarith only [hCp,hCg,hA,mul_nonneg hCp hA,mul_nonneg hCg hA]
  have hc₃ : 135*Cp*(A+1)+72*(Cg+5*A)≤C*(A+1) := by
    unfold C
    nlinarith only [hCg,hA,mul_nonneg hCg hA]
  refine ⟨hb.1.trans ?_,hb.2.1.trans ?_,hb.2.2.trans ?_⟩
  · have hc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₁ hell.le) hR.le
    nlinarith only [hGR,hc]
  · have hc := mul_le_mul_of_nonneg_right hc₂ hell.le
    calc
      _=9*M₂+12*(G/R) := by ring
      _≤9*M₂+12*((Cg+5*A)*ell) := by linarith only [hGradR]
      _≤_ := by dsimp [M₂]; nlinarith only [hc]
  · have hc := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc₃ hell.le) hh.le
    calc
      _=27*M₃+108*(M₂/R)+72*(G/R^2) := by ring
      _≤27*M₃+108*(M₂/h)+72*((Cg+5*A)*ell/h) := by linarith only [hGradR₂,hHessR]
      _=(135*Cp*(A+1)+72*(Cg+5*A))*ell/h := by dsimp [M₂,M₃]; ring
      _≤_ := hc

end Bilevel.ChiSplitChain
