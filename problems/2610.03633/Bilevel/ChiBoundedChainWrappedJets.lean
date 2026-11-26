import Bilevel.ChiBoundedChainPayloadJets
import Bilevel.ChiBoundedChainCompositionBounds
import Bilevel.ChiBoundedChainLocalBudgets
import Bilevel.RadialThird

/-! Order-sensitive radial/frame composition for the actual revised payload. -/
noncomputable section
namespace Bilevel.ChiBoundedChain
open RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem frame_coordinates_jets (n : ℕ) (R : ℝ) (hR : 0<R) (U : Space n →ₗᵢ[ℝ] E) (u : E) :
    ‖iteratedFDeriv ℝ 1 (WrappedChain.coordinates n R U) u‖≤1 ∧
    ‖iteratedFDeriv ℝ 2 (WrappedChain.coordinates n R U) u‖≤4/R ∧
    ‖iteratedFDeriv ℝ 3 (WrappedChain.coordinates n R U) u‖≤24/R^2 := by
  refine ⟨(ZeroChainWrappedResidual.coordinates_jet_le n R U u 1 (by norm_num)).trans ?_,
    (ZeroChainWrappedResidual.coordinates_jet_le n R U u 2 (by norm_num)).trans ?_,
    (ZeroChainWrappedResidual.coordinates_jet_le n R U u 3 (by norm_num)).trans ?_⟩
  · rw [Composition.norm_first,(compress_hasFDerivAt R u).fderiv]
    exact compressDerivative_opNorm_le R hR u
  · rw [← norm_iteratedFDeriv_fderiv (n:=1),← norm_iteratedFDeriv_fderiv (n:=0),norm_iteratedFDeriv_zero]
    exact second_derivative_norm R hR u
  · rw [← norm_iteratedFDeriv_fderiv (n:=2),← norm_iteratedFDeriv_fderiv (n:=1),
      ← norm_iteratedFDeriv_fderiv (n:=0),norm_iteratedFDeriv_zero]
    exact third_derivative_norm R hR u

theorem carried_function_jets {n : ℕ} (f : Space n → ℝ) (hf : ContDiff ℝ 3 f)
    (G M₂ M₃ R : ℝ) (hG : 0≤G) (hM₂ : 0≤M₂) (hM₃ : 0≤M₃) (hR : 0<R)
    (hfirst : ∀ z,‖gradient f z‖≤G) (hsecond : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤M₂)
    (hthird : ∀ z,‖iteratedFDeriv ℝ 3 f z‖≤M₃) (U : Space n →ₗᵢ[ℝ] E) (u : E) :
    ‖iteratedFDeriv ℝ 2 (f ∘ WrappedChain.coordinates n R U) u‖≤M₂+4*G/R ∧
    ‖iteratedFDeriv ℝ 3 (f ∘ WrappedChain.coordinates n R U) u‖≤M₃+12*M₂/R+24*G/R^2 := by
  have hc := ZeroChainWrappedResidual.coordinates_contDiff n R U
  have hz := frame_coordinates_jets n R hR U u
  have hz₁ := hz.1
  have hz₂ := hz.2.1
  have hz₃ := hz.2.2
  have h₁ : ‖iteratedFDeriv ℝ 1 f (WrappedChain.coordinates n R U u)‖≤G := by
    rw [Composition.norm_first,← GradientJetBounds.gradient_norm_eq]
    exact hfirst _
  have h₂ := hsecond (WrappedChain.coordinates n R U u)
  have h₃ := hthird (WrappedChain.coordinates n R U u)
  have hsecondcomp := Composition.second_comp_bound
    (hc.of_le (by exact_mod_cast (show (2:ℕ)≤3 by omega)))
    (hf.of_le (by exact_mod_cast (show (2:ℕ)≤3 by omega))) u
  have hthirdcomp := Composition.third_comp_bound hc hf u
  constructor
  · apply hsecondcomp.trans
    calc
      _ ≤ M₂*1^2+G*(4/R) := by gcongr
      _ = _ := by ring
  · apply hthirdcomp.trans
    calc
      _ ≤ M₃*1^3+3*M₂*1*(4/R)+G*(24/R^2) := by gcongr
      _ = _ := by ring

theorem payload_norm_budget_le_radius {n : ℕ} {Cg A ν ℓ h hp R : ℝ}
    (hCg : 0≤Cg) (hA : 0≤A) (_hν : 0≤ν) (hℓ : 0≤ℓ) (hh : 0<h)
    (hhp : h≤hp) (hνℓ : ν≤ℓ) (hpR : hp≤R)
    (hwidth : h*Real.sqrt ((n:ℝ)+1)≤R) :
    Cg*(ℓ*h)*Real.sqrt ((n:ℝ)+1)+A*(3*ν*hp+ℓ*h)+A*(ℓ*h)≤(Cg+5*A)*ℓ*R := by
  have hhr := hhp.trans hpR
  have hcp := mul_le_mul_of_nonneg_left hwidth (mul_nonneg hCg hℓ)
  have hνhp : ν*hp≤ℓ*R := (mul_le_mul_of_nonneg_right hνℓ (hh.le.trans hhp)).trans
    (mul_le_mul_of_nonneg_left hpR hℓ)
  have hℓh := mul_le_mul_of_nonneg_left hhr hℓ
  have hrec := mul_le_mul_of_nonneg_left (show 3*ν*hp+ℓ*h≤4*(ℓ*R) by linarith) hA
  have hneg := mul_le_mul_of_nonneg_left hℓh hA
  nlinarith only [hcp,hrec,hneg]

/-- Actual second and third jets of the framed, radially compressed payload.
The radius conditions absorb the full chain gradient without introducing a
length-dependent higher-derivative constant. -/
theorem wrapped_payload_source_jets : ∃ C : ℝ,0≤C ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F],
    ∀ (n : ℕ) (A ν ℓ h hp T R : ℝ),0≤A → 0≤ν → 0<ℓ → 0<h → 0<hp → 0<T →
      ν≤ℓ → h≤hp → h≤T → hp≤R → h*Real.sqrt ((n:ℝ)+1)≤R →
      ∀ (U : Space n →ₗᵢ[ℝ] F) (u : F),
      ‖iteratedFDeriv ℝ 2 ((payload n ℓ h A ν (ℓ*h) hp T) ∘ WrappedChain.coordinates n R U) u‖≤C*(A+1)*ℓ ∧
      ‖iteratedFDeriv ℝ 3 ((payload n ℓ h A ν (ℓ*h) hp T) ∘ WrappedChain.coordinates n R U) u‖≤C*(A+1)*ℓ/h := by
  obtain ⟨Cp,hCp,hpjet⟩ := payload_source_jets
  obtain ⟨Cg,hCg,hchain⟩ := Size.chain_gradient_norm_uniform
  let C := 13*Cp+24*Cg+120
  have hC : 0≤C := by unfold C;positivity
  refine ⟨C,hC,fun F _ _ _ n A ν ℓ h hp T R hA hν hℓ hh hhp hT hνℓ hhp' hT' hpR hwidth U u => ?_⟩
  let G := Cg*(ℓ*h)*Real.sqrt ((n:ℝ)+1)+A*(3*ν*hp+ℓ*h)+A*(ℓ*h)
  let M₂ := Cp*(A+1)*ℓ
  let M₃ := Cp*(A+1)*ℓ/h
  have hG : 0≤G := by unfold G;positivity
  have hM₂ : 0≤M₂ := by unfold M₂;positivity
  have hM₃ : 0≤M₃ := by unfold M₃;positivity
  have hR : 0<R := hhp.trans_le hpR
  have hhr : h≤R := hhp'.trans hpR
  have hfirst : ∀ z,‖gradient (payload n ℓ h A ν (ℓ*h) hp T) z‖≤G := fun z =>
    payload_gradient_norm_le n ℓ h A ν (ℓ*h) hp T _ hA hν (by positivity) hh hhp z
      (hchain n ℓ h hℓ.le hh z)
  have hsecond : ∀ z,‖iteratedFDeriv ℝ 2 (payload n ℓ h A ν (ℓ*h) hp T) z‖≤M₂ := fun z =>
    (hpjet n A ν ℓ h hp T hA hν hℓ hh hhp hT hνℓ hhp' hT' z).1
  have hthird : ∀ z,‖iteratedFDeriv ℝ 3 (payload n ℓ h A ν (ℓ*h) hp T) z‖≤M₃ := fun z =>
    (hpjet n A ν ℓ h hp T hA hν hℓ hh hhp hT hνℓ hhp' hT' z).2
  have hb := carried_function_jets _ (payload_contDiff n ℓ h A ν (ℓ*h) hp T 3)
    G M₂ M₃ R hG hM₂ hM₃ hR hfirst hsecond hthird U u
  have hGradR : G/R≤(Cg+5*A)*ℓ := (div_le_iff₀ hR).mpr
    (payload_norm_budget_le_radius hCg hA hν hℓ.le hh hhp' hνℓ hpR hwidth)
  have hGradR₂ : G/R^2≤(Cg+5*A)*ℓ/h := by
    calc
      _ = (G/R)/R := by ring
      _ ≤ ((Cg+5*A)*ℓ)/R := div_le_div_of_nonneg_right hGradR hR.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hh hhr
  have hHessR : M₂/R≤M₂/h := div_le_div_of_nonneg_left hM₂ hh hhr
  have hc₂ : Cp*(A+1)+4*(Cg+5*A)≤C*(A+1) := by
    unfold C
    nlinarith only [hCp,hCg,hA,mul_nonneg hCp hA,mul_nonneg hCg hA]
  have hc₃ : 13*Cp*(A+1)+24*(Cg+5*A)≤C*(A+1) := by
    unfold C
    nlinarith only [hCg,hA,mul_nonneg hCg hA]
  constructor
  · apply hb.1.trans
    have hc := mul_le_mul_of_nonneg_right hc₂ hℓ.le
    calc
      _ = M₂+4*(G/R) := by ring
      _ ≤ M₂+4*((Cg+5*A)*ℓ) := by linarith only [hGradR]
      _ ≤ _ := by dsimp [M₂];nlinarith only [hc]
  · apply hb.2.trans
    have hc := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc₃ hℓ.le) hh.le
    calc
      _ = M₃+12*(M₂/R)+24*(G/R^2) := by ring
      _ ≤ M₃+12*(M₂/h)+24*((Cg+5*A)*ℓ/h) := by linarith only [hGradR₂,hHessR]
      _ = (13*Cp*(A+1)+24*(Cg+5*A))*ℓ/h := by dsimp [M₂,M₃];ring
      _ ≤ _ := hc

end Bilevel.ChiBoundedChain
