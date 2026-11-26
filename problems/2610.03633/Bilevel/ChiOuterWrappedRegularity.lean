import Bilevel.ChiOuterRegularity
import Bilevel.ChiOuterMacro
import Bilevel.ChiBoundedChainWrappedJets
import Bilevel.ChiRecursiveJointObjective

/-! Actual second derivative bounds for the one-sided macro after radial
compression and its public bowl. Constants are independent of chain length. -/
noncomputable section
namespace Bilevel.ChiOuter.Regularity
open ChiBoundedChain ChiRecursive RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem bowl_gradient (ν R : ℝ) (hR : 0<R) :
    gradient (bowl ν R : E → ℝ)=fun u => ν • compress R u := by
  funext u
  simpa only [compress,smul_smul] using (bowl_hasGradientAt ν R hR u).gradient

theorem bowl_jet_two (ν R : ℝ) (hν : 0≤ν) (hR : 0<R) (u : E) :
    ‖iteratedFDeriv ℝ 2 (bowl ν R) u‖≤ν := by
  rw [← GradientJetBounds.hessian_norm_eq (full_bowl_contDiff ν R 3) u,bowl_gradient ν R hR,
    ((compress_hasFDerivAt R u).const_smul ν).fderiv,norm_smul,Real.norm_eq_abs,abs_of_nonneg hν]
  exact (mul_le_mul_of_nonneg_left (compressDerivative_opNorm_le R hR u) hν).trans_eq (mul_one _)

theorem macro_second_bound (n : ℕ) (ℓ h ν R G H : ℝ) (hν : 0≤ν) (hR : 0<R)
    (hG : 0≤G) (hH : 0≤H)
    (hg : ∀ z : Space n,‖gradient (ChiOuter.chain n ℓ h) z‖≤G)
    (hh : ∀ z : Space n,‖iteratedFDeriv ℝ 2 (ChiOuter.chain n ℓ h) z‖≤H)
    (U : Space n →ₗᵢ[ℝ] E) (u : E) :
    ‖iteratedFDeriv ℝ 2 (macroValue n ℓ h ν R U) u‖≤H+4*G/R+ν := by
  have hc := ZeroChainWrappedResidual.coordinates_contDiff n R U
  have hf := ChiOuter.chain_contDiff n ℓ h 3
  have hz := frame_coordinates_jets n R hR U u
  have hfirst : ‖iteratedFDeriv ℝ 1 (ChiOuter.chain n ℓ h) (WrappedChain.coordinates n R U u)‖≤G := by
    rw [Composition.norm_first,← GradientJetBounds.gradient_norm_eq]
    exact hg _
  have h23 : (2:WithTop ℕ∞)≤3 := by exact_mod_cast (show (2:ℕ)≤3 by omega)
  have hcomp := Composition.second_comp_bound (hc.of_le h23) (hf.of_le h23) u
  have hb : ‖iteratedFDeriv ℝ 2 (ChiOuter.chain n ℓ h ∘ WrappedChain.coordinates n R U) u‖≤H+4*G/R := by
    apply hcomp.trans
    calc
      _ ≤ H*1^2+G*(4/R) := by gcongr; exact hh _; exact hz.1; exact hz.2.1
      _ = _ := by ring
  change ‖iteratedFDeriv ℝ 2
    (fun v => (ChiOuter.chain n ℓ h ∘ WrappedChain.coordinates n R U) v+bowl ν R v) u‖≤_
  rw [iteratedFDeriv_add_apply' (((hf.comp hc).of_le h23).contDiffAt)
    (((full_bowl_contDiff ν R 3).of_le h23).contDiffAt)]
  exact (norm_add_le _ _).trans (add_le_add hb (bowl_jet_two ν R hν hR u))

theorem macro_jet_two_uniform : ∃ Cg Ch : ℝ,0≤Cg ∧ 0≤Ch ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (ℓ h Km : ℝ),0≤ℓ → 0<h → 0<Km →
      ∀ (U : Space n →ₗᵢ[ℝ] F) (u : F),
      ‖iteratedFDeriv ℝ 2 (macroValue n ℓ h (ℓ/24) (Km*h*Real.sqrt ((n:ℝ)+1)) U) u‖≤
        (Ch+4*Cg/Km+1/24)*ℓ := by
  obtain ⟨Cg,hCg,hg⟩ := ChiOuter.chain_gradient_norm_uniform
  obtain ⟨Ch,hCh,hh⟩ := chain_jet_two_uniform
  refine ⟨Cg,Ch,hCg,hCh,fun F _ _ _ n ℓ h Km hℓ hw hKm U u => ?_⟩
  have hs : 0<Real.sqrt ((n:ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
  have hb := macro_second_bound n ℓ h (ℓ/24) (Km*h*Real.sqrt ((n:ℝ)+1))
    (Cg*(ℓ*h)*Real.sqrt ((n:ℝ)+1)) (Ch*ℓ) (by positivity) (by positivity)
    (by positivity) (by positivity) (hg n ℓ h hℓ hw) (hh n ℓ h hℓ hw) U u
  convert hb using 1
  field_simp
  ring

end Bilevel.ChiOuter.Regularity
