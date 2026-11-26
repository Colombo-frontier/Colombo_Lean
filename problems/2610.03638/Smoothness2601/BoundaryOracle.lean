import Smoothness2601.BoundaryInstance
import Smoothness2601.FiniteSampleOracle

/-! A globally valid two-point f-oracle and exact g-gradients for the boundary
hard population. The noise amplitude is independent of the frame dimension. -/
noncomputable section
open Bilevel.PrimitiveGeometry
namespace Smoothness2601.BoundaryInstance
open SineGeometry ExtensiveChain HardProfiles
variable {b : Budgets} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) {s : ℝ} (hs : 0 < s)

def signalField (_hs : 0 < s) (x : E) : Joint E ℝ :=
  pack (s • (HardProfiles.profiles U).gB ((s/spatialConstant b)⁻¹ • x)) 0

theorem signalField_continuous : Continuous (signalField (b := b) U hs) := by
  have hg : Continuous (HardProfiles.profiles U).gB :=
    (LipschitzWith.of_dist_le_mul (K := ⟨frontierSmoothness,frontierSmoothness_nonneg⟩)
      (fun x z => by simpa only [dist_eq_norm,NNReal.coe_mk] using
        (HardProfiles.profiles U).lip_gB x z)).continuous
  unfold signalField
  exact (packLinear (X := E) (Y := ℝ)).continuous.comp
    ((continuous_const.smul (hg.comp (continuous_const.smul continuous_id))).prodMk continuous_const)

theorem signalField_bound (x : E) : ‖signalField (b := b) U hs x‖ ≤ s*Cutoffs.frontierGradientBound := by
  rw [signalField,norm_pack_zero,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
  exact mul_le_mul_of_nonneg_left ((HardProfiles.profiles U).bound_gB _) hs.le

theorem gradient_barrier (hμL : b.μ ≤ b.L₁) (x : E)
    (hhidden : ∃ j : Fin (n+1),
      |frameProjection U (Bilevel.RadialWrapper.compress (chainRadius radiusConstant n)
        ((s/spatialConstant b)⁻¹ • x)) j| < 1) :
    s/2 ≤ ‖gradient (population U hs hμL).objective x‖ := by
  rw [objective_gradient,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
  exact (mul_le_mul_of_nonneg_left (profiles_barrier U _ hhidden) hs.le).trans_eq' (by ring)

theorem objective_formula (hμL : b.μ ≤ b.L₁) (x : E) :
    (population U hs hμL).objective x = (s^2/spatialConstant b)*
      ((HardProfiles.profiles U).A ((s/spatialConstant b)⁻¹ • x)+
        (HardProfiles.profiles U).B ((s/spatialConstant b)⁻¹ • x)) := by
  unfold population
  rw [(profiles U hs).population_objective (calibration U hs hμL)]
  simp only [show (calibration U hs hμL).c = 0 from rfl,zero_mul,add_zero]
  rfl

theorem initialized (hμL : b.μ ≤ b.L₁)
    (hgap : (s^2/spatialConstant b)*gapConstant*(n+1) ≤ b.Δ) :
    (population U hs hμL).Initialized 0 0 := by
  let P := population U hs hμL
  have hg : ∀ x, P.objective 0-P.objective x ≤ b.Δ := by
    intro x
    dsimp [P]
    rw [objective_formula,objective_formula,smul_zero,← mul_sub]
    have ht := mul_le_mul_of_nonneg_left (profiles_gap U ((s/spatialConstant b)⁻¹ • x))
      (by have := spatialConstant_pos b; positivity : 0 ≤ s^2/spatialConstant b)
    exact ht.trans (by convert hgap using 1; ring)
  have hlo : ∀ y ∈ Set.range P.objective, P.objective 0-b.Δ ≤ y := by
    rintro y ⟨x,rfl⟩
    linarith [hg x]
  refine ⟨⟨P.objective 0-b.Δ,hlo⟩,?_,?_⟩
  · have hi := le_csInf (show (Set.range P.objective).Nonempty from ⟨P.objective 0,0,rfl⟩) hlo
    linarith
  · rw [zero_inner,sub_self,norm_zero]
    exact b.R₀_nonneg

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def signal (q : Adaptive.Query E ℝ) : Joint E ℝ := signalField (b := b) U hs q.2.1

omit [SecondCountableTopology E] in
theorem signal_measurable : Measurable (signal (b := b) U hs) :=
  (signalField_continuous U hs).measurable.comp (measurable_fst.comp measurable_snd)

def oracle (hμL : b.μ ≤ b.L₁) (hsmall : s ≤ b.σ/(Cutoffs.frontierGradientBound+1)) :
    Adaptive.Oracle (population U hs hμL) Unit :=
  FreshUpperBernoulli.oracle (population U hs hμL) (signal (b := b) U hs) (signal_measurable (b := b) U hs)
    (B := s*(Cutoffs.frontierGradientBound+1))
    (mul_pos hs (by linarith [frontierGradientBound_nonneg]))
    ((le_div_iff₀ (by linarith [frontierGradientBound_nonneg])).mp hsmall)
    (fun q => (signalField_bound (b := b) U hs q.2.1).trans (by nlinarith))

end Smoothness2601.BoundaryInstance
