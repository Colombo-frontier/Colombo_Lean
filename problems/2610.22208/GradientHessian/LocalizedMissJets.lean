import GradientHessian.Localized
import GradientHessian.JetLocality

/-! A genuine localized support miss removes the actual perturbation and
port on a neighborhood. The noncompact incoming term is kept unless a separate
child gate annihilates it. -/

noncomputable section
namespace GradientHessian.LocalizedMissJets
open Filter JetLocality
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem distance_miss_near (L : F →L[ℝ] E) (c : E) (x : F) {w : ℝ}
    (hmiss : 3*w < ‖L x-c‖) : ∀ᶠ z in 𝓝 x, 3*w < ‖L z-c‖ :=
  ((L.continuous.continuousAt.sub continuousAt_const).norm).preimage_mem_nhds (lt_mem_nhds hmiss)

theorem perturbation_zero_near (L : F →L[ℝ] E) (R : ℝ) (c : E) (x : F) {w : ℝ}
    (hw : 0<w) (hmiss : 3*w < ‖L x-c‖) :
    (fun z => Localized.perturbation R w c (L z)) =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [distance_miss_near L c x hmiss] with z hz
  exact Localized.perturbation_eq_zero_of_three_mul_le_norm hw hz.le

theorem port_zero_near (L : F →L[ℝ] E) (c : E) (x : F) {w : ℝ}
    (hw : 0<w) (hmiss : 3*w < ‖L x-c‖) :
    (fun z => Localized.port w c (L z)) =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [distance_miss_near L c x hmiss] with z hz
  exact Localized.port_eq_zero_of_two_mul_le_norm hw (by linarith)

theorem potential_eq_public_near (L : F →L[ℝ] E) (R : ℝ) (c : E) (x : F) {w : ℝ}
    (hw : 0<w) (hmiss : 3*w < ‖L x-c‖) :
    (fun z => Localized.potential R w c (L z)) =ᶠ[𝓝 x]
      fun z => Localized.publicPotential R (L z) := by
  filter_upwards [perturbation_zero_near L R c x hw hmiss] with z hz
  simp only [Localized.potential, hz, add_zero]

theorem perturbation_richJet_zero (L : F →L[ℝ] E) (R : ℝ) (c : E) (x : F) {w : ℝ}
    (hw : 0<w) (hmiss : 3*w < ‖L x-c‖) :
    richJet (fun z => Localized.perturbation R w c (L z)) x = 0 :=
  (richJet_congr_of_eventuallyEq (perturbation_zero_near L R c x hw hmiss)).trans (richJet_zero x)

theorem port_richJet_zero (L : F →L[ℝ] E) (c : E) (x : F) {w : ℝ}
    (hw : 0<w) (hmiss : 3*w < ‖L x-c‖) :
    richJet (fun z => Localized.port w c (L z)) x = 0 :=
  (richJet_congr_of_eventuallyEq (port_zero_near L c x hw hmiss)).trans (richJet_zero x)

theorem potential_richJet_public (L : F →L[ℝ] E) (R : ℝ) (c : E) (x : F) {w : ℝ}
    (hw : 0<w) (hmiss : 3*w < ‖L x-c‖) :
    richJet (fun z => Localized.potential R w c (L z)) x =
      richJet (fun z => Localized.publicPotential R (L z)) x :=
  richJet_congr_of_eventuallyEq (potential_eq_public_near L R c x hw hmiss)

end GradientHessian.LocalizedMissJets
