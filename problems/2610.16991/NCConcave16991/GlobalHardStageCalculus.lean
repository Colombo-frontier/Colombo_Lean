import NCConcave16991.GlobalHardStage

/-! # Actual C-infinity calculus of the literal outer-stage terms -/

namespace NCConcave16991.GlobalHard

noncomputable section

open LocalizationScalar LocalizationRadial
open scoped InnerProductSpace ContDiff

variable {A B E : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem stateScore_contDiff (v : B) : ContDiff ℝ ∞ (stateScore v) :=
  (innerSL ℝ v).contDiff.comp (radialCap_contDiff (by norm_num : (0 : ℝ) < 10))

theorem statePenalty_contDiff (v : B) : ContDiff ℝ ∞ (statePenalty v) := by
  have hs := stateScore_contDiff v
  have hn : ContDiff ℝ ∞ (fun s : B ↦ ‖s‖ ^ 2) := contDiff_id.norm_sq (𝕜 := ℝ)
  exact ((contDiff_const.mul hn).sub
    (contDiff_const.mul (activationSq_contDiff.comp hs))).add (statePotential_contDiff.comp hs)

theorem precedingFactor_contDiff : ContDiff ℝ ∞ precedingFactor :=
  (contDiff_const.sub stateClamp_contDiff).mul (contDiff_const.sub gate_contDiff)

theorem outerStage_contDiff (u : A) (v : B) (previous : E → ℝ) (s : E → B) (a : E → A) (b : E → B)
    (hp : ContDiff ℝ ∞ previous) (hs : ContDiff ℝ ∞ s) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (fun z ↦ outerStage u v (previous z) (s z) (a z) (b z)) := by
  have ht := (stateScore_contDiff v).comp hs
  have hprev := gate_contDiff.comp hp
  have hcur := gate_contDiff.comp ht
  have hl : ContDiff ℝ ∞ (fun z ↦ activationLoad (previous z) (stateScore v (s z))) :=
    hprev.mul ((contDiff_const (c := (1 : ℝ))).sub hcur)
  have hea := (innerSL ℝ u).contDiff.comp ((radialCap_contDiff (by norm_num : (0 : ℝ) < 21)).comp ha)
  have hstate := (radialCap_contDiff (by norm_num : (0 : ℝ) < 10)).comp hs
  have hconn := (radialCap_contDiff (by norm_num : (0 : ℝ) < 21)).comp hb
  have hex := hstate.inner ℝ hconn
  have hen : ContDiff ℝ ∞ (fun z ↦ entrance u (previous z) (stateScore v (s z)) (a z)) :=
    ((contDiff_const (c := (-4 : ℝ))).mul hl).mul hea
  have hxit := hl.neg.mul hex
  have hcoup : ContDiff ℝ ∞ (fun z ↦ stateCoupling (previous z) (stateScore v (s z))) :=
    ((contDiff_const (c := stateWeight)).mul hcur).mul (precedingFactor_contDiff.comp hp)
  have hpen := (statePenalty_contDiff v).comp hs
  exact ((hen.add hxit).add hcoup).add hpen

end

end NCConcave16991.GlobalHard
