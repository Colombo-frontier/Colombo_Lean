import NCConcave16991.GlobalHardGateJets
import NCConcave16991.GlobalHardVectorJets

/-! # Actual quantitative calculus of the entrance and public vector exit -/

namespace NCConcave16991.GlobalHard

noncomputable section

open LocalizationScalar LocalizationRadial
open scoped InnerProductSpace

variable {H A B E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem activationLoad_score_jet (v : A) (hv : ‖v‖ = 1) (w : B) (hw : ‖w‖ = 1)
    (P : H →L[ℝ] A) (hP : ‖P‖ ≤ 1) (Q : H →L[ℝ] B) (hQ : ‖Q‖ ≤ 1) :
    JetBound (fun x ↦ activationLoad (stateScore v (P x)) (stateScore w (Q x))) 1 20 640 := by
  convert ((gate_score_jet v hv).comp_contraction P hP).mul
    ((one_sub_gate_score_jet w hw).comp_contraction Q hQ) using 1 <;> norm_num [activationLoad]

theorem initial_activationLoad_score_jet (w : B) (hw : ‖w‖ = 1)
    (Q : H →L[ℝ] B) (hQ : ‖Q‖ ≤ 1) :
    JetBound (fun x ↦ activationLoad 1 (stateScore w (Q x))) 1 20 640 := by
  have hh := ((one_sub_gate_score_jet w hw).comp_contraction Q hQ).weaken
    1 20 640 le_rfl (by norm_num) (by norm_num)
  simpa only [activationLoad, gate_one (by norm_num : (1 : ℝ) ≤ 1), one_mul] using hh

theorem capped_source_jet (u : E) (hu : ‖u‖ = 1) (P : H →L[ℝ] E) (hP : ‖P‖ ≤ 1) :
    JetBound (fun x ↦ ⟪u, radialCap 21 (P x)⟫_ℝ) 42 1 1 := by
  convert (VectorJetBound.const (H := H) u).inner
    (cap_contraction_jet 21 1 (by norm_num) (by norm_num) P hP) using 1 <;> norm_num [hu]

/-- The source entrance has the actual bound 107684, below the source's
round number 200000, even when the coordinate contractions overlap. -/
theorem entrance_score_jet (v : A) (hv : ‖v‖ = 1) (w : B) (hw : ‖w‖ = 1)
    (u : E) (hu : ‖u‖ = 1) (P : H →L[ℝ] A) (hP : ‖P‖ ≤ 1)
    (Q : H →L[ℝ] B) (hQ : ‖Q‖ ≤ 1) (R : H →L[ℝ] E) (hR : ‖R‖ ≤ 1) :
    JetBound (fun x ↦ entrance u (stateScore v (P x)) (stateScore w (Q x)) (R x))
      168 3364 107684 := by
  have hh := (activationLoad_score_jet v hv w hw P hP Q hQ).mul (capped_source_jet u hu R hR)
  convert hh.const_mul (-4) using 1 <;> norm_num [entrance, mul_assoc]

/-- The exact public vector exit has the actual bound 540186, below 600000.
The score gate and the vector cap share the very same state coordinate. -/
theorem exit_score_jet (v : A) (hv : ‖v‖ = 1) (w : B) (hw : ‖w‖ = 1)
    (P : H →L[ℝ] A) (hP : ‖P‖ ≤ 1) (Q R : H →L[ℝ] B)
    (hQ : ‖Q‖ ≤ 1) (hR : ‖R‖ ≤ 1) :
    JetBound (fun x ↦ exit (stateScore v (P x)) (stateScore w (Q x)) (Q x) (R x))
      840 16862 540186 := by
  have hh := (activationLoad_score_jet v hv w hw P hP Q hQ).mul (capped_inner_jet Q R hQ hR)
  convert hh.const_mul (-1) using 1 <;> norm_num [exit, mul_assoc]

theorem initial_entrance_score_jet (w : B) (hw : ‖w‖ = 1)
    (u : E) (hu : ‖u‖ = 1) (Q : H →L[ℝ] B) (hQ : ‖Q‖ ≤ 1)
    (R : H →L[ℝ] E) (hR : ‖R‖ ≤ 1) :
    JetBound (fun x ↦ entrance u 1 (stateScore w (Q x)) (R x)) 168 3364 107684 := by
  have hh := (initial_activationLoad_score_jet w hw Q hQ).mul (capped_source_jet u hu R hR)
  convert hh.const_mul (-4) using 1 <;> norm_num [entrance, mul_assoc]

theorem initial_exit_score_jet (w : B) (hw : ‖w‖ = 1)
    (Q R : H →L[ℝ] B) (hQ : ‖Q‖ ≤ 1) (hR : ‖R‖ ≤ 1) :
    JetBound (fun x ↦ exit 1 (stateScore w (Q x)) (Q x) (R x)) 840 16862 540186 := by
  have hh := (initial_activationLoad_score_jet w hw Q hQ).mul (capped_inner_jet Q R hQ hR)
  convert hh.const_mul (-1) using 1 <;> norm_num [exit, mul_assoc]

theorem initial_stateCoupling_zero (current : ℝ) : stateCoupling 1 current = 0 := by
  simp [stateCoupling, precedingFactor, gate_one (by norm_num : (1 : ℝ) ≤ 1)]

end

end NCConcave16991.GlobalHard
