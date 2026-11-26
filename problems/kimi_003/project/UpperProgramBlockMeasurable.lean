import UpperProgramBlocks

open MeasureTheory
namespace Task006.Full

set_option maxHeartbeats 1000000 in
theorem upperBlockIterate_measurable {d T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : UpperProgramParameters) {F : Space d → Ω → ℝ} (hF : Measurable (Function.uncurry F)) (t : ℕ) :
    Measurable (fun blocks : Fin T → UpperSampleBlock d Ω => upperBlockIterate P F blocks t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    by_cases ht : t < T
    · have hstep : (fun blocks : Fin T → UpperSampleBlock d Ω => upperBlockIterate P F blocks (t + 1)) =
          fun blocks => ballProj (P.R - (P.ρ + P.δ)) P.inner_nonneg
            (upperBlockIterate P F blocks t - P.η • upperBlockDirection P F
              (upperBlockIterate P F blocks t) (blocks ⟨t, ht⟩)) := by
        funext blocks
        rw [upperBlockIterate, dif_pos ht]
      rw [hstep]
      have hpair : Measurable (fun blocks : Fin T → UpperSampleBlock d Ω =>
          (upperBlockIterate P F blocks t, blocks ⟨t, ht⟩)) :=
        ih.prodMk (measurable_pi_apply (⟨t, ht⟩ : Fin T))
      have hdir : Measurable (fun blocks : Fin T → UpperSampleBlock d Ω =>
          upperBlockDirection P F (upperBlockIterate P F blocks t) (blocks ⟨t, ht⟩)) := by
        have hbase : Measurable (fun xb : Space d × UpperSampleBlock d Ω =>
            upperBlockDirection P F xb.1 xb.2) :=
          upperBlockDirection_measurable (d := d) (Ω := Ω) (F := F) P hF
        simpa only [Function.comp_def] using hbase.comp hpair
      exact (ballProj_lipschitz (E := Space d) P.inner_nonneg).continuous.measurable.comp
        (ih.sub (hdir.const_smul P.η))
    · simpa only [upperBlockIterate, dif_neg ht] using ih

#print axioms upperBlockIterate_measurable
end Task006.Full
