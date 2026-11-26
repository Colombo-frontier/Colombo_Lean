import NCConcave16991.MixedHaarProgramSampler
import NCConcave16991.MixedHaarProgramMeasurable

/-! # Joint measurability of the actual Gaussian fixed-program evaluator -/

noncomputable section

open MeasureTheory

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {A R X Ω S W Z O : Type} [MeasurableSpace A] [MeasurableSpace R]
  [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace W]
  [MeasurableSpace Z] [MeasurableSpace O] {T : ℕ}
  (P : OracleProgram.Fixed A R X Ω T) (reveal : S → A → W → S × R) (complete : S → Z → O)
  (hr : Measurable (fun p : S × (A × W) ↦ reveal p.1 p.2.1 p.2.2))
  (hc : Measurable (fun p : S × Z ↦ complete p.1 p.2))

include hr in
theorem programNextInput_measurable (k t : ℕ) (ht : t + (k + 1) = T) :
    Measurable (programNextInput (Z := Z) P reveal k t ht) := by
  let C := ProgramSampleInput Ω S R W Z (k + 1) t
  have hq : Measurable (fun p : C ↦ P.ask ⟨t,by omega⟩ p.1 p.2.2.1) :=
    (P.ask_measurable ⟨t,by omega⟩).comp
      (measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have hsr : Measurable (fun p : C ↦ reveal p.2.1 (P.ask ⟨t,by omega⟩ p.1 p.2.2.1) p.2.2.2.1) :=
    hr.comp ((measurable_fst.comp measurable_snd).prodMk
      (hq.prodMk (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))))
  have hnew : Measurable (fun p : C ↦ Fin.snoc (α := fun _ : Fin (t + 1) ↦ R) p.2.2.1
      (reveal p.2.1 (P.ask ⟨t,by omega⟩ p.1 p.2.2.1) p.2.2.2.1).2) :=
    (OracleProgram.fin_snoc_measurable t).comp
      ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk (measurable_snd.comp hsr))
  exact measurable_fst.prodMk ((measurable_fst.comp hsr).prodMk
    (hnew.prodMk (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))))

include hr hc in
theorem programGaussianEvalFrom_joint_measurable (k t : ℕ) (ht : t + k = T) :
    Measurable (fun p : ProgramSampleInput Ω S R W Z k t ↦
      programGaussianEvalFrom P reveal complete p.1 k t ht p.2.1 p.2.2.1 p.2.2.2) := by
  induction k generalizing t with
  | zero =>
      have hf : Measurable (fun p : ProgramSampleInput Ω S R W Z 0 t ↦
          P.finish p.1 (fun i : Fin T ↦ p.2.2.1 (Fin.cast ht.symm i))) :=
        P.finish_measurable.comp (measurable_fst.prodMk
          ((OracleProgram.measurable_reindex (Fin.cast ht.symm)).comp
            (measurable_fst.comp (measurable_snd.comp measurable_snd))))
      exact hf.prodMk (hc.comp ((measurable_fst.comp measurable_snd).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  | succ k ih =>
      exact (ih (t + 1) (by omega)).comp (programNextInput_measurable P reveal hr k t ht)

include hr hc in
theorem programGaussianEvalFrom_fixed_measurable (seed : Ω) (k t : ℕ) (ht : t + k = T)
    (s : S) (replies : Fin t → R) :
    Measurable (programGaussianEvalFrom P reveal complete seed k t ht s replies) :=
  (programGaussianEvalFrom_joint_measurable P reveal complete hr hc k t ht).comp
    (measurable_const.prodMk (measurable_const.prodMk (measurable_const.prodMk measurable_id)))

include hr in
theorem programGaussianGoodFrom_joint_measurable (G : S → A → W → Prop)
    (hG : Measurable (fun p : S × (A × W) ↦ G p.1 p.2.1 p.2.2))
    (k t : ℕ) (ht : t + k = T) :
    Measurable (fun p : ProgramSampleInput Ω S R W Z k t ↦
      programGaussianGoodFrom P reveal G p.1 k t ht p.2.1 p.2.2.1 p.2.2.2) := by
  induction k generalizing t with
  | zero => exact measurable_const
  | succ k ih =>
      have hq : Measurable (fun p : ProgramSampleInput Ω S R W Z (k + 1) t ↦
          P.ask ⟨t,by omega⟩ p.1 p.2.2.1) :=
        (P.ask_measurable ⟨t,by omega⟩).comp
          (measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd)))
      exact (hG.comp ((measurable_fst.comp measurable_snd).prodMk
        (hq.prodMk (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))))).and
        ((ih (t + 1) (by omega)).comp (programNextInput_measurable P reveal hr k t ht))

end NCConcave16991.MixedHaar
