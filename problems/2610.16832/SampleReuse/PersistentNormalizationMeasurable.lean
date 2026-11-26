import SampleReuse.PersistentHandleNormalization

open SecondOrder MeasureTheory
namespace SampleReuse
noncomputable section

theorem normalizePersistentAlgorithm_measurable {Ξ Q H Y O S : Type}
    [MeasurableSpace Ξ] [MeasurableSpace Q] [MeasurableSpace H]
    [MeasurableSpace Y] [MeasurableSpace O] [MeasurableSpace S]
    [Countable H] [MeasurableSingletonClass H]
    [MeasurableSpace (List H)] [MeasurableSingletonClass (List H)]
    (P : Ξ → OracleAlgorithm (Q × H) Y O S) (hP : MeasurableOracleAlgorithmFamily P) (N : ℕ) :
    MeasurableOracleAlgorithmFamily (fun ξ => normalizePersistentAlgorithm N (P ξ)) := by
  refine ⟨⟨hP.initial.prodMk measurable_const,?_,?_⟩,?_⟩
  · intro n
    have hq : Measurable (fun w : Ξ × (S × List H) => (P w.1).query n w.2.1) :=
      (hP.query n).comp (measurable_fst.prodMk measurable_snd.fst)
    exact hq.fst.prodMk ((measurable_of_countable (fun w : List H × H => handleSlot N w.1 w.2)).comp
      (measurable_snd.snd.prodMk hq.snd))
  · intro n
    have hu : Measurable (fun w : Ξ × ((S × List H) × Y) => (P w.1).update n w.2.1.1 w.2.2) :=
      (hP.update n).comp (measurable_fst.prodMk (measurable_snd.fst.fst.prodMk measurable_snd.snd))
    have hq : Measurable (fun w : Ξ × ((S × List H) × Y) => (P w.1).query n w.2.1.1) :=
      (hP.query n).comp (measurable_fst.prodMk measurable_snd.fst.fst)
    exact hu.prodMk ((measurable_of_countable (fun w : List H × H => w.1 ++ [w.2])).comp
      (measurable_snd.fst.snd.prodMk hq.snd))
  · intro n
    exact (hP.output n).comp (measurable_fst.prodMk measurable_snd.fst)

end
end SampleReuse
