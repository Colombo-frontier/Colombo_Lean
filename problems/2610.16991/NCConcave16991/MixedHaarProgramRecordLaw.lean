import NCConcave16991.MixedHaarProgramLaw
import NCConcave16991.OracleProgramRecord

/-! # The full generated cache is almost surely consistent with the final operator -/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

variable {A R X Ω S W Z O : Type} [MeasurableSpace A] [MeasurableSpace R]
  [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace W]
  [MeasurableSpace Z] [MeasurableSpace O] {T : ℕ}
  (P : OracleProgram.Fixed A R X Ω T) (reveal : S → A → W → S × R) (complete : S → Z → O)
  (oracle : O → A → R) (τ : Measure W) (ν : Measure Z)
  [IsProbabilityMeasure τ] [IsProbabilityMeasure ν]
  (hr : Measurable (fun p : S × (A × W) ↦ reveal p.1 p.2.1 p.2.2))
  (hc : Measurable (fun p : S × Z ↦ complete p.1 p.2))
  (ho : Measurable (Function.uncurry oracle))
  (hlocal : ∀ s q, (τ.prod ν).map (fun p : W × Z ↦
      ((reveal s q p.1).2,complete (reveal s q p.1).1 p.2)) =
    ν.map (fun z ↦ (oracle (complete s z) q,complete s z)))

include hr hc ho hlocal in
theorem programGaussianEval_cacheConsistent_ae [MeasurableEq R] (seed : Ω) (s : S) :
    ∀ᵐ p ∂revealTapeLaw τ ν T,
      let out := programGaussianEval (OracleProgram.recordReplies P) reveal complete seed s p
      OracleProgram.CacheConsistent P (oracle out.2) seed out.1.2 := by
  let PP := OracleProgram.recordReplies P
  let E : Set ((X × (Fin T → R)) × O) :=
    {r | OracleProgram.CacheConsistent P (oracle r.2) seed r.1.2}
  have hE : MeasurableSet E := (OracleProgram.cacheConsistent_measurableSet P oracle ho).preimage
    (measurable_snd.prodMk (measurable_const.prodMk (measurable_snd.comp measurable_fst)))
  have hl : Measurable (programGaussianEval PP reveal complete seed s) :=
    programGaussianEvalFrom_fixed_measurable PP reveal complete hr hc seed T 0 (by omega) s Fin.elim0
  have hcomp : Measurable (complete s) := hc.comp (measurable_const.prodMk measurable_id)
  have heval : Measurable (fun z ↦ OracleProgram.eval PP (oracle (complete s z)) seed) :=
    (OracleProgram.eval_joint_measurable PP oracle ho).comp (hcomp.prodMk measurable_const)
  have hright : Measurable (fun z ↦ (OracleProgram.eval PP (oracle (complete s z)) seed,complete s z)) :=
    heval.prodMk hcomp
  have hg : ∀ᵐ r ∂ν.map (fun z ↦ (OracleProgram.eval PP (oracle (complete s z)) seed,complete s z)), r ∈ E :=
    (ae_map_iff hright.aemeasurable hE).mpr (Filter.Eventually.of_forall (fun z ↦
      OracleProgram.eval_recordReplies_consistent P (oracle (complete s z)) seed))
  rw [← programGaussianEval_joint_law PP reveal complete oracle τ ν hr hc ho hlocal seed s] at hg
  exact (ae_map_iff hl.aemeasurable hE).mp hg

theorem programGaussianEvalFrom_record_finish (seed : Ω) (k t : ℕ) (ht : t + k = T)
    (s : S) (replies : Fin t → R) (p : RevealTape W Z k) :
    (programGaussianEvalFrom (OracleProgram.recordReplies P) reveal complete seed k t ht s replies p).1.1 =
      P.finish seed (programGaussianEvalFrom (OracleProgram.recordReplies P) reveal complete seed k t ht s replies p).1.2 := by
  induction k generalizing t s with
  | zero => rfl
  | succ k ih =>
      exact ih (t + 1) (by omega)
        (reveal s (P.ask ⟨t,by omega⟩ seed replies) p.1).1
        (Fin.snoc replies (reveal s (P.ask ⟨t,by omega⟩ seed replies) p.1).2) p.2

include hr hc ho hlocal in
theorem programGaussianEval_eq_static_ae [MeasurableEq R] (seed : Ω) (s : S) :
    ∀ᵐ p ∂revealTapeLaw τ ν T,
      let out := programGaussianEval (OracleProgram.recordReplies P) reveal complete seed s p
      out.1.1 = OracleProgram.eval P (oracle out.2) seed := by
  filter_upwards [programGaussianEval_cacheConsistent_ae P reveal complete oracle τ ν hr hc ho hlocal seed s] with p hp
  change (programGaussianEval (OracleProgram.recordReplies P) reveal complete seed s p).1.1 =
    OracleProgram.eval P (oracle (programGaussianEval (OracleProgram.recordReplies P) reveal complete seed s p).2) seed
  rw [show (programGaussianEval (OracleProgram.recordReplies P) reveal complete seed s p).1.1 =
      P.finish seed (programGaussianEval (OracleProgram.recordReplies P) reveal complete seed s p).1.2 from
    programGaussianEvalFrom_record_finish P reveal complete seed T 0 (by omega) s Fin.elim0 p]
  exact OracleProgram.CacheConsistent.finish_eq_eval P _ seed _ hp

end NCConcave16991.MixedHaar
