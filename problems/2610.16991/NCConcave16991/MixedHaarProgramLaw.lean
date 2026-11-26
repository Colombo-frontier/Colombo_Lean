import NCConcave16991.MixedHaarProgramSamplerMeasurable

/-! # Exact static-hidden-operator law for arbitrary adaptive fixed programs

Only the actual one-request answer/completion identity is used. The proof
integrates every genuine fresh draw and retains the program's complete output.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 1000000
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

include hr hc ho hlocal

theorem programGaussianEvalFrom_lintegral (seed : Ω) (k t : ℕ) (ht : t + k = T)
    (s : S) (replies : Fin t → R) (F : X × O → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F (programGaussianEvalFrom P reveal complete seed k t ht s replies p) ∂revealTapeLaw τ ν k) =
      ∫⁻ z, F (OracleProgram.evalFrom P (oracle (complete s z)) seed k t ht replies,complete s z) ∂ν := by
  induction k generalizing t s with
  | zero => rfl
  | succ k ih =>
      have hlt : t < T := by omega
      have hnext : t + 1 + k = T := by omega
      let q := P.ask ⟨t,hlt⟩ seed replies
      let F1 : R × O → ℝ≥0∞ := fun r ↦
        F (OracleProgram.evalFrom P (oracle r.2) seed k (t + 1) hnext (Fin.snoc replies r.1),r.2)
      have hpref : Measurable (fun r : R × O ↦ Fin.snoc (α := fun _ : Fin (t + 1) ↦ R) replies r.1) :=
        (OracleProgram.fin_snoc_measurable t).comp (measurable_const.prodMk measurable_fst)
      have htail : Measurable (fun r : R × O ↦
          OracleProgram.evalFrom P (oracle r.2) seed k (t + 1) hnext (Fin.snoc replies r.1)) :=
        (OracleProgram.evalFrom_joint_measurable P oracle ho k (t + 1) hnext).comp
          (measurable_snd.prodMk (measurable_const.prodMk hpref))
      have hF1 : Measurable F1 := hF.comp (htail.prodMk measurable_snd)
      have hrev : Measurable (reveal s q) :=
        hr.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
      have hcomp : Measurable (complete s) := hc.comp (measurable_const.prodMk measurable_id)
      have hleft : Measurable (fun p : W × Z ↦ ((reveal s q p.1).2,complete (reveal s q p.1).1 p.2)) :=
        ((measurable_snd.comp hrev).comp measurable_fst).prodMk
          (hc.comp (((measurable_fst.comp hrev).comp measurable_fst).prodMk measurable_snd))
      have hright : Measurable (fun z ↦ (oracle (complete s z) q,complete s z)) :=
        (ho.comp (hcomp.prodMk measurable_const)).prodMk hcomp
      have hOne := congrArg (fun μ : Measure (R × O) ↦ ∫⁻ r, F1 r ∂μ) (hlocal s q)
      rw [lintegral_map hF1 hleft,lintegral_map hF1 hright] at hOne
      have hinner : Measurable (fun p : W × Z ↦ F1 ((reveal s q p.1).2,complete (reveal s q p.1).1 p.2)) :=
        hF1.comp hleft
      rw [lintegral_prod _ hinner.aemeasurable] at hOne
      have hwhole := programGaussianEvalFrom_fixed_measurable P reveal complete hr hc seed (k + 1) t ht s replies
      calc
        _ = ∫⁻ w, ∫⁻ p, F (programGaussianEvalFrom P reveal complete seed k (t + 1) hnext
              (reveal s q w).1 (Fin.snoc replies (reveal s q w).2) p) ∂revealTapeLaw τ ν k ∂τ :=
          lintegral_prod _ (hF.comp hwhole).aemeasurable
        _ = ∫⁻ w, ∫⁻ z, F (OracleProgram.evalFrom P (oracle (complete (reveal s q w).1 z)) seed
              k (t + 1) hnext (Fin.snoc replies (reveal s q w).2),complete (reveal s q w).1 z) ∂ν ∂τ :=
          lintegral_congr_ae (Filter.Eventually.of_forall (fun w ↦
            ih (t + 1) hnext (reveal s q w).1 (Fin.snoc replies (reveal s q w).2)))
        _ = _ := by simpa only [F1,OracleProgram.evalFrom,q] using hOne

theorem programGaussianEvalFrom_joint_law (seed : Ω) (k t : ℕ) (ht : t + k = T)
    (s : S) (replies : Fin t → R) :
    (revealTapeLaw τ ν k).map (programGaussianEvalFrom P reveal complete seed k t ht s replies) =
      ν.map (fun z ↦ (OracleProgram.evalFrom P (oracle (complete s z)) seed k t ht replies,complete s z)) := by
  apply Measure.ext_of_lintegral
  intro F hF
  have hl := programGaussianEvalFrom_fixed_measurable P reveal complete hr hc seed k t ht s replies
  have hcomp : Measurable (complete s) := hc.comp (measurable_const.prodMk measurable_id)
  have heval : Measurable (fun z ↦ OracleProgram.evalFrom P (oracle (complete s z)) seed k t ht replies) :=
    (OracleProgram.evalFrom_joint_measurable P oracle ho k t ht).comp
      (hcomp.prodMk (measurable_const.prodMk measurable_const))
  rw [lintegral_map hF hl,lintegral_map hF (heval.prodMk hcomp)]
  exact programGaussianEvalFrom_lintegral P reveal complete oracle τ ν hr hc ho hlocal seed k t ht s replies F hF

theorem programGaussianEval_joint_law (seed : Ω) (s : S) :
    (revealTapeLaw τ ν T).map (programGaussianEval P reveal complete seed s) =
      ν.map (fun z ↦ (OracleProgram.eval P (oracle (complete s z)) seed,complete s z)) :=
  programGaussianEvalFrom_joint_law P reveal complete oracle τ ν hr hc ho hlocal seed T 0 (by omega) s Fin.elim0

theorem programGaussianEval_hidden_preserving (seed : Ω) (s : S) :
    MeasurePreserving (fun p ↦ (programGaussianEval P reveal complete seed s p).2)
      (revealTapeLaw τ ν T) (ν.map (complete s)) := by
  have hl : Measurable (programGaussianEval P reveal complete seed s) :=
    programGaussianEvalFrom_fixed_measurable P reveal complete hr hc seed T 0 (by omega) s Fin.elim0
  have hcomp : Measurable (complete s) := hc.comp (measurable_const.prodMk measurable_id)
  have heval : Measurable (fun z ↦ OracleProgram.eval P (oracle (complete s z)) seed) :=
    (OracleProgram.eval_joint_measurable P oracle ho).comp (hcomp.prodMk measurable_const)
  have hh := congrArg (fun μ : Measure (X × O) ↦ μ.map Prod.snd)
    (programGaussianEval_joint_law P reveal complete oracle τ ν hr hc ho hlocal seed s)
  rw [Measure.map_map measurable_snd hl,Measure.map_map measurable_snd (heval.prodMk hcomp)] at hh
  exact ⟨measurable_snd.comp hl,by simpa only [Function.comp_def] using hh⟩

end NCConcave16991.MixedHaar
