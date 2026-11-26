import SampleReuse.CurvatureFirstTrajectory
import SampleReuse.CurvatureFirstMeasurable
import SampleReuse.OracleBatchDiagonalMeasurable

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

theorem checkpointPacket_measurable {Ω S E : Type} [MeasurableSpace Ω] [MeasurableSpace S]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {H d B : ℕ} (hB : 0 < B) (scale σ L : ℝ)
    (sample : Ω → Point d → E) (hsample : Measurable (fun w : Ω × Point d => sample w.1 w.2))
    (reserve : ℕ → Fin B → Fin H) (k : S → ℕ) (hk : Measurable k)
    (cache : S → TreeCache d E) (hc : Measurable cache) (x : S → Point d) (hx : Measurable x)
    (tape : S → SampleTape H Ω) (ht : Measurable tape) :
    Measurable (fun w => checkpointPacket hB scale σ L sample reserve (k w) (cache w) (x w) (tape w)) := by
  apply measurable_natChoice (fun j w => checkpointPacket hB scale σ L sample reserve j (cache w) (x w) (tape w)) _ k hk
  intro j
  by_cases hj : j = 0
  · simp only [checkpointPacket,if_pos hj,batchMeanTape]
    exact (Finset.measurable_sum Finset.univ (fun i _ =>
      hsample.comp (((measurable_pi_apply (reserve j i)).comp ht).prodMk hx))).const_smul ((B:ℝ)⁻¹)
  · have hp : Measurable (fun w => (cache w (ancestorParent j)).1) :=
      ((measurable_pi_apply _).comp hc).fst
    have hA : Measurable (fun w : S × Ω => sample w.2 (x w.1) - sample w.2 (cache w.1 (ancestorParent j)).1) :=
      (hsample.comp (measurable_snd.prodMk (hx.comp measurable_fst))).sub
        (hsample.comp (measurable_snd.prodMk (hp.comp measurable_fst)))
    have hn : Measurable (fun w => checkpointBatchSize (B := B) scale σ L j (cache w) (x w)) := by
      simpa only [checkpointBatchSize,if_neg hj] using chordBatchSize_measurable scale σ L x _ hx hp
    have hb : Measurable (fun w => fun i => tape w (reserve j i)) :=
      measurable_pi_lambda _ (fun i => (measurable_pi_apply _).comp ht)
    simpa only [checkpointPacket,if_neg hj,adaptiveBatchMean,batchMeanTape] using
      adaptiveBatchMean_diagonal_measurable hB
        (fun w z => sample z (x w) - sample z (cache w (ancestorParent j)).1) hA
        (fun w => checkpointBatchSize (B := B) scale σ L j (cache w) (x w)) hn
        (fun w i => tape w (reserve j i)) hb

theorem curvatureMacroAdvance_inspection_measurable {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]
    {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ)
    (hFg : Measurable (fun w : Ω × Point d => gradient (F w.1) w.2))
    (hFH : Measurable (fun w : Ω × Point d => hessian (F w.1) w.2))
    (t : ℕ) (s : S → OptimizerCache d) (hs : Measurable s) (b : S → Bool) (hb : Measurable b)
    (tape : S → SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (ht : Measurable tape) :
    Measurable (fun w => curvatureMacroAdvance P ε γ (b w)
      (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F (tape w) t (s w))) := by
  let pH w := checkpointPacket hBH scaleH P.hessianNoise P.hessianLip (fun z => hessian (F z))
    (hessianReserve T Bg BH) t (s w).2.2.2 (s w).1 (tape w)
  let pG w := checkpointPacket hBg scaleG P.gradientNoise P.gradientLip (fun z => gradient (F z))
    (gradientReserve T Bg BH) (s w).2.1 (s w).2.2.1 (s w).1 (tape w)
  have hpH : Measurable pH := checkpointPacket_measurable hBH scaleH P.hessianNoise P.hessianLip _ hFH
    (hessianReserve T Bg BH) _ measurable_const _ hs.snd.snd.snd _ hs.fst tape ht
  have hpG : Measurable pG := checkpointPacket_measurable hBg scaleG P.gradientNoise P.gradientLip _ hFg
    (gradientReserve T Bg BH) _ hs.snd.fst _ hs.snd.snd.fst _ hs.fst tape ht
  let H w := checkpointValue t (s w).2.2.2 (pH w)
  let g w := checkpointValue (s w).2.1 (s w).2.2.1 (pG w)
  have hH : Measurable H := checkpointValue_measurable _ measurable_const _ hs.snd.snd.snd _ hpH
  have hg : Measurable g := checkpointValue_measurable _ hs.snd.fst _ hs.snd.snd.fst _ hpG
  have hcH := installCheckpoint_measurable (fun _ : S => t) measurable_const _ hs.snd.snd.snd _ hs.fst pH hpH
  have hcG := installCheckpoint_measurable (fun w => (s w).2.1) hs.snd.fst _ hs.snd.snd.fst _ hs.fst pG hpG
  let reply w := sourceCurvatureSelector (3*γ/4) (H w)
  have hr : Measurable reply := (sourceCurvatureSelector_measurable _).comp hH
  have hcurv := (curvatureNext_measurable (d := d) (γ/P.hessianLip)).comp
    (hs.fst.prodMk ((curvatureVector_measurable.comp hr).prodMk hb))
  have hmove := (gradientMove_measurable (d := d) P ε).comp (hs.fst.prodMk hg)
  have hsmall : MeasurableSet {w | ‖g w‖ ≤ 3*ε/4} := measurableSet_le hg.norm measurable_const
  have hgradpoint : Measurable (fun w => if ‖g w‖ ≤ 3*ε/4 then (s w).1 else gradientMove P ε (s w).1 (g w)) :=
    Measurable.ite hsmall hs.fst hmove
  have hcurvstate := hcurv.prodMk (hs.snd.fst.prodMk (hs.snd.snd.fst.prodMk hcH))
  have hgradstate := hgradpoint.prodMk ((hs.snd.fst.add_const 1).prodMk (hcG.prodMk hcH))
  have hcond : MeasurableSet {w | curvatureTag (reply w) = true} :=
    (curvatureTag_measurable.comp hr) (measurableSet_singleton true)
  have hfinal := @Measurable.ite S (OptimizerCache d) _ _ _ _
    (fun w => curvatureTag (reply w) = true) (fun _ => inferInstance) hcond hcurvstate hgradstate
  convert hfinal using 1
  funext w
  simp only [curvatureMacroAdvance,curvatureFirstInspect,pH,pG,H,g,reply,inspectionNextPoint]
  split_ifs <;> rfl

theorem curvatureMacroRun_measurable {Ω : Type} [MeasurableSpace Ω]
    {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ)
    (hFg : Measurable (fun w : Ω × Point d => gradient (F w.1) w.2))
    (hFH : Measurable (fun w : Ω × Point d => hessian (F w.1) w.2))
    (x₀ : Point d) (t : ℕ) :
    Measurable (fun w : SampleTape ((T+1)*Bg+(T+1)*BH) Ω × (ℕ → Bool) =>
      curvatureMacroRun hBg hBH P ε γ scaleG scaleH F w.1 w.2 x₀ t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact curvatureMacroAdvance_inspection_measurable hBg hBH P ε γ scaleG scaleH F hFg hFH
      t _ ih _ ((measurable_pi_apply t).comp measurable_snd) _ measurable_fst

end
end SampleReuse
