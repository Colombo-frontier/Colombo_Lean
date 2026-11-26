import SampleReuse.CurvatureFirstMeasurable

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

instance optimizerOutputMeasurableSpace (d : ℕ) : MeasurableSpace (Option (Point d)) :=
  MeasurableSpace.comap (Equiv.optionEquivSumPUnit.{0,0} (Point d)) inferInstance

theorem optimizerOutput_some_measurable (d : ℕ) : Measurable (some : Point d → Option (Point d)) := by
  intro s hs
  rcases hs with ⟨u, hu, rfl⟩
  simpa only [Set.preimage_preimage, Function.comp_def, Equiv.optionEquivSumPUnit_some] using measurable_inl hu

theorem curvatureFirstProgram_measurableFamily {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (q₀ : PersistentQuery ((T+1)*Bg+(T+1)*BH) d) (m t : ℕ) :
    OracleProgram.MeasurableFamily q₀ none
      (fun w : (ℕ → Bool) × OptimizerCache d =>
        curvatureFirstProgram hBg hBH P ε γ scaleG scaleH w.1 m t w.2) := by
  classical
  induction m generalizing t with
  | zero => exact OracleProgram.measurableFamily_done q₀ none (fun _ => none) measurable_const
  | succ m ih =>
    let W := (ℕ → Bool) × OptimizerCache d
    let WH := W × (Point d →L[ℝ] Point d)
    let WG := WH × Point d
    let valH (w : WH) := checkpointValue t w.1.2.2.2.2 w.2
    let cacheH (w : WH) := installCheckpoint t w.1.2.2.2.2 w.1.2.1 w.2
    let replyH (w : WH) := sourceCurvatureSelector (3*γ/4) (valH w)
    have hvH : Measurable valH := checkpointValue_measurable (fun _ => t) measurable_const
      (fun w : WH => w.1.2.2.2.2) measurable_fst.snd.snd.snd.snd Prod.snd measurable_snd
    have hcH : Measurable cacheH := installCheckpoint_measurable (fun _ => t) measurable_const
      (fun w : WH => w.1.2.2.2.2) measurable_fst.snd.snd.snd.snd
      (fun w : WH => w.1.2.1) measurable_fst.snd.fst Prod.snd measurable_snd
    have hrH : Measurable replyH := (sourceCurvatureSelector_measurable _).comp hvH
    have hcurv : OracleProgram.MeasurableFamily q₀ none
        (fun w : WH => curvatureFirstProgram hBg hBH P ε γ scaleG scaleH w.1.1 m (t+1)
          (curvatureNext (γ/P.hessianLip) w.1.2.1 (curvatureVector (replyH w)) (w.1.1 t),
            w.1.2.2.1, w.1.2.2.2.1, cacheH w)) := by
      apply (ih (t+1)).comp (fun w : WH => (w.1.1,
        (curvatureNext (γ/P.hessianLip) w.1.2.1 (curvatureVector (replyH w)) (w.1.1 t),
          w.1.2.2.1, w.1.2.2.2.1, cacheH w)))
      have hx := (curvatureNext_measurable (d := d) (γ/P.hessianLip)).comp
        (measurable_fst.snd.fst.prodMk
          ((curvatureVector_measurable.comp hrH).prodMk ((measurable_pi_apply t).comp measurable_fst.fst)))
      exact measurable_fst.fst.prodMk (hx.prodMk
        (measurable_fst.snd.snd.fst.prodMk (measurable_fst.snd.snd.snd.fst.prodMk hcH)))
    let valG (w : WG) := checkpointValue w.1.1.2.2.1 w.1.1.2.2.2.1 w.2
    let cacheG (w : WG) := installCheckpoint w.1.1.2.2.1 w.1.1.2.2.2.1 w.1.1.2.1 w.2
    have hvG : Measurable valG := checkpointValue_measurable _ measurable_fst.fst.snd.snd.fst
      _ measurable_fst.fst.snd.snd.snd.fst _ measurable_snd
    have hcG : Measurable cacheG := installCheckpoint_measurable _ measurable_fst.fst.snd.snd.fst
      _ measurable_fst.fst.snd.snd.snd.fst _ measurable_fst.fst.snd.fst _ measurable_snd
    have hmove : OracleProgram.MeasurableFamily q₀ none
        (fun w : WG => curvatureFirstProgram hBg hBH P ε γ scaleG scaleH w.1.1.1 m (t+1)
          (gradientMove P ε w.1.1.2.1 (valG w), w.1.1.2.2.1+1, cacheG w, cacheH w.1)) := by
      apply (ih (t+1)).comp (fun w : WG => (w.1.1.1,
        (gradientMove P ε w.1.1.2.1 (valG w), w.1.1.2.2.1+1, cacheG w, cacheH w.1)))
      have hx := (gradientMove_measurable (d := d) P ε).comp (measurable_fst.fst.snd.fst.prodMk hvG)
      exact measurable_fst.fst.fst.prodMk (hx.prodMk
        ((measurable_fst.fst.snd.snd.fst.add_const 1).prodMk (hcG.prodMk (hcH.comp measurable_fst))))
    have hdone : OracleProgram.MeasurableFamily (Y := PersistentReply d) q₀ none (fun w : WG => .done (some w.1.1.2.1)) :=
      OracleProgram.measurableFamily_done q₀ none (fun w : WG => some w.1.1.2.1)
        ((optimizerOutput_some_measurable d).comp measurable_fst.fst.snd.fst)
    have hgcond : MeasurableSet {w : WG | ‖valG w‖ ≤ 3*ε/4} := measurableSet_le hvG.norm measurable_const
    have hG : OracleProgram.MeasurableFamily q₀ none (fun w : WH =>
        OracleProgram.bind
          (checkpointProgram hBg scaleG P.gradientNoise P.gradientLip true Prod.fst
            (gradientReserve T Bg BH) w.1.2.2.1 w.1.2.2.2.1 w.1.2.1)
          (fun packetG => if ‖valG (w,packetG)‖ ≤ 3*ε/4 then .done (some w.1.2.1) else
            curvatureFirstProgram hBg hBH P ε γ scaleG scaleH w.1.1 m (t+1)
              (gradientMove P ε w.1.2.1 (valG (w,packetG)), w.1.2.2.1+1,
                cacheG (w,packetG), cacheH w))) :=
      (checkpointProgram_measurableFamily hBg scaleG P.gradientNoise P.gradientLip q₀ true
      Prod.fst measurable_fst (gradientReserve T Bg BH)
      (fun w : WH => w.1.2.2.1) measurable_fst.snd.snd.fst
      (fun w : WH => w.1.2.2.2.1) measurable_fst.snd.snd.snd.fst
      (fun w : WH => w.1.2.1) measurable_fst.snd.fst).bind (hdone.ite hmove _ hgcond)
    have hhcond : MeasurableSet {w : WH | curvatureTag (replyH w) = true} :=
      (curvatureTag_measurable.comp hrH) (measurableSet_singleton true)
    have hbranch := hcurv.ite hG {w : WH | curvatureTag (replyH w) = true} hhcond
    simpa only [curvatureFirstProgram] using
      (checkpointProgram_measurableFamily hBH scaleH P.hessianNoise P.hessianLip q₀ false
      Prod.snd measurable_snd (hessianReserve T Bg BH) (fun _ : W => t) measurable_const
      (fun w : W => w.2.2.2.2) measurable_snd.snd.snd.snd
      (fun w : W => w.2.1) measurable_snd.fst).bind hbranch

end
end SampleReuse
