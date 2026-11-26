import UpperProgramIntegrability
import UpperOptimizationMoments

/-! Exact iid round-block law of the actual private seed and sample tape. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped BigOperators

namespace Task006.Full

abbrev UpperSampleBlock (d : ℕ) (Ω : Type*) := UpperBlockSeed d × (Fin d → Ω)

noncomputable def upperSampleBlockLaw {Ω : Type*} [MeasurableSpace Ω]
    (d : ℕ) (μ : Measure Ω) : Measure (UpperSampleBlock d Ω) :=
  (upperBlockSeedLaw d).prod (Measure.pi (fun _ : Fin d => μ))

instance upperSampleBlockLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (d : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ] : IsProbabilityMeasure (upperSampleBlockLaw d μ) := by
  unfold upperSampleBlockLaw
  infer_instance

def upperHandleIndex {d T : ℕ} (p : Fin T × Fin d) : ℕ := p.1.val * d + p.2.val

theorem upperHandleIndex_injective {d T : ℕ} (hd : 0 < d) :
    Function.Injective (@upperHandleIndex d T) := by
  have hdiv (p : Fin T × Fin d) : upperHandleIndex p / d = p.1.val := by
    unfold upperHandleIndex
    rw [Nat.mul_comm, Nat.mul_add_div hd, Nat.div_eq_of_lt p.2.isLt, Nat.add_zero]
  have hmod (p : Fin T × Fin d) : upperHandleIndex p % d = p.2.val := by
    simp [upperHandleIndex, Nat.add_mod, Nat.mod_eq_of_lt p.2.isLt]
  intro p q hpq
  apply Prod.ext
  · apply Fin.ext
    rw [← hdiv p, ← hdiv q, hpq]
  · apply Fin.ext
    rw [← hmod p, ← hmod q, hpq]

def upperSamplePath {d T : ℕ} {Ω : Type*} (tape : ℕ → Ω) (t : Fin T) (i : Fin d) : Ω :=
  tape (t.val * d + i.val)

theorem upperSamplePath_measurable {d T : ℕ} {Ω : Type*} [MeasurableSpace Ω] :
    Measurable (@upperSamplePath d T Ω) := by
  apply measurable_pi_lambda
  intro t
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

theorem upperSamplePath_map {d T : ℕ} (hd : 0 < d) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    (iidHandleLaw μ).map (@upperSamplePath d T Ω) =
      Measure.pi (fun _t : Fin T => Measure.pi (fun _i : Fin d => μ)) := by
  let flat : (ℕ → Ω) → (Fin T × Fin d → Ω) := fun tape p => tape (upperHandleIndex p)
  have hflat : Measurable flat := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hiNat : iIndepFun (fun h : ℕ => fun tape : ℕ → Ω => tape h) (iidHandleLaw μ) :=
    iIndepFun_infinitePi (X := fun _ ω => ω) (fun _ => measurable_id)
  have hiFlat : iIndepFun (fun p : Fin T × Fin d => fun tape : ℕ → Ω => tape (upperHandleIndex p))
      (iidHandleLaw μ) := hiNat.precomp (upperHandleIndex_injective hd)
  have hflatMap : (iidHandleLaw μ).map flat = Measure.pi (fun _ : Fin T × Fin d => μ) := by
    have hm := hiFlat.map_fun_eq_pi_map (fun _ => (measurable_pi_apply _).aemeasurable)
    simpa only [flat, iidHandleLaw, infinitePi_map_eval] using hm
  have hcur : (Measure.pi (fun _ : Fin T × Fin d => μ)).map (MeasurableEquiv.curry (Fin T) (Fin d) Ω) =
      Measure.pi (fun _t : Fin T => Measure.pi (fun _i : Fin d => μ)) := by
    simpa only [infinitePi_eq_pi] using infinitePi_map_curry (fun _ : Fin T => fun _ : Fin d => μ)
  have hcomp : (@upperSamplePath d T Ω) = (MeasurableEquiv.curry (Fin T) (Fin d) Ω) ∘ flat := rfl
  rw [hcomp, ← Measure.map_map (MeasurableEquiv.curry (Fin T) (Fin d) Ω).measurable hflat,
    hflatMap, hcur]

def upperBlockPath {d T : ℕ} {Ω : Type*} (w : UpperSeed d T × (ℕ → Ω)) (t : Fin T) : UpperSampleBlock d Ω :=
  (w.1 t, upperSamplePath w.2 t)

theorem upperBlockPath_measurable {d T : ℕ} {Ω : Type*} [MeasurableSpace Ω] :
    Measurable (@upperBlockPath d T Ω) := by
  apply measurable_pi_lambda
  intro t
  exact ((measurable_pi_apply t).comp measurable_fst).prodMk
    ((measurable_pi_apply t).comp (upperSamplePath_measurable.comp measurable_snd))

/-- The actual program's round blocks are iid with the original public Haar/U
law and independent fresh sample handles. This is a proved pushforward identity,
not an assumed conditional sampling law. -/
theorem upperBlockPath_map {d T : ℕ} (hd : 0 < d) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ((upperSeedLaw d T).prod (iidHandleLaw μ)).map (@upperBlockPath d T Ω) =
      Measure.pi (fun _ : Fin T => upperSampleBlockLaw d μ) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow (UpperBlockSeed d) (Fin d → Ω) (Fin T)
  have hm := Measure.map_prod_map (upperSeedLaw d T) (iidHandleLaw μ)
    measurable_id (@upperSamplePath_measurable d T Ω _)
  rw [Measure.map_id, upperSamplePath_map hd μ] at hm
  have heq : (@upperBlockPath d T Ω) = e.symm ∘ Prod.map id (@upperSamplePath d T Ω) := rfl
  rw [heq, ← Measure.map_map e.symm.measurable (measurable_id.prodMap upperSamplePath_measurable), ← hm]
  exact (measurePreserving_arrowProdEquivProdArrow (UpperBlockSeed d) (Fin d → Ω) (Fin T)
    (fun _ => upperBlockSeedLaw d) (fun _ => Measure.pi (fun _ : Fin d => μ))).symm.map_eq

noncomputable def upperBlockDirection {d : ℕ} {Ω : Type*} (P : UpperProgramParameters)
    (F : Space d → Ω → ℝ) (x : Space d) (block : UpperSampleBlock d Ω) : Space d :=
  orthogonalReconstruct block.1.1 (fun i => scalarClip P.b
    ((F (x + P.δ • Task006.HaarRebalancing.column block.1.1 i + P.ρ • (block.1.2 i).val) (block.2 i) -
      F (x - P.δ • Task006.HaarRebalancing.column block.1.1 i + P.ρ • (block.1.2 i).val) (block.2 i)) /
        (2 * P.δ)))

noncomputable def upperBlockIterate {d T : ℕ} {Ω : Type*} (P : UpperProgramParameters)
    (F : Space d → Ω → ℝ) (blocks : Fin T → UpperSampleBlock d Ω) : ℕ → Space d
  | 0 => 0
  | t + 1 => if ht : t < T then
      ballProj (P.R - (P.ρ + P.δ)) P.inner_nonneg
        (upperBlockIterate P F blocks t - P.η • upperBlockDirection P F
          (upperBlockIterate P F blocks t) (blocks ⟨t, ht⟩))
    else upperBlockIterate P F blocks t

theorem upperDirection_eq_blockDirection {d T : ℕ} (P : UpperProgramParameters) (hd : 0 < d)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {L : ℝ}
    (I : SampleInstance d L P.R Ω μ) (tape : ℕ → Ω) (seed : UpperSeed d T) (t : Fin T) :
    upperDirection P (seed t) ((upperPairedProgram P hd).toAlgorithm.finalTranscript I.sample tape seed) t.val =
      upperBlockDirection P I.sample
        (upperIterate P seed ((upperPairedProgram P hd).toAlgorithm.finalTranscript I.sample tape seed) t.val)
        (upperBlockPath (seed, tape) t) := by
  unfold upperDirection upperBlockDirection orthogonalReconstruct
  apply Finset.sum_congr rfl
  intro i _
  change scalarClip P.b (upperRecordedSecant P
      ((upperPairedProgram P hd).toAlgorithm.finalTranscript I.sample tape seed) t i) •
      Task006.HaarRebalancing.column (seed t).1 i =
    scalarClip P.b (I.oracleSecant P.ρ P.δ
      (upperIterate P seed ((upperPairedProgram P hd).toAlgorithm.finalTranscript I.sample tape seed) t.val)
      (Task006.HaarRebalancing.column (seed t).1 i) ((seed t).2 i).val (tape (t.val * d + i.val))) •
      Task006.HaarRebalancing.column (seed t).1 i
  rw [upperRecordedSecant_eq_oracleSecant P hd I tape seed t i]

theorem upperIterate_eq_blockIterate {d T : ℕ} (P : UpperProgramParameters) (hd : 0 < d)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {L : ℝ}
    (I : SampleInstance d L P.R Ω μ) (tape : ℕ → Ω) (seed : UpperSeed d T) (t : ℕ) :
    upperIterate P seed ((upperPairedProgram P hd).toAlgorithm.finalTranscript I.sample tape seed) t =
      upperBlockIterate P I.sample (upperBlockPath (seed, tape)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [upperIterate, upperBlockIterate]
    split_ifs with ht
    · rw [upperDirection_eq_blockDirection P hd I tape seed ⟨t, ht⟩, ih]
    · exact ih

theorem upperBlockDirection_norm_le {d : ℕ} {Ω : Type*} (P : UpperProgramParameters)
    (F : Space d → Ω → ℝ) (x : Space d) (block : UpperSampleBlock d Ω) :
    ‖upperBlockDirection P F x block‖ ≤ Real.sqrt d * P.b := by
  apply orthogonalReconstruct_norm_le _ _ P.clip_nonneg
  intro i
  rw [abs_scalarClip P.clip_nonneg]
  exact min_le_right _ _

theorem upperBlockIterate_norm_le {d T : ℕ} {Ω : Type*} (P : UpperProgramParameters)
    (F : Space d → Ω → ℝ) (blocks : Fin T → UpperSampleBlock d Ω) (t : ℕ) :
    ‖upperBlockIterate P F blocks t‖ ≤ P.R - (P.ρ + P.δ) := by
  induction t with
  | zero => simpa only [upperBlockIterate, norm_zero] using P.inner_nonneg
  | succ t ih =>
    rw [upperBlockIterate]
    split_ifs with ht
    · simpa only [Metric.mem_closedBall, dist_zero_right] using
        ballProj_mem (P.R - (P.ρ + P.δ)) P.inner_nonneg
          (upperBlockIterate P F blocks t - P.η • upperBlockDirection P F
            (upperBlockIterate P F blocks t) (blocks ⟨t, ht⟩))
    · exact ih

theorem upperBlockIterate_past {d T : ℕ} {Ω : Type*} (P : UpperProgramParameters)
    (F : Space d → Ω → ℝ) {blocks blocks' : Fin T → UpperSampleBlock d Ω} (t : ℕ)
    (hh : ∀ j : Fin T, j.val < t → blocks j = blocks' j) :
    upperBlockIterate P F blocks t = upperBlockIterate P F blocks' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hprev : ∀ j : Fin T, j.val < t → blocks j = blocks' j := fun j hj => hh j (by omega)
    rw [upperBlockIterate, upperBlockIterate]
    split_ifs with ht
    · rw [ih hprev, hh ⟨t, ht⟩ (Nat.lt_succ_self t)]
    · exact ih hprev

theorem upperBlockDirection_measurable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : UpperProgramParameters) {F : Space d → Ω → ℝ} (hF : Measurable (Function.uncurry F)) :
    Measurable (fun xb : Space d × UpperSampleBlock d Ω => upperBlockDirection P F xb.1 xb.2) := by
  unfold upperBlockDirection orthogonalReconstruct
  apply Finset.measurable_sum
  intro i _
  have hseed : Measurable (fun xb : Space d × UpperSampleBlock d Ω => xb.2.1) :=
    measurable_fst.comp measurable_snd
  have hq := (Task006.HaarRebalancing.measurable_column i).comp (measurable_fst.comp hseed)
  have hu := measurable_subtype_coe.comp ((measurable_pi_apply i).comp (measurable_snd.comp hseed))
  have hz : Measurable (fun xb : Space d × UpperSampleBlock d Ω => xb.2.2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  have hp := hF.comp (((measurable_fst.add (hq.const_smul P.δ)).add (hu.const_smul P.ρ)).prodMk hz)
  have hm := hF.comp (((measurable_fst.sub (hq.const_smul P.δ)).add (hu.const_smul P.ρ)).prodMk hz)
  exact (((scalarClip_continuous P.clip_nonneg).measurable.comp ((hp.sub hm).div_const (2 * P.δ))).smul hq)

#print axioms upperSamplePath_map
#print axioms upperBlockPath_map
#print axioms upperIterate_eq_blockIterate

end Task006.Full
