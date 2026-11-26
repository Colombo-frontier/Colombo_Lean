import GradientHessian.NalenPolicyData
import GradientHessian.ClockedOraclePolicy

/-! An actual NALEN mixed-query policy. Its finite public schedule has
one initial gradient and four instructions per iteration: optional rich
snapshot, predictor gradient, corrector gradient, optional candidate check.
Internal instructions require no oracle reply. -/

noncomputable section
namespace GradientHessian.NalenPolicy
open MeasureTheory Model Nalen

instance operatorMeasurable (d : ℕ) : MeasurableSpace (Point d →L[ℝ] Point d) := borel _
instance operatorBorel (d : ℕ) : BorelSpace (Point d →L[ℝ] Point d) := ⟨rfl⟩

def readGradient {d : ℕ} (o : OrdinaryReply d) : Point d :=
  (InnerProductSpace.toDual ℝ (Point d)).symm o.2

def readHessian {d : ℕ} (r : RichReply d) : Point d →L[ℝ] Point d :=
  (InnerProductSpace.toDual ℝ (Point d)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp r.2.2

@[fun_prop] theorem readGradient_measurable (d : ℕ) : Measurable (readGradient (d := d)) :=
  (InnerProductSpace.toDual ℝ (Point d)).symm.continuous.measurable.comp measurable_snd

@[fun_prop] theorem readHessian_measurable (d : ℕ) : Measurable (readHessian (d := d)) := by
  apply Continuous.measurable
  exact continuous_const.clm_comp continuous_snd.snd

@[simp] theorem readGradient_oracle {d : ℕ} (f : Point d → ℝ) (x : Point d) :
    readGradient (ordinaryOracle f x)=gradient f x := rfl

@[simp] theorem readHessian_oracle {d : ℕ} (f : Point d → ℝ) (x : Point d) :
    readHessian (richOracle f x)=hessianOperator f x := rfl

def iteration (k : ℕ) : ℕ := (k-1)/4
def phase (k : ℕ) : ℕ := (k-1)%4

theorem iteration_clock (n r : ℕ) (hr : r<4) : iteration (1+4*n+r)=n := by unfold iteration; omega
theorem phase_clock (n r : ℕ) (hr : r<4) : phase (1+4*n+r)=r := by unfold phase; omega

def kind (m q k : ℕ) : Fin 3 :=
  if k=0 then 1
  else if phase k=0 then if iteration k%m=0 then 2 else 0
  else if phase k=3 then if (iteration k+1)%q=0 then 1 else 0
  else 1

def queryPoint {d : ℕ} (q k : ℕ) (s : Data (Point d)) : Point d :=
  if k=0 then 0 else if phase k=3 then average q (iteration k) s
    else Nalen.midpoint (position s) (delta s)

def ordinaryUpdate {d : ℕ} {D : ℝ} (hD : 0≤D) (η : ℝ) (q k : ℕ)
    (p : Data (Point d) × OrdinaryReply d) : Data (Point d) :=
  if k=0 then initial D (readGradient p.2)
  else if phase k=1 then predict hD η p.1 (readGradient p.2)
  else if phase k=2 then correct hD η (iteration k) p.1 (readGradient p.2)
  else consider q (iteration k) p.1 (readGradient p.2)

def richUpdate {d : ℕ} (p : Data (Point d) × RichReply d) : Data (Point d) :=
  snapshot p.1 (readHessian p.2)

theorem queryPoint_measurable (d q k : ℕ) : Measurable (queryPoint (d := d) q k) := by
  unfold queryPoint
  split_ifs
  · exact measurable_const
  · exact average_measurable q (iteration k)
  · unfold Nalen.midpoint
    fun_prop

theorem predictReply_measurable (d : ℕ) {D : ℝ} (hD : 0≤D) (η : ℝ) :
    Measurable (fun p : Data (Point d) × OrdinaryReply d => predict hD η p.1 (readGradient p.2)) := by
  have hm : Measurable (fun p : Data (Point d) × OrdinaryReply d => (p.1,readGradient p.2)) :=
    measurable_fst.prodMk ((readGradient_measurable d).comp measurable_snd)
  exact (predict_measurable (E := Point d) hD η).comp hm

theorem correctReply_measurable (d : ℕ) {D : ℝ} (hD : 0≤D) (η : ℝ) (n : ℕ) :
    Measurable (fun p : Data (Point d) × OrdinaryReply d => correct hD η n p.1 (readGradient p.2)) := by
  have hm : Measurable (fun p : Data (Point d) × OrdinaryReply d => (p.1,readGradient p.2)) :=
    measurable_fst.prodMk ((readGradient_measurable d).comp measurable_snd)
  exact (correct_measurable (E := Point d) hD η n).comp hm

theorem considerReply_measurable (d q n : ℕ) :
    Measurable (fun p : Data (Point d) × OrdinaryReply d => consider q n p.1 (readGradient p.2)) := by
  have hm : Measurable (fun p : Data (Point d) × OrdinaryReply d => (p.1,readGradient p.2)) :=
    measurable_fst.prodMk ((readGradient_measurable d).comp measurable_snd)
  simpa only [Function.comp_def] using (consider_measurable (E := Point d) q n).comp hm

theorem ordinaryUpdate_measurable (d : ℕ) {D : ℝ} (hD : 0≤D) (η : ℝ) (q k : ℕ) :
    Measurable (ordinaryUpdate (d := d) hD η q k) := by
  unfold ordinaryUpdate
  split_ifs
  · exact (initial_measurable (E := Point d) D).comp ((readGradient_measurable d).comp measurable_snd)
  · exact predictReply_measurable d hD η
  · exact correctReply_measurable d hD η (iteration k)
  · exact considerReply_measurable d q (iteration k)

theorem richUpdate_measurable (d : ℕ) : Measurable (richUpdate (d := d)) :=
  snapshot_measurable.comp (measurable_fst.prodMk ((readHessian_measurable d).comp measurable_snd))

def program (d : ℕ) {D : ℝ} (hD : 0≤D) (η : ℝ) (m q N : ℕ) :
    ClockedOracle.Program (PUnit : Type) (Data (Point d)) (Point d) (OrdinaryReply d) (RichReply d) where
  length := 1+4*N
  kind := kind m q
  initial := fun _ => make 0 0 0 0 (fun _ => 0) 0 0
  point := queryPoint q
  output := best
  think := fun _ => id
  ordinaryNext := ordinaryUpdate hD η q
  richNext := fun _ => richUpdate
  initial_measurable := measurable_const
  point_measurable := queryPoint_measurable d q
  output_measurable := best_measurable
  think_measurable := fun _ => measurable_id
  ordinaryNext_measurable := ordinaryUpdate_measurable d hD η q
  richNext_measurable := fun _ => richUpdate_measurable d

def policy (d : ℕ) {D : ℝ} (hD : 0≤D) (η : ℝ) (m q N : ℕ) :=
  (program d hD η m q N).policy

def algorithm (d : ℕ) {D : ℝ} (hD : 0≤D) (η : ℝ) (m q N : ℕ) : Model.Algorithm d where
  Seed := PUnit
  State := ℕ × Data (Point d)
  seedSpace := inferInstance
  stateSpace := inferInstance
  seedLaw := Measure.dirac PUnit.unit
  probability := inferInstance
  policy := policy d hD η m q N

theorem policy_terminates (d : ℕ) {D : ℝ} (hD : 0≤D) (η : ℝ) (m q N : ℕ)
    (ordinary : Point d → OrdinaryReply d) (rich : Point d → RichReply d) :
    (policy d hD η m q N).Terminates ordinary rich :=
  (program d hD η m q N).terminates ordinary rich

theorem policy_halts_by (d : ℕ) {D : ℝ} (hD : 0≤D) (η : ℝ) (m q N : ℕ)
    (ordinary : Point d → OrdinaryReply d) (rich : Point d → RichReply d) :
    (policy d hD η m q N).mode ((policy d hD η m q N).run ordinary rich (1+4*N) PUnit.unit)=0 :=
  (program d hD η m q N).halt ordinary rich PUnit.unit

theorem policy_schedule_caps (d : ℕ) {D : ℝ} (hD : 0≤D) (η : ℝ) (m q N : ℕ)
    (ordinary : Point d → OrdinaryReply d) (rich : Point d → RichReply d) :
    (policy d hD η m q N).HasCaps ordinary rich
      ((program d hD η m q N).count 1) ((program d hD η m q N).count 2) :=
  (program d hD η m q N).hasCaps ordinary rich

@[simp] theorem kind_initial (m q : ℕ) : kind m q 0=1 := rfl

theorem kind_snapshot (m q n : ℕ) : kind m q (1+4*n)=if n%m=0 then 2 else 0 := by
  have hn : 1+4*n≠0 := by omega
  have hi := iteration_clock n 0 (by omega)
  have hp := phase_clock n 0 (by omega)
  simp only [Nat.add_zero] at hi hp
  simp [kind,hn,hi,hp]

theorem kind_predict (m q n : ℕ) : kind m q (1+4*n+1)=1 := by
  have hn : 1+4*n+1≠0 := by omega
  simp [kind,hn,phase_clock n 1 (by omega)]

theorem kind_correct (m q n : ℕ) : kind m q (1+4*n+2)=1 := by
  have hn : 1+4*n+2≠0 := by omega
  simp [kind,hn,phase_clock n 2 (by omega)]

theorem kind_candidate (m q n : ℕ) : kind m q (1+4*n+3)=if (n+1)%q=0 then 1 else 0 := by
  have hn : 1+4*n+3≠0 := by omega
  simp [kind,hn,phase_clock n 3 (by omega),iteration_clock n 3 (by omega)]

end GradientHessian.NalenPolicy
