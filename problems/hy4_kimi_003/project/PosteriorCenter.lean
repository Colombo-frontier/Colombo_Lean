import PosteriorCenterCore

open MeasureTheory Set
open scoped RealInnerProductSpace

set_option maxHeartbeats 1000000

namespace Task006.PosteriorCenter

open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereState Task006.AdaptiveSphereFrame
open Task006.AdaptiveSphereResidualFrame Task006.AdaptiveSphereGeometry
open Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereMeasurable

noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

def centerStep (k : ℕ) (hkd : k ≤ d) (state : FrameState d) (C q : E d) (a : ℝ) : E d :=
  if hr : state.1.val < k then
    let pivot : Fin d := ⟨state.1.val,by omega⟩
    let res := residualCoordinates pivot.val (Nat.le_of_lt pivot.isLt) (action state.2⁻¹ q)
    if res = 0 then C else
      C + ((a - inner ℝ C q) / ‖res‖) • frameVector (residualUpdate pivot state.2 q) pivot
  else C

theorem measurable_frameVector (j : Fin d) :
    Measurable (fun B : OrthogonalGroup d => frameVector B j) := by
  have hm := (orthogonal_action_measurable (d := d)).comp
    (measurable_id.prodMk (measurable_const (a := (EuclideanSpace.basisFun (Fin d) ℝ) j)))
  simpa only [frameVector,Function.comp_def,id_eq] using hm

theorem measurable_centerStep (k : ℕ) (hkd : k ≤ d) :
    Measurable (fun p : FrameState d × (E d × (E d × ℝ)) =>
      centerStep k hkd p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  classical
  have hfixed (rank : Fin (d+1)) :
      Measurable (fun p : OrthogonalGroup d × (E d × (E d × ℝ)) =>
        centerStep k hkd (rank,p.1) p.2.1 p.2.2.1 p.2.2.2) := by
    by_cases hr : rank.val < k
    · let pivot : Fin d := ⟨rank.val,by omega⟩
      have hBq : Measurable (fun p : OrthogonalGroup d × (E d × (E d × ℝ)) => (p.1,p.2.2.1)) :=
        measurable_fst.prodMk measurable_snd.snd.fst
      have hres : Measurable (fun p : OrthogonalGroup d × (E d × (E d × ℝ)) =>
          residualCoordinates pivot.val (Nat.le_of_lt pivot.isLt) (action p.1⁻¹ p.2.2.1)) := by
        have hm := (continuous_residualCoordinates pivot.val (Nat.le_of_lt pivot.isLt)).measurable.comp
          (orthogonal_inverse_action_measurable.comp hBq)
        simpa only [Function.comp_def] using hm
      have hpivot : Measurable (fun p : OrthogonalGroup d × (E d × (E d × ℝ)) =>
          frameVector (residualUpdate pivot p.1 p.2.2.1) pivot) := by
        have hm := (measurable_frameVector pivot).comp ((measurable_residualUpdate pivot).comp hBq)
        simpa only [Function.comp_def] using hm
      have hresult : Measurable (fun p : OrthogonalGroup d × (E d × (E d × ℝ)) =>
          if residualCoordinates pivot.val (Nat.le_of_lt pivot.isLt) (action p.1⁻¹ p.2.2.1) = 0 then p.2.1
          else p.2.1 + ((p.2.2.2 - inner ℝ p.2.1 p.2.2.1) /
            ‖residualCoordinates pivot.val (Nat.le_of_lt pivot.isLt) (action p.1⁻¹ p.2.2.1)‖) •
              frameVector (residualUpdate pivot p.1 p.2.2.1) pivot) :=
        Measurable.ite (hres (measurableSet_singleton 0))
        measurable_snd.fst
        (measurable_snd.fst.add
          (((measurable_snd.snd.snd.sub (measurable_snd.fst.inner measurable_snd.snd.fst)).div hres.norm).smul hpivot))
      simpa only [centerStep,dif_pos hr,Function.comp_def] using hresult
    · simpa only [centerStep,dif_neg hr] using
        (measurable_snd.fst : Measurable (fun p : OrthogonalGroup d × (E d × (E d × ℝ)) => p.2.1))
  have hm : Measurable (fun p : Fin (d+1) × (OrthogonalGroup d × (E d × (E d × ℝ))) =>
      centerStep k hkd (p.1,p.2.1) p.2.2.1 p.2.2.2.1 p.2.2.2.2) :=
    measurable_from_prod_countable_right hfixed
  have hr : Measurable (fun p : FrameState d × (E d × (E d × ℝ)) =>
      (p.1.1,(p.1.2,p.2))) := measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)
  simpa only [Function.comp_def] using hm.comp hr

theorem centerStep_projected (k : ℕ) (hkd : k ≤ d) (state : FrameState d) (q θ : E d) :
    centerStep k hkd state (projectedCenter state θ) q (inner ℝ θ q) =
      projectedCenter (stateStep k hkd state q) θ := by
  by_cases hr : state.1.val < k
  · let pivot : Fin d := ⟨state.1.val,by omega⟩
    by_cases hz : residualCoordinates pivot.val (Nat.le_of_lt pivot.isLt) (action state.2⁻¹ q) = 0
    · dsimp only [pivot] at hz
      simp only [centerStep,stateStep,dif_pos hr,hz,if_pos]
    · have hu := (projectedCenter_update pivot state.2 q θ hz).symm
      dsimp only [pivot] at hz hu
      simpa only [centerStep,stateStep,dif_pos hr,hz,if_neg,ite_false] using hu
  · simp only [centerStep,stateStep,dif_neg hr]

def centerFromTranscript (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) : ℕ → Transcript N → E d
  | 0, _ => 0
  | t+1, h =>
    if ht : t < N then
      centerStep k hkd (frameFromTranscript A weight tape seed k hkd t h)
        (centerFromTranscript A weight tape seed k hkd t h)
        (effectiveVector weight tape (A.action ⟨t,ht⟩ seed h)) (h ⟨t,ht⟩)
    else centerFromTranscript A weight tape seed k hkd t h

theorem measurable_centerFromTranscript (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) :
    Measurable (centerFromTranscript A weight tape seed k hkd t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    by_cases ht : t < N
    · have hq : Measurable (fun h : Transcript N => effectiveVector weight tape (A.action ⟨t,ht⟩ seed h)) :=
        (measurable_effectiveVector weight tape).comp
        ((A.action_measurable ⟨t,ht⟩).comp (measurable_const.prodMk measurable_id))
      have hm := (measurable_centerStep k hkd).comp
        ((measurable_frameFromTranscript A weight tape seed k hkd t).prodMk
          (ih.prodMk (hq.prodMk (measurable_pi_apply ⟨t,ht⟩))))
      simpa only [centerFromTranscript,dif_pos ht,Function.comp_def] using hm
    · simpa only [centerFromTranscript,dif_neg ht] using ih

theorem centerFromTranscript_past_only (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (h h' : Transcript N) (hpast : ∀ i, i.val < t → h i = h' i) :
    centerFromTranscript A weight tape seed k hkd t h =
      centerFromTranscript A weight tape seed k hkd t h' := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hp := fun i (hi : i.val < t) => hpast i (by omega)
    have hprev := ih hp
    rw [centerFromTranscript,centerFromTranscript]
    split_ifs with ht
    · rw [hprev,frameFromTranscript_past_only A weight tape seed k hkd t h h' hp,
        A.past_only ⟨t,ht⟩ seed h h' hp,hpast ⟨t,ht⟩ (by simp)]
    · exact hprev

theorem projectedCenter_initial (θ : E d) : projectedCenter (initialState d) θ = 0 := by
  simp [projectedCenter,initialState,prefixPart]
  rfl

theorem centerFromTranscript_eq_projected_of_consistent (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (h : Transcript N) (θ : E d)
    (hreply : ∀ i : Fin N, h i = inner ℝ θ (effectiveVector weight tape (A.action i seed h)))
    (t : ℕ) :
    centerFromTranscript A weight tape seed k hkd t h =
      projectedCenter (frameFromTranscript A weight tape seed k hkd t h) θ := by
  induction t with
  | zero => exact (projectedCenter_initial θ).symm
  | succ t ih =>
    rw [centerFromTranscript,frameFromTranscript]
    split_ifs with ht
    · rw [ih,hreply ⟨t,ht⟩,centerStep_projected]
    · exact ih

theorem finalTranscript_consistent (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (θ : E d) (i : Fin N) :
    A.finalTranscript (linearSample weight θ) tape seed i = inner ℝ θ
      (effectiveVector weight tape
        (A.action i seed (A.finalTranscript (linearSample weight θ) tape seed))) := by
  have ha : A.action i seed (A.finalTranscript (linearSample weight θ) tape seed) =
      A.executedAction (linearSample weight θ) tape seed i := by
    apply A.past_only
    intro j hj
    exact runPrefix_coordinate_stable A (linearSample weight θ) tape seed i.val N
      (Nat.le_of_lt i.isLt) j hj
  rw [ha]
  change A.runPrefix (linearSample weight θ) tape seed N i = _
  rw [runPrefix_coordinate_stable A (linearSample weight θ) tape seed (i.val+1) N
    (by omega) i (by omega),runPrefix_succ_self,scalarReply_linear]

theorem centerFromTranscript_actual_eq_projected (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (θ : E d) (t : ℕ) :
    centerFromTranscript A weight tape seed k hkd t
        (A.finalTranscript (linearSample weight θ) tape seed) =
      projectedCenter (frameFromTranscript A weight tape seed k hkd t
        (A.finalTranscript (linearSample weight θ) tape seed)) θ :=
  centerFromTranscript_eq_projected_of_consistent A weight tape seed k hkd _ θ
    (finalTranscript_consistent A weight tape seed θ) t

end
end Task006.PosteriorCenter
