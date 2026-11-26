import ExactValue.CenteredAcceleration

open scoped InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace ExactValue
noncomputable section

def centeredBatchPoint {d : ℕ} (K : ClosedConvexDomain d) (c : Euclid d)
    (L h : ℝ) (v : ℕ → ℝ) (t : ℕ) : Euclid d :=
  batchPoint (centeredDomain K c) L h v t + c

def centeredBatchOutput {d : ℕ} (K : ClosedConvexDomain d) (c : Euclid d)
    (L h : ℝ) (v : ℕ → ℝ) (N : ℕ) : Euclid d :=
  (batchRun (centeredDomain K c) L h v N).x + c

theorem centeredBatchOutput_mem {d : ℕ} (K : ClosedConvexDomain d) {c : Euclid d}
    (hc : c ∈ K.carrier) {L : ℝ} (hL : 0 < L) (h : ℝ) (v : ℕ → ℝ) (N : ℕ) :
    centeredBatchOutput K c L h v N ∈ K.carrier :=
  batchRun_mem (centeredDomain K c) (by simpa [centeredDomain] using hc) hL h v N

theorem centeredBatchPoint_norm {d : ℕ} {c : Euclid d} {R L h : ℝ}
    (hR : 0 ≤ R) (hc : ‖c‖ ≤ R / 2) (hL : 0 < L) (hh : 0 ≤ h) (hhR : h ≤ R / 2)
    (v : ℕ → ℝ) (n : ℕ) :
    ‖centeredBatchPoint (ballDomain (d := d) (R / 2) (by positivity)) c L h v n‖ ≤ R := by
  let K := centeredDomain (ballDomain (d := d) (R / 2) (by positivity)) c
  have hz : (0 : Euclid d) ∈ K.carrier := by simpa [K, centeredDomain, ballDomain] using hc
  have hy : ‖batchY K L h v (n / (d + 1)) + c‖ ≤ R / 2 := by
    simpa only [K, centeredDomain, ballDomain, Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
      using batchY_mem K hz hL h v (n / (d + 1))
  change ‖batchPoint K L h v n + c‖ ≤ R
  unfold batchPoint
  split_ifs with hi
  · exact hy.trans (by linarith)
  · rw [show batchY K L h v (n / (d + 1)) + h • EuclideanSpace.single _ 1 + c =
        (batchY K L h v (n / (d + 1)) + c) + h • EuclideanSpace.single _ 1 by abel]
    exact displaced_query_in_ball hy hh hhR (by simp [EuclideanSpace.norm_single])

theorem centeredBatch_fields_continuous {d : ℕ} (K : ClosedConvexDomain d) (L h : ℝ) (n : ℕ) :
    Continuous (fun p : Euclid d × (ℕ → ℝ) => (batchRun (centeredDomain K p.1) L h p.2 n).x) ∧
      Continuous (fun p : Euclid d × (ℕ → ℝ) => (batchRun (centeredDomain K p.1) L h p.2 n).w) := by
  induction n with
  | zero => exact ⟨continuous_const, continuous_const⟩
  | succ n ih =>
    have hg : Continuous (fun p : Euclid d × (ℕ → ℝ) => batchGradient d h p.2 n) :=
      (batchGradient_continuous d h n).comp continuous_snd
    have hw := ih.2.add ((continuous_const (y := accelerationStep L n)).smul hg)
    constructor
    · simp only [batchRun, batchNext, centeredDomain_project, coupledPoint]
      exact (continuous_const.smul ih.1).add
        (continuous_const.smul (((K.project_continuous.comp (hw.neg.add continuous_fst))).sub continuous_fst))
    · exact hw

theorem centeredBatchPoint_continuous {d : ℕ} (K : ClosedConvexDomain d) (L h : ℝ) (n : ℕ) :
    Continuous (fun p : Euclid d × (ℕ → ℝ) => centeredBatchPoint K p.1 L h p.2 n) := by
  have hf := centeredBatch_fields_continuous K L h (n / (d + 1))
  have hy : Continuous (fun p : Euclid d × (ℕ → ℝ) =>
      batchY (centeredDomain K p.1) L h p.2 (n / (d + 1))) := by
    simp only [batchY, accelY, centeredDomain_project, coupledPoint]
    exact (continuous_const.smul hf.1).add
      (continuous_const.smul ((K.project_continuous.comp (hf.2.neg.add continuous_fst)).sub continuous_fst))
  unfold centeredBatchPoint batchPoint
  split_ifs with hi
  · exact hy.add continuous_fst
  · exact (hy.add continuous_const).add continuous_fst

theorem centeredBatchOutput_continuous {d : ℕ} (K : ClosedConvexDomain d) (L h : ℝ) (N : ℕ) :
    Continuous (fun p : Euclid d × (ℕ → ℝ) => centeredBatchOutput K p.1 L h p.2 N) :=
  (centeredBatch_fields_continuous K L h N).1.add continuous_fst

theorem centeredBatchPoint_continuous_fixed {d : ℕ} (K : ClosedConvexDomain d) (c : Euclid d)
    (L h : ℝ) (n : ℕ) : Continuous (fun v : ℕ → ℝ => centeredBatchPoint K c L h v n) :=
  (centeredBatchPoint_continuous K L h n).comp (f := fun v : ℕ → ℝ => (c, v))
    ((continuous_const (y := c)).prodMk (continuous_id (X := ℕ → ℝ)))

theorem centeredBatchOutput_continuous_fixed {d : ℕ} (K : ClosedConvexDomain d) (c : Euclid d)
    (L h : ℝ) (N : ℕ) : Continuous (fun v : ℕ → ℝ => centeredBatchOutput K c L h v N) :=
  (centeredBatchOutput_continuous K L h N).comp (f := fun v : ℕ → ℝ => (c, v))
    ((continuous_const (y := c)).prodMk (continuous_id (X := ℕ → ℝ)))

/-- One finite-difference accelerated phase, with arbitrary public starting point. -/
def centeredValueAlgorithm {d : ℕ} {R L h : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (hh : 0 ≤ h) (hhR : h ≤ R / 2) (c : QueryBall d (R / 2)) (N : ℕ) :
    ValueAlgorithm d R ((d + 1) * N) where
  query n hist := ⟨centeredBatchPoint (ballDomain (d := d) (R / 2) (by positivity)) c L h (historyValues hist) n,
    centeredBatchPoint_norm hR c.property hL hh hhR _ n⟩
  output hist := ⟨centeredBatchOutput (ballDomain (d := d) (R / 2) (by positivity)) c L h (historyValues hist) N, by
    have hn : ‖centeredBatchOutput (ballDomain (d := d) (R / 2) (by positivity)) c L h (historyValues hist) N‖ ≤ R / 2 :=
      by
        have hc : (c : Euclid d) ∈ (ballDomain (d := d) (R / 2) (by positivity)).carrier := by
          simpa [ballDomain] using c.property
        simpa [ballDomain] using centeredBatchOutput_mem (ballDomain (d := d) (R / 2) (by positivity)) hc hL h
          (historyValues hist) N
    linarith⟩
  query_borel := by
    intro n
    apply Continuous.borel_measurable
    apply Continuous.subtype_mk
    exact (centeredBatchPoint_continuous_fixed (ballDomain (d := d) (R / 2) (by positivity))
      (c : Euclid d) L h n).comp (f := fun hist : QueryHistory d R n => historyValues hist)
        (historyValues_continuous (d := d) (n := n) R)
  output_borel := by
    apply Continuous.borel_measurable
    apply Continuous.subtype_mk
    exact (centeredBatchOutput_continuous_fixed (ballDomain (d := d) (R / 2) (by positivity))
      (c : Euclid d) L h N).comp (f := fun hist : QueryHistory d R ((d + 1) * N) => historyValues hist)
        (historyValues_continuous (d := d) (n := (d + 1) * N) R)

theorem centered_algorithm_query {d : ℕ} {R L h : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (hh : 0 ≤ h) (hhR : h ≤ R / 2) (c : QueryBall d (R / 2)) (N : ℕ)
    (f : Euclid d → ℝ) (t : ℕ) :
    let A := centeredValueAlgorithm hR hL hh hhR c N
    (A.query t (policyHistory A.query f t) : Euclid d) =
      centeredBatchPoint (ballDomain (d := d) (R / 2) (by positivity)) c L h (policyValue A.query f) t := by
  dsimp only
  change batchPoint _ L h (historyValues (policyHistory _ f t)) t + (c : Euclid d) = _
  apply congrArg (fun z : Euclid d => z + c)
  apply batchPoint_congr
  intro i hi
  apply historyValues_policy
  have hmul : (t / (d + 1)) * (d + 1) ≤ t := by
    simpa only [Nat.mul_comm] using Nat.mul_div_le t (d + 1)
  omega

theorem centered_algorithm_result {d : ℕ} {R L h : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (hh : 0 ≤ h) (hhR : h ≤ R / 2) (c : QueryBall d (R / 2)) (N : ℕ) (f : Euclid d → ℝ) :
    (centeredValueAlgorithm hR hL hh hhR c N).result f =
      centeredRun (ballDomain (d := d) (R / 2) (by positivity)) c f L h N := by
  let A := centeredValueAlgorithm hR hL hh hhR c N
  let K := centeredDomain (ballDomain (d := d) (R / 2) (by positivity)) c
  let v := policyValue A.query f
  have hv (t : ℕ) : v t = f (batchPoint K L h v t + c) := by
    exact congrArg f (centered_algorithm_query hR hL hh hhR c N f t)
  have hrun := batchRun_eq_accelRun K L h v (fun x => f (x + c)) hv N
  have hhist : batchRun K L h (historyValues (policyHistory A.query f ((d + 1) * N))) N =
      batchRun K L h v N := by
    apply batchRun_congr
    intro t ht
    exact historyValues_policy A.query f t (by simpa only [Nat.mul_comm] using ht)
  change (batchRun K L h (historyValues (policyHistory A.query f ((d + 1) * N))) N).x + (c : Euclid d) = _
  rw [hhist, hrun]
  rfl

end
end ExactValue
