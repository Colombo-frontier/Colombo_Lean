import ExactValue.CenteredBatch

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace ExactValue
noncomputable section

def phaseValues (v : ℕ → ℝ) (offset : ℕ) : ℕ → ℝ := fun i => v (offset + i)

theorem phaseValues_continuous (offset : ℕ) :
    Continuous (fun v : ℕ → ℝ => phaseValues v offset) := by
  apply continuous_pi
  intro i
  exact continuous_apply (offset + i)

def restartOrigin {d : ℕ} (K : ClosedConvexDomain d) (L : ℝ) (steps : ℕ → ℝ)
    (N : ℕ) (v : ℕ → ℝ) : ℕ → Euclid d
  | 0 => 0
  | s + 1 => centeredBatchOutput K (restartOrigin K L steps N v s) L (steps s)
      (phaseValues v (s * ((d + 1) * N))) N

def restartPoint {d : ℕ} (K : ClosedConvexDomain d) (L : ℝ) (steps : ℕ → ℝ)
    (N : ℕ) (v : ℕ → ℝ) (n : ℕ) : Euclid d :=
  let P := (d + 1) * N
  let s := n / P
  centeredBatchPoint K (restartOrigin K L steps N v s) L (steps s)
    (phaseValues v (s * P)) (n % P)

theorem restartOrigin_mem {d : ℕ} (K : ClosedConvexDomain d) (hz : (0 : Euclid d) ∈ K.carrier)
    {L : ℝ} (hL : 0 < L) (steps : ℕ → ℝ) (N : ℕ) (v : ℕ → ℝ) (s : ℕ) :
    restartOrigin K L steps N v s ∈ K.carrier := by
  induction s with
  | zero => exact hz
  | succ s ih => exact centeredBatchOutput_mem K ih hL _ _ N

theorem restartOrigin_continuous {d : ℕ} (K : ClosedConvexDomain d) (L : ℝ)
    (steps : ℕ → ℝ) (N s : ℕ) : Continuous (fun v : ℕ → ℝ => restartOrigin K L steps N v s) := by
  induction s with
  | zero => exact continuous_const
  | succ s ih =>
    exact (centeredBatchOutput_continuous K L (steps s) N).comp
      (f := fun v : ℕ → ℝ => (restartOrigin K L steps N v s, phaseValues v (s * ((d + 1) * N))))
      (ih.prodMk (phaseValues_continuous (s * ((d + 1) * N))))

theorem restartPoint_continuous {d : ℕ} (K : ClosedConvexDomain d) (L : ℝ)
    (steps : ℕ → ℝ) (N n : ℕ) : Continuous (fun v : ℕ → ℝ => restartPoint K L steps N v n) := by
  exact (centeredBatchPoint_continuous K L (steps (n / ((d + 1) * N))) (n % ((d + 1) * N))).comp
    (f := fun v : ℕ → ℝ => (restartOrigin K L steps N v (n / ((d + 1) * N)),
      phaseValues v ((n / ((d + 1) * N)) * ((d + 1) * N))))
    ((restartOrigin_continuous K L steps N (n / ((d + 1) * N))).prodMk
      (phaseValues_continuous ((n / ((d + 1) * N)) * ((d + 1) * N))))

theorem restartOrigin_congr {d : ℕ} (K : ClosedConvexDomain d) (L : ℝ) (steps : ℕ → ℝ)
    (N : ℕ) (v w : ℕ → ℝ) (s : ℕ)
    (hv : ∀ i, i < s * ((d + 1) * N) → v i = w i) :
    restartOrigin K L steps N v s = restartOrigin K L steps N w s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have hc := ih (fun i hi => hv i (hi.trans_le (Nat.mul_le_mul_right _ (Nat.le_succ s))))
    simp only [restartOrigin]
    rw [hc]
    unfold centeredBatchOutput
    apply congrArg (fun st : AccelState d => st.x + restartOrigin K L steps N w s)
    apply batchRun_congr
    intro i hi
    apply hv
    have hip : i < (d + 1) * N := by simpa only [Nat.mul_comm] using hi
    change s * ((d + 1) * N) + i < (s + 1) * ((d + 1) * N)
    exact (Nat.add_lt_add_left hip (s * ((d + 1) * N))).trans_eq (by ring)

theorem restartPoint_congr {d : ℕ} (K : ClosedConvexDomain d) (L : ℝ) (steps : ℕ → ℝ)
    (N : ℕ) (v w : ℕ → ℝ) (n : ℕ) (hv : ∀ i, i < n → v i = w i) :
    restartPoint K L steps N v n = restartPoint K L steps N w n := by
  let P := (d + 1) * N
  have hprefix : (n / P) * P ≤ n := Nat.div_mul_le_self n P
  have hc := restartOrigin_congr K L steps N v w (n / P)
    (fun i hi => hv i (hi.trans_le hprefix))
  unfold restartPoint
  dsimp only
  rw [hc]
  unfold centeredBatchPoint
  apply congrArg (fun z : Euclid d => z + restartOrigin K L steps N w (n / P))
  apply batchPoint_congr
  intro i hi
  change i < ((n % P) / (d + 1)) * (d + 1) at hi
  apply hv
  have hpartial : ((n % P) / (d + 1)) * (d + 1) ≤ n % P := Nat.div_mul_le_self _ _
  have hdecomp : (n / P) * P + n % P = n := Nat.div_add_mod' n P
  change (n / P) * P + i < n
  omega

theorem restartPoint_norm {d : ℕ} {R L : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (steps : ℕ → ℝ) (hsteps : ∀ s, 0 ≤ steps s ∧ steps s ≤ R / 2)
    (N : ℕ) (v : ℕ → ℝ) (n : ℕ) :
    ‖restartPoint (ballDomain (d := d) (R / 2) (by positivity)) L steps N v n‖ ≤ R := by
  let K := ballDomain (d := d) (R / 2) (by positivity)
  have hz : (0 : Euclid d) ∈ K.carrier := by simp [K, ballDomain]; positivity
  have hc : ‖restartOrigin K L steps N v (n / ((d + 1) * N))‖ ≤ R / 2 := by
    simpa [K, ballDomain] using restartOrigin_mem K hz hL steps N v (n / ((d + 1) * N))
  exact centeredBatchPoint_norm hR hc hL (hsteps _).1 (hsteps _).2 _ _

/-- A complete sequence of phases, with query and terminal maps Borel on every history. -/
def restartedValueAlgorithm {d : ℕ} {R L : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (steps : ℕ → ℝ) (hsteps : ∀ s, 0 ≤ steps s ∧ steps s ≤ R / 2) (N S : ℕ) :
    ValueAlgorithm d R (((d + 1) * N) * S) where
  query n hist := ⟨restartPoint (ballDomain (R / 2) (by positivity)) L steps N (historyValues hist) n,
    restartPoint_norm hR hL steps hsteps N _ n⟩
  output hist := ⟨restartOrigin (ballDomain (R / 2) (by positivity)) L steps N (historyValues hist) S, by
    have hz : (0 : Euclid d) ∈ (ballDomain (R / 2) (by positivity)).carrier := by
      simp [ballDomain]; positivity
    have hn : ‖restartOrigin (ballDomain (d := d) (R / 2) (by positivity)) L steps N (historyValues hist) S‖ ≤ R / 2 := by
      simpa [ballDomain] using restartOrigin_mem (ballDomain (d := d) (R / 2) (by positivity)) hz hL steps N
        (historyValues hist) S
    linarith⟩
  query_borel := by
    intro n
    apply Continuous.borel_measurable
    apply Continuous.subtype_mk
    exact (restartPoint_continuous (ballDomain (d := d) (R / 2) (by positivity)) L steps N n).comp
      (f := fun hist : QueryHistory d R n => historyValues hist)
      (historyValues_continuous (d := d) (n := n) R)
  output_borel := by
    apply Continuous.borel_measurable
    apply Continuous.subtype_mk
    exact (restartOrigin_continuous (ballDomain (d := d) (R / 2) (by positivity)) L steps N S).comp
      (f := fun hist : QueryHistory d R (((d + 1) * N) * S) => historyValues hist)
      (historyValues_continuous (d := d) (n := ((d + 1) * N) * S) R)

theorem restarted_algorithm_query {d : ℕ} {R L : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (steps : ℕ → ℝ) (hsteps : ∀ s, 0 ≤ steps s ∧ steps s ≤ R / 2) (N S : ℕ)
    (f : Euclid d → ℝ) (n : ℕ) :
    let A := restartedValueAlgorithm (d := d) hR hL steps hsteps N S
    (A.query n (policyHistory A.query f n) : Euclid d) =
      restartPoint (ballDomain (R / 2) (by positivity)) L steps N (policyValue A.query f) n := by
  dsimp only
  apply restartPoint_congr
  intro i hi
  exact historyValues_policy _ f i hi

theorem restarted_algorithm_result {d : ℕ} {R L : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (steps : ℕ → ℝ) (hsteps : ∀ s, 0 ≤ steps s ∧ steps s ≤ R / 2) (N S : ℕ)
    (f : Euclid d → ℝ) :
    let A := restartedValueAlgorithm (d := d) hR hL steps hsteps N S
    A.result f = restartOrigin (ballDomain (R / 2) (by positivity)) L steps N (policyValue A.query f) S := by
  dsimp only
  apply restartOrigin_congr
  intro i hi
  exact historyValues_policy _ f i (by simpa only [Nat.mul_comm] using hi)

theorem batchRun_eq_accelRun_bounded {d : ℕ} (K : ClosedConvexDomain d) (L h : ℝ)
    (v : ℕ → ℝ) (f : Euclid d → ℝ) (n : ℕ)
    (hv : ∀ t, t < n * (d + 1) → v t = f (batchPoint K L h v t)) :
    batchRun K L h v n = accelRun K f (finiteGradient f h) L n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp := ih (fun t ht => hv t (ht.trans_le (Nat.mul_le_mul_right _ (Nat.le_succ n))))
    have hbase := hv (n * (d + 1)) (by simpa only [Nat.add_zero] using batchIndex_lt n d 0 (Nat.succ_pos d))
    rw [batchPoint_at_base] at hbase
    have hgrad : batchGradient d h v n = finiteGradient f h (batchY K L h v n) := by
      ext i
      change (v (n * (d + 1) + i.val + 1) - v (n * (d + 1))) / h = _
      rw [hv _ (by simpa only [Nat.add_assoc] using batchIndex_lt n d (i.val + 1) (by omega)),
        hbase, batchPoint_at_coordinate]
      rfl
    simp only [batchRun, accelRun, batchNext, accelNext, hgrad, hbase, batchY]
    rw [hp]

theorem restartPoint_in_phase {d : ℕ} (K : ClosedConvexDomain d) (L : ℝ) (steps : ℕ → ℝ)
    (N : ℕ) (v : ℕ → ℝ) (s t : ℕ) (ht : t < (d + 1) * N) :
    restartPoint K L steps N v (s * ((d + 1) * N) + t) =
      centeredBatchPoint K (restartOrigin K L steps N v s) L (steps s)
        (phaseValues v (s * ((d + 1) * N))) t := by
  have hP : 0 < (d + 1) * N := lt_of_le_of_lt (Nat.zero_le t) ht
  have hdiv : (s * ((d + 1) * N) + t) / ((d + 1) * N) = s := by
    rw [Nat.mul_comm s ((d + 1) * N), Nat.mul_add_div hP, Nat.div_eq_of_lt ht, Nat.add_zero]
  simp [restartPoint, hdiv, Nat.mod_eq_of_lt ht]

/-- The actual scalar-value interaction realizes exactly one analytic accelerated phase. -/
theorem restartOrigin_oracle_step {d : ℕ} (K : ClosedConvexDomain d) (L : ℝ) (steps : ℕ → ℝ)
    (N : ℕ) (v : ℕ → ℝ) (f : Euclid d → ℝ)
    (hv : ∀ t, v t = f (restartPoint K L steps N v t)) (s : ℕ) :
    restartOrigin K L steps N v (s + 1) =
      centeredRun K (restartOrigin K L steps N v s) f L (steps s) N := by
  let c := restartOrigin K L steps N v s
  have hlocal (t : ℕ) (ht : t < N * (d + 1)) :
      phaseValues v (s * ((d + 1) * N)) t =
        f (batchPoint (centeredDomain K c) L (steps s) (phaseValues v (s * ((d + 1) * N))) t + c) := by
    have h := hv (s * ((d + 1) * N) + t)
    rw [restartPoint_in_phase K L steps N v s t (by simpa only [Nat.mul_comm] using ht)] at h
    exact h
  have hr := batchRun_eq_accelRun_bounded (centeredDomain K c) L (steps s)
    (phaseValues v (s * ((d + 1) * N))) (fun x => f (x + c)) N hlocal
  change (batchRun (centeredDomain K c) L (steps s) (phaseValues v (s * ((d + 1) * N))) N).x + c = _
  rw [hr]
  rfl

end
end ExactValue
