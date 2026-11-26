import MatchingBounds1005.CUPGCausality
import MatchingBounds1005.CUPGQueryIndices
import MatchingBounds1005.CUPGOrderedReplies
import MatchingBounds1005.CUPGPhase

/-! Exact replay of the actual physical first-order execution. All transcript
identities are derived from the causal closed-loop run. -/
noncomputable section
namespace MatchingBounds1005.CUPG

def actualPhaseData {d : ℕ} (f : Model.Space d → ℝ) (q α τ L ε : ℝ)
    (N : ℕ) (start : Model.Space d) : PhaseData d :=
  (start, arrayRun (fun t a => rawBodyQuery q α τ L ε N t (start, a)) f (9 * N + 2))

theorem actualPhaseData_response {d : ℕ} (f : Model.Space d → ℝ) (q α τ L ε : ℝ)
    (N : ℕ) (start : Model.Space d) (j : ℕ) (hj : j < 9 * N + 2) :
    (actualPhaseData f q α τ L ε N start).2 j =
      Model.oracle f (rawBodyQuery q α τ L ε N j (actualPhaseData f q α τ L ε N start)) :=
  arrayRun_response _ (rawBodyQuery_causal q α τ L ε N start) f _ j hj

theorem actualPhaseData_zero {d : ℕ} (f : Model.Space d → ℝ) (q α τ L ε : ℝ)
    (N : ℕ) (start : Model.Space d) :
    (actualPhaseData f q α τ L ε N start).2 0 = Model.oracle f start := by
  rw [actualPhaseData_response f q α τ L ε N start 0 (by omega), rawBodyQuery_zero]
  rfl

theorem rawState_succ {d : ℕ} (q α : ℝ) (p : PhaseData d) (n : ℕ) :
    rawState q α p (n + 1) = replyStep q α p.1 (rawState q α p n) (p.2 (3 * n + 2)) := rfl

theorem actualPhaseData_state {d : ℕ} {f : Model.Space d → ℝ} (hf : Differentiable ℝ f)
    (q α τ L ε : ℝ) (N : ℕ) (start : Model.Space d) (j : ℕ) (hj : j ≤ N) :
    stateOfReply (rawState q α (actualPhaseData f q α τ L ε N start) j) =
      estimateRun (regularized f α start) q α start j := by
  induction j with
  | zero =>
    simp only [rawState, replyRun, stateOfReply, estimateRun,
      actualPhaseData_zero f q α τ L ε N start, Model.oracle]
    simp [actualPhaseData, regularized]
  | succ j ih =>
    have hi := ih (by omega)
    have hp : rawState q α (actualPhaseData f q α τ L ε N start) j =
        replyOfState (estimateRun (regularized f α start) q α start j) := congrArg replyOfState hi
    have hr := actualPhaseData_response f q α τ L ε N start (3 * j + 2) (by omega)
    rw [rawBodyQuery_x q α τ L ε N j (by omega)] at hr
    have hx : rawX q α (actualPhaseData f q α τ L ε N start) j =
        query q (estimateRun (regularized f α start) q α start j) := congrArg (query q) hi
    rw [hx] at hr
    rw [rawState_succ, hp, hr]
    exact replyStep_correct hf q α start _

theorem actualPhaseData_y {d : ℕ} {f : Model.Space d → ℝ} (hf : Differentiable ℝ f)
    (q α τ L ε : ℝ) (N : ℕ) (start : Model.Space d) (j : ℕ) (hj : j ≤ N) :
    rawY q α (actualPhaseData f q α τ L ε N start) j =
      (estimateRun (regularized f α start) q α start j).point :=
  congrArg EstimateState.point (actualPhaseData_state hf q α τ L ε N start j hj)

theorem actualPhaseData_x {d : ℕ} {f : Model.Space d → ℝ} (hf : Differentiable ℝ f)
    (q α τ L ε : ℝ) (N : ℕ) (start : Model.Space d) (j : ℕ) (hj : j ≤ N) :
    rawX q α (actualPhaseData f q α τ L ε N start) j =
      query q (estimateRun (regularized f α start) q α start j) :=
  congrArg (query q) (actualPhaseData_state hf q α τ L ε N start j hj)

theorem actualPhaseData_yReply {d : ℕ} {f : Model.Space d → ℝ} (hf : Differentiable ℝ f)
    (q α τ L ε : ℝ) (N : ℕ) (start : Model.Space d) (j : ℕ) (hj : j ≤ N) :
    rawYReply (actualPhaseData f q α τ L ε N start) j =
      Model.oracle f (estimateRun (regularized f α start) q α start j).point := by
  cases j with
  | zero => exact actualPhaseData_zero f q α τ L ε N start
  | succ j =>
    have hr := actualPhaseData_response f q α τ L ε N start (3 * (j + 1)) (by omega)
    rw [rawBodyQuery_y_succ q α τ L ε N j (by omega), actualPhaseData_y hf q α τ L ε N start (j + 1) hj] at hr
    simpa only [rawYReply, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte] using hr

theorem actualPhaseData_proxY {d : ℕ} {f : Model.Space d → ℝ} (hf : Differentiable ℝ f)
    (q α τ L ε : ℝ) (N : ℕ) (start : Model.Space d) (j : ℕ) (hj : j ≤ N) :
    rawProxY q α (actualPhaseData f q α τ L ε N start) j =
      Model.oracle (regularized f α start) (estimateRun (regularized f α start) q α start j).point := by
  unfold rawProxY
  rw [actualPhaseData_y hf q α τ L ε N start j hj, actualPhaseData_yReply hf q α τ L ε N start j hj]
  exact proximalReply_correct hf α start _

theorem actualPhaseData_z {d : ℕ} {f : Model.Space d → ℝ} (hf : Differentiable ℝ f)
    (q α τ L ε : ℝ) (N : ℕ) (start : Model.Space d) (j : ℕ) (hj : j ≤ N) :
    rawZ q α (actualPhaseData f q α τ L ε N start) j =
      descentPoint (regularized f α start) q α (estimateRun (regularized f α start) q α start j).point := by
  unfold rawZ
  rw [actualPhaseData_y hf q α τ L ε N start j hj, actualPhaseData_proxY hf q α τ L ε N start j hj]
  rfl

theorem actualPhaseData_zReply {d : ℕ} {f : Model.Space d → ℝ} (hf : Differentiable ℝ f)
    (q α τ L ε : ℝ) (N : ℕ) (start : Model.Space d) (j : ℕ) (hj : j ≤ N) :
    rawZReply (actualPhaseData f q α τ L ε N start) j = Model.oracle f
      (descentPoint (regularized f α start) q α (estimateRun (regularized f α start) q α start j).point) := by
  cases j with
  | zero =>
    have hr := actualPhaseData_response f q α τ L ε N start 1 (by omega)
    rw [rawBodyQuery_one, actualPhaseData_z hf q α τ L ε N start 0 (by omega)] at hr
    exact hr
  | succ j =>
    have hr := actualPhaseData_response f q α τ L ε N start (3 * (j + 1) + 1) (by omega)
    rw [rawBodyQuery_z_succ q α τ L ε N j (by omega), actualPhaseData_z hf q α τ L ε N start (j + 1) hj] at hr
    simpa only [rawZReply, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte] using hr

theorem actualPhaseData_gap {d : ℕ} {f : Model.Space d → ℝ} (hf : Differentiable ℝ f)
    (q α τ L ε : ℝ) (N : ℕ) (start : Model.Space d) (j : ℕ) (hj : j ≤ N) :
    rawGap q α (actualPhaseData f q α τ L ε N start) j =
      progressGap (regularized f α start) α start
        (descentPoint (regularized f α start) q α (estimateRun (regularized f α start) q α start j).point) := by
  unfold rawGap
  rw [actualPhaseData_zero, actualPhaseData_z hf q α τ L ε N start j hj,
    actualPhaseData_zReply hf q α τ L ε N start j hj]
  change f start - (proximalReply α start _ (Model.oracle f _)).1 + α / 2 * ‖_ - start‖ ^ 2 = _
  rw [proximalReply_correct hf]
  simp [Model.oracle, progressGap, regularized]

theorem actualPhaseData_pass {d : ℕ} {f : Model.Space d → ℝ} (hf : Differentiable ℝ f)
    (q α τ L ε : ℝ) (N : ℕ) (start : Model.Space d) (j : ℕ) (hj : j ≤ N) :
    RawPass q α L (actualPhaseData f q α τ L ε N start) j ↔
      ProgressPass (regularized f α start) q α L start j := by
  unfold RawPass ProgressPass
  rw [actualPhaseData_proxY hf q α τ L ε N start j hj, actualPhaseData_zero,
    actualPhaseData_gap hf q α τ L ε N start j hj]
  simp only [Model.oracle, regularized, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, add_zero]

theorem actualPhaseData_stopped {d : ℕ} {f : Model.Space d → ℝ} (hf : Differentiable ℝ f)
    (q α τ L ε : ℝ) (N : ℕ) (start : Model.Space d) (j : ℕ) (hj : j ≤ N) :
    RawStopped q α L ε (actualPhaseData f q α τ L ε N start) j ↔
      Stopped (regularized f α start) q α L (ε / 10) start j := by
  unfold RawStopped Stopped
  rw [actualPhaseData_pass hf q α τ L ε N start j hj,
    actualPhaseData_proxY hf q α τ L ε N start j hj]
  rfl

theorem actualPhaseData_stop {d : ℕ} {f : Model.Space d → ℝ} (hf : Differentiable ℝ f)
    (q α τ L ε : ℝ) (N : ℕ) (start : Model.Space d) :
    rawStop q α L ε N (actualPhaseData f q α τ L ε N start) =
      stoppedIndex f q α L ε start N := by
  classical
  apply firstIndex_congr
  intro j hj
  exact actualPhaseData_stopped hf q α τ L ε N start j hj

theorem actualPhaseData_witness {d : ℕ} {f : Model.Space d → ℝ} (hf : Differentiable ℝ f)
    (q α τ L ε : ℝ) (N : ℕ) (start : Model.Space d) (j : ℕ) (hj : j ≤ N) :
    rawWitness q α (actualPhaseData f q α τ L ε N start) j =
      witnessPoint (regularized f α start) q α start j := by
  unfold rawWitness witnessPoint
  rw [actualPhaseData_proxY hf q α τ L ε N start j hj, actualPhaseData_zero,
    actualPhaseData_z hf q α τ L ε N start j hj]
  simp only [Model.oracle, regularized, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, add_zero]
  rfl

theorem actualPhaseData_witnessRecord {d : ℕ} {f : Model.Space d → ℝ} (hf : Differentiable ℝ f)
    (q α τ L ε : ℝ) (N : ℕ) (start : Model.Space d) (j : ℕ) (hj : j ≤ N) :
    rawWitnessRecord q α (actualPhaseData f q α τ L ε N start) j =
      (witnessPoint (regularized f α start) q α start j,
        f (witnessPoint (regularized f α start) q α start j)) := by
  unfold rawWitnessRecord witnessPoint
  rw [actualPhaseData_proxY hf q α τ L ε N start j hj, actualPhaseData_zero,
    actualPhaseData_z hf q α τ L ε N start j hj, actualPhaseData_zReply hf q α τ L ε N start j hj]
  simp only [Model.oracle, regularized, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, add_zero]
  split_ifs <;> rfl

theorem actualPhaseData_record {d : ℕ} (f : Model.Space d → ℝ) (q α τ L ε : ℝ)
    (N : ℕ) (start : Model.Space d) (j : ℕ) (hj : j < 9 * N + 2) :
    rawRecord q α τ L ε N j (actualPhaseData f q α τ L ε N start) =
      (rawBodyQuery q α τ L ε N j (actualPhaseData f q α τ L ε N start),
        f (rawBodyQuery q α τ L ε N j (actualPhaseData f q α τ L ε N start))) := by
  unfold rawRecord
  rw [actualPhaseData_response f q α τ L ε N start j hj]
  rfl

theorem actualPhaseData_candidateMaps {d : ℕ} {f : Model.Space d → ℝ} (hf : Differentiable ℝ f)
    (q α τ L ε : ℝ) (N : ℕ) (start : Model.Space d) :
    (rawCandidateMaps q α τ L ε N).map (fun F => F (actualPhaseData f q α τ L ε N start)) =
      (phasePoints f q α τ start N (stoppedIndex f q α L ε start N)).map (fun x => (x, f x)) := by
  classical
  let p := actualPhaseData f q α τ L ε N start
  let n := stoppedIndex f q α L ε start N
  let y := fun j => (estimateRun (regularized f α start) q α start j).point
  let x := fun j => query q (estimateRun (regularized f α start) q α start j)
  let w := witnessPoint (regularized f α start) q α start n
  have hn : n ≤ N := firstIndex_le _ N
  have hs : rawStop q α L ε N p = n := actualPhaseData_stop hf q α τ L ε N start
  have hw : rawWitness q α p (rawStop q α L ε N p) = w := by
    rw [hs]
    exact actualPhaseData_witness hf q α τ L ε N start n hn
  have hwr : rawWitnessRecord q α p (rawStop q α L ε N p) = (w, f w) := by
    rw [hs]
    exact actualPhaseData_witnessRecord hf q α τ L ε N start n hn
  have hrecords (I : ℕ → ℕ) (G : ℕ → Model.Space d) (k : ℕ)
      (hi : ∀ j < k, I j < 9 * N + 2)
      (hg : ∀ j < k, rawBodyQuery q α τ L ε N (I j) p = G j) :
      (List.range k).map (fun j => rawRecord q α τ L ε N (I j) p) =
        (List.range k).map (fun j => (G j, f (G j))) := by
    apply List.map_congr_left
    intro j hj
    have hjk := List.mem_range.mp hj
    rw [actualPhaseData_record f q α τ L ε N start (I j) (hi j hjk), hg j hjk]
  have hY := hrecords (fun j => 3 * j) y (N + 1) (by intro j hj; dsimp only; omega) (by
    intro j hj
    rw [rawBodyQuery_y q α τ L ε N j (by omega)]
    exact actualPhaseData_y hf q α τ L ε N start j (by omega))
  have hNear := hrecords (fun j => 3 * N + 2 + 2 * j) (fun j => guardNear (y (j + 1)) (y j)) N
    (by intro j hj; dsimp only; omega) (by
      intro j hj
      rw [rawBodyQuery_near q α τ L ε N j hj,
        actualPhaseData_y hf q α τ L ε N start (j + 1) (by omega),
        actualPhaseData_y hf q α τ L ε N start j (by omega)])
  have hFar := hrecords (fun j => 3 * N + 3 + 2 * j) (fun j => guardFar (y (j + 1)) (y j)) N
    (by intro j hj; dsimp only; omega) (by
      intro j hj
      rw [rawBodyQuery_far q α τ L ε N j hj,
        actualPhaseData_y hf q α τ L ε N start (j + 1) (by omega),
        actualPhaseData_y hf q α τ L ε N start j (by omega)])
  have hMinusY := hrecords (fun j => 5 * N + 2 + 4 * j) (fun j => escapeMinus (y j) (x j) (16 * τ)) N
    (by intro j hj; dsimp only; omega) (by
      intro j hj
      rw [rawBodyQuery_minusY q α τ L ε N j hj,
        actualPhaseData_y hf q α τ L ε N start j (by omega),
        actualPhaseData_x hf q α τ L ε N start j (by omega)])
  have hPlusY := hrecords (fun j => 5 * N + 3 + 4 * j) (fun j => escapePlus (y j) (x j) (16 * τ)) N
    (by intro j hj; dsimp only; omega) (by
      intro j hj
      rw [rawBodyQuery_plusY q α τ L ε N j hj,
        actualPhaseData_y hf q α τ L ε N start j (by omega),
        actualPhaseData_x hf q α τ L ε N start j (by omega)])
  have hMinusW := hrecords (fun j => 5 * N + 4 + 4 * j) (fun j => escapeMinus w (x j) (16 * τ)) N
    (by intro j hj; dsimp only; omega) (by
      intro j hj
      rw [rawBodyQuery_minusW q α τ L ε N j hj, hw,
        actualPhaseData_x hf q α τ L ε N start j (by omega)])
  have hPlusW := hrecords (fun j => 5 * N + 5 + 4 * j) (fun j => escapePlus w (x j) (16 * τ)) N
    (by intro j hj; dsimp only; omega) (by
      intro j hj
      rw [rawBodyQuery_plusW q α τ L ε N j hj, hw,
        actualPhaseData_x hf q α τ L ε N start j (by omega)])
  change (rawCandidateMaps q α τ L ε N).map (fun F => F p) =
    (phasePoints f q α τ start N n).map (fun x => (x, f x))
  dsimp only at hY hNear hFar hMinusY hPlusY hMinusW hPlusW
  simp only [rawCandidateMaps, phasePoints, List.map_append, List.map_cons, List.map_nil,
    List.map_map, Function.comp_def]
  rw [hwr, hY, hNear, hFar, hMinusY, hPlusY, hMinusW, hPlusW]

theorem actualPhaseData_candidate {d : ℕ} {f : Model.Space d → ℝ} (hf : Differentiable ℝ f)
    (q α τ L ε : ℝ) (N : ℕ) (start : Model.Space d) :
    rawOrderedCandidate q α τ L ε N (actualPhaseData f q α τ L ε N start) =
      phasePoint f q α τ L ε start N := by
  classical
  let n := stoppedIndex f q α L ε start N
  have hn : n ≤ N := firstIndex_le _ N
  unfold rawOrderedCandidate phasePoint
  rw [actualPhaseData_stop hf q α τ L ε N start,
    actualPhaseData_pass hf q α τ L ε N start n hn,
    actualPhaseData_y hf q α τ L ε N start n hn]
  dsimp only
  split_ifs
  · rfl
  · rw [actualPhaseData_candidateMaps hf q α τ L ε N start]
    change (bestReplyList (start, ((actualPhaseData f q α τ L ε N start).2 0).1)
      ((phasePoints f q α τ start N n).map (fun x => (x, f x)))).1 = phaseBest f q α τ start N n
    rw [actualPhaseData_zero]
    exact congrArg Prod.fst (bestReplyList_correct f start (phasePoints f q α τ start N n))

end MatchingBounds1005.CUPG
