import MatchingBounds1005.CUPGPhaseReplies
import MatchingBounds1005.CUPGOracleArray

/-! Exact finite response dependencies of the accelerated phase. -/
noncomputable section
namespace MatchingBounds1005.CUPG

theorem firstIndex_congr (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (N : ℕ) (hPQ : ∀ j ≤ N, P j ↔ Q j) : firstIndex P N = firstIndex Q N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hi := ih (fun j hj => hPQ j (by omega))
    simp only [firstIndex, hi]
    simp only [hPQ (firstIndex Q N) (by have hh := firstIndex_le Q N; omega)]

theorem replyRun_congr {d : ℕ} (q α : ℝ) (start : Model.Space d) (fa fb : ℝ)
    (a b : ℕ → Model.Response d) (n : ℕ) (hf : fa = fb)
    (hab : ∀ j < n, a j = b j) : replyRun q α start fa a n = replyRun q α start fb b n := by
  induction n with
  | zero => simp only [replyRun, hf]
  | succ n ih =>
    rw [replyRun, replyRun, ih (fun j hj => hab j (by omega)), hab n (by omega)]

theorem rawState_congr {d : ℕ} (q α : ℝ) (start : Model.Space d)
    (a b : ℕ → Model.Response d) (n : ℕ) (hzero : a 0 = b 0)
    (hx : ∀ j < n, a (3 * j + 2) = b (3 * j + 2)) :
    rawState q α (start, a) n = rawState q α (start, b) n :=
  replyRun_congr q α start _ _ _ _ n (congrArg Prod.fst hzero) hx

theorem rawY_congr {d : ℕ} (q α : ℝ) (start : Model.Space d)
    (a b : ℕ → Model.Response d) (n : ℕ) (hzero : a 0 = b 0)
    (hx : ∀ j < n, a (3 * j + 2) = b (3 * j + 2)) :
    rawY q α (start, a) n = rawY q α (start, b) n :=
  congrArg Prod.fst (rawState_congr q α start a b n hzero hx)

theorem rawX_congr {d : ℕ} (q α : ℝ) (start : Model.Space d)
    (a b : ℕ → Model.Response d) (n : ℕ) (hzero : a 0 = b 0)
    (hx : ∀ j < n, a (3 * j + 2) = b (3 * j + 2)) :
    rawX q α (start, a) n = rawX q α (start, b) n :=
  congrArg (replyQuery q) (rawState_congr q α start a b n hzero hx)

theorem rawZ_congr {d : ℕ} (q α : ℝ) (start : Model.Space d)
    (a b : ℕ → Model.Response d) (n : ℕ)
    (hab : ∀ j < 3 * n + 1, a j = b j) :
    rawZ q α (start, a) n = rawZ q α (start, b) n := by
  have hy := rawY_congr q α start a b n (hab 0 (by omega)) (fun j hj => hab _ (by omega))
  have hyr : rawYReply (start, a) n = rawYReply (start, b) n := by
    apply hab
    split_ifs <;> omega
  simp only [rawZ, rawProxY, Prod.fst, hy, hyr]

theorem rawPass_congr {d : ℕ} (q α L : ℝ) (start : Model.Space d)
    (a b : ℕ → Model.Response d) (n : ℕ)
    (hab : ∀ j < 3 * n + 2, a j = b j) :
    RawPass q α L (start, a) n ↔ RawPass q α L (start, b) n := by
  have hy := rawY_congr q α start a b n (hab 0 (by omega)) (fun j hj => hab _ (by omega))
  have hz := rawZ_congr q α start a b n (fun j hj => hab j (by omega))
  have hyr : rawYReply (start, a) n = rawYReply (start, b) n := by
    apply hab
    split_ifs <;> omega
  have hzr : rawZReply (start, a) n = rawZReply (start, b) n := by
    apply hab
    split_ifs <;> omega
  simp only [RawPass, rawGap, rawProxY, Prod.fst, Prod.snd, hy, hz, hyr, hzr, hab 0 (by omega)]

theorem rawStopped_congr {d : ℕ} (q α L ε : ℝ) (start : Model.Space d)
    (a b : ℕ → Model.Response d) (n : ℕ)
    (hab : ∀ j < 3 * n + 2, a j = b j) :
    RawStopped q α L ε (start, a) n ↔ RawStopped q α L ε (start, b) n := by
  have hp := rawPass_congr q α L start a b n hab
  have hy := rawY_congr q α start a b n (hab 0 (by omega)) (fun j hj => hab _ (by omega))
  have hyr : rawYReply (start, a) n = rawYReply (start, b) n := by
    apply hab
    split_ifs <;> omega
  simp only [RawStopped, rawProxY, Prod.fst, hp, hy, hyr]

theorem rawStop_congr {d : ℕ} (q α L ε : ℝ) (start : Model.Space d)
    (a b : ℕ → Model.Response d) (N : ℕ)
    (hab : ∀ j < 3 * N + 2, a j = b j) :
    rawStop q α L ε N (start, a) = rawStop q α L ε N (start, b) := by
  classical
  apply firstIndex_congr
  intro j hj
  exact rawStopped_congr q α L ε start a b j (fun i hi => hab i (by omega))

theorem rawWitness_congr {d : ℕ} (q α : ℝ) (start : Model.Space d)
    (a b : ℕ → Model.Response d) (n : ℕ)
    (hab : ∀ j < 3 * n + 1, a j = b j) :
    rawWitness q α (start, a) n = rawWitness q α (start, b) n := by
  have hy := rawY_congr q α start a b n (hab 0 (by omega)) (fun j hj => hab _ (by omega))
  have hz := rawZ_congr q α start a b n hab
  have hyr : rawYReply (start, a) n = rawYReply (start, b) n := by
    apply hab
    split_ifs <;> omega
  simp only [rawWitness, rawProxY, Prod.fst, Prod.snd, hy, hz, hyr, hab 0 (by omega)]

theorem rawWitness_stop_congr {d : ℕ} (q α L ε : ℝ) (start : Model.Space d)
    (a b : ℕ → Model.Response d) (N : ℕ)
    (hab : ∀ j < 3 * N + 2, a j = b j) :
    rawWitness q α (start, a) (rawStop q α L ε N (start, a)) =
      rawWitness q α (start, b) (rawStop q α L ε N (start, b)) := by
  classical
  rw [rawStop_congr q α L ε start a b N hab]
  apply rawWitness_congr
  have hn : rawStop q α L ε N (start, b) ≤ N := firstIndex_le _ N
  intro j hj
  exact hab j (by omega)

theorem rawBodyQuery_causal {d : ℕ} (q α τ L ε : ℝ) (N : ℕ) (start : Model.Space d) :
    ArrayCausal (fun t a => rawBodyQuery q α τ L ε N t (start, a)) := by
  intro t a b hab
  change rawBodyQuery q α τ L ε N t (start, a) = rawBodyQuery q α τ L ε N t (start, b)
  by_cases ht : t = 0
  · subst t; simp [rawBodyQuery]
  have hzero : a 0 = b 0 := hab 0 (by omega)
  have hY (n : ℕ) (hn : 3 * n ≤ t) : rawY q α (start, a) n = rawY q α (start, b) n :=
    rawY_congr q α start a b n hzero (fun j hj => hab _ (by omega))
  have hX (n : ℕ) (hn : 3 * n + 2 ≤ t) : rawX q α (start, a) n = rawX q α (start, b) n :=
    rawX_congr q α start a b n hzero (fun j hj => hab _ (by omega))
  have hZ (n : ℕ) (hn : 3 * n + 1 ≤ t) : rawZ q α (start, a) n = rawZ q α (start, b) n :=
    rawZ_congr q α start a b n (fun j hj => hab _ (by omega))
  have hW (hn : 3 * N + 2 ≤ t) :
      rawWitness q α (start, a) (rawStop q α L ε N (start, a)) =
        rawWitness q α (start, b) (rawStop q α L ε N (start, b)) :=
    rawWitness_stop_congr q α L ε start a b N (fun j hj => hab j (by omega))
  unfold rawBodyQuery
  split_ifs
  all_goals try rfl
  all_goals try first | (apply hY; omega) | (apply hX; omega) | (apply hZ; omega)
  all_goals first
    | apply congrArg₂ guardNear
    | apply congrArg₂ guardFar
    | apply congrArg₂ (fun u v => escapeMinus u v (16 * τ))
    | apply congrArg₂ (fun u v => escapePlus u v (16 * τ))
  all_goals first | (apply hY; omega) | (apply hX; omega) | (apply hW; omega)

theorem indexedBest_congr {E : Type*} (a b : E × ℝ) (r s : ℕ → E × ℝ)
    (N : ℕ) (hab : a = b) (hrs : ∀ j < N, r j = s j) :
    indexedBest a r N = indexedBest b s N := by
  induction N with
  | zero => exact hab
  | succ N ih => rw [indexedBest, indexedBest, ih (fun j hj => hrs j (by omega)), hrs N (by omega)]

theorem rawCandidate_congr {d : ℕ} (q α τ L ε : ℝ) (N : ℕ) (start : Model.Space d)
    (a b : ℕ → Model.Response d) (hab : ∀ j < 9 * N + 2, a j = b j) :
    rawCandidate q α τ L ε N (start, a) = rawCandidate q α τ L ε N (start, b) := by
  classical
  have hn : rawStop q α L ε N (start, b) ≤ N := firstIndex_le _ N
  have hs := rawStop_congr q α L ε start a b N (fun j hj => hab j (by omega))
  have hp := rawPass_congr q α L start a b (rawStop q α L ε N (start, b))
    (fun j hj => hab j (by omega))
  have hy := rawY_congr q α start a b (rawStop q α L ε N (start, b))
    (hab 0 (by omega)) (fun j hj => hab _ (by omega))
  unfold rawCandidate
  rw [hs, hp, hy]
  split_ifs
  · rfl
  · apply congrArg Prod.fst
    apply indexedBest_congr
    · simp only [Prod.fst, Prod.snd, hab 0 (by omega)]
    · intro j hj
      apply Prod.ext
      · exact rawBodyQuery_causal q α τ L ε N start j a b (fun i hi => hab i (by omega))
      · exact congrArg Prod.fst (hab j hj)

theorem rawPhaseQuery_causal {d : ℕ} (q α τ L ε : ℝ) (N : ℕ) (start : Model.Space d) :
    ArrayCausal (fun t a => rawPhaseQuery q α τ L ε N t (start, a)) := by
  intro t a b hab
  change rawPhaseQuery q α τ L ε N t (start, a) = rawPhaseQuery q α τ L ε N t (start, b)
  unfold rawPhaseQuery
  split_ifs with ht
  · exact rawBodyQuery_causal q α τ L ε N start t a b hab
  · exact rawCandidate_congr q α τ L ε N start a b (fun j hj => hab j (by omega))

end MatchingBounds1005.CUPG
