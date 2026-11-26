import Mathlib
import PaperAudit.Frontier04

open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000


section
-- Source component: FirstActivationEarlyCount.lean

namespace FangqingFirstActivationEarlyCount

open MeasureTheory OriginalPrefixOracleReplay OriginalTwoGroupPrefixExecution
  FangqingStoppedTwoGroupReplay

set_option maxHeartbeats 3500000

variable {Seed Side H W Q A : Type*} {m : ℕ} [Zero H] [Zero W] [Zero A]

def decisionAt (query : OriginalTwoGroupPrefixExecution.Query Seed A Q) (dec : Activation Side A Q)
    (reply : Reply Seed Side H W A Q m) (seed : Seed) (side : Side)
    (handle : Fin 1 → H) (tail : Fin m → W) (n : ℕ) : Bool :=
  let st := run query dec reply n seed side handle tail
  dec n side st (query n seed st.2.2)

def firstActivationUntil (query : OriginalTwoGroupPrefixExecution.Query Seed A Q)
    (dec : Activation Side A Q) (reply : Reply Seed Side H W A Q m)
    (N : ℕ) (seed : Seed) (side : Side) : ℕ :=
  firstHitUntil N (decisionAt query dec reply seed side 0 0)

theorem mask_zero_columns {E : Type*} [Zero E] {k : ℕ} (v : Fin k → E) :
    FangqingPrefixAdaptedModel.mask 0 v = 0 := by
  funext i
  simp only [FangqingPrefixAdaptedModel.mask, Nat.not_lt_zero, if_false, Pi.zero_apply]

theorem counts_zero_of_no_previous_activation
    (query : OriginalTwoGroupPrefixExecution.Query Seed A Q) (dec : Activation Side A Q)
    (reply : Reply Seed Side H W A Q m) (seed : Seed) (side : Side)
    (handle : Fin 1 → H) (tail : Fin m → W) (n : ℕ)
    (hno : ∀ j < n, decisionAt query dec reply seed side handle tail j = false) :
    (run query dec reply n seed side handle tail).1 = 0 ∧
      (run query dec reply n seed side handle tail).2.1 = 0 := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      obtain ⟨hh, ht⟩ := ih (fun j hj => hno j (by omega))
      have hd := hno n (by omega)
      change dec n side (run query dec reply n seed side handle tail)
        (query n seed (run query dec reply n seed side handle tail).2.2) = false at hd
      change OriginalPrefixOracleReplay.advance 1 _ _ = 0 ∧
        OriginalPrefixOracleReplay.advance m _ _ = 0
      simp only [hd, tailDecision, hh, ht, Nat.lt_irrefl, decide_false,
        OriginalPrefixOracleReplay.advance, Bool.false_eq_true, and_false, if_false, true_and]

theorem zero_counts_before_public_activation
    (query : OriginalTwoGroupPrefixExecution.Query Seed A Q) (dec : Activation Side A Q)
    (reply : Reply Seed Side H W A Q m) (N : ℕ) (seed : Seed) (side : Side) (n : ℕ)
    (hn : n ≤ firstActivationUntil query dec reply N seed side) :
    (run query dec reply n seed side (0 : Fin 1 → H) (0 : Fin m → W)).1 = 0 ∧
      (run query dec reply n seed side (0 : Fin 1 → H) (0 : Fin m → W)).2.1 = 0 := by
  apply counts_zero_of_no_previous_activation
  intro j hj
  exact before_firstHit_is_false N (decisionAt query dec reply seed side 0 0) j (hj.trans_le hn)

theorem run_before_activation_equals_zero_columns_run
    (query : OriginalTwoGroupPrefixExecution.Query Seed A Q) (dec : Activation Side A Q)
    (reply : Reply Seed Side H W A Q m) (N : ℕ) (seed : Seed) (side : Side)
    (handle : Fin 1 → H) (tail : Fin m → W) (n : ℕ)
    (hn : n ≤ firstActivationUntil query dec reply N seed side) :
    run query dec reply n seed side handle tail = run query dec reply n seed side 0 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hp := ih (by omega)
      have hz := zero_counts_before_public_activation query dec reply N seed side (n + 1) hn
      have hkh := hz.1
      have hkt := hz.2
      change nextHandle dec n side (run query dec reply n seed side (0 : Fin 1 → H) (0 : Fin m → W))
        (query n seed (run query dec reply n seed side (0 : Fin 1 → H) (0 : Fin m → W)).2.2) = 0 at hkh
      change nextTail (m := m) (run query dec reply n seed side (0 : Fin 1 → H) (0 : Fin m → W)) = 0 at hkt
      change step query dec reply n seed side handle tail (run query dec reply n seed side handle tail) =
        step query dec reply n seed side 0 0 (run query dec reply n seed side 0 0)
      rw [hp]
      simp only [step, hkh, hkt, mask_zero_columns]

theorem actual_first_activation_equals_public_activation
    (query : OriginalTwoGroupPrefixExecution.Query Seed A Q) (dec : Activation Side A Q)
    (reply : Reply Seed Side H W A Q m) (N : ℕ) (seed : Seed) (side : Side)
    (handle : Fin 1 → H) (tail : Fin m → W) :
    firstHitUntil N (decisionAt query dec reply seed side handle tail) =
      firstActivationUntil query dec reply N seed side := by
  let tau := firstActivationUntil query dec reply N seed side
  have htau : tau ≤ N := firstHitUntil_le N _
  have hdecEq : ∀ j ≤ tau,
      decisionAt query dec reply seed side handle tail j = decisionAt query dec reply seed side 0 0 j := by
    intro j hj
    unfold decisionAt
    rw [run_before_activation_equals_zero_columns_run query dec reply N seed side handle tail j hj]
  have hno : ∀ j < tau, decisionAt query dec reply seed side handle tail j = false := by
    intro j hj
    rw [hdecEq j hj.le]
    exact before_firstHit_is_false N _ j hj
  have hLower := firstHitUntil_lower_bound N tau (decisionAt query dec reply seed side handle tail) htau hno
  by_cases ht : tau = N
  · have hUpper := firstHitUntil_le N (decisionAt query dec reply seed side handle tail)
    omega
  · have hlt : tau < N := by omega
    have hb : decisionAt query dec reply seed side 0 0 tau = true := firstHit_is_hit_when_lt N _ hlt
    have hHit : decisionAt query dec reply seed side handle tail tau = true := (hdecEq tau le_rfl).trans hb
    exact le_antisymm (firstHit_le_of_hit N _ tau hlt hHit) hLower

theorem actual_counts_zero_before_activation
    (query : OriginalTwoGroupPrefixExecution.Query Seed A Q) (dec : Activation Side A Q)
    (reply : Reply Seed Side H W A Q m) (N : ℕ) (seed : Seed) (side : Side)
    (handle : Fin 1 → H) (tail : Fin m → W) (n : ℕ)
    (hn : n ≤ firstActivationUntil query dec reply N seed side) :
    (run query dec reply n seed side handle tail).1 = 0 ∧
      (run query dec reply n seed side handle tail).2.1 = 0 := by
  rw [run_before_activation_equals_zero_columns_run query dec reply N seed side handle tail n hn]
  exact zero_counts_before_public_activation query dec reply N seed side n hn

theorem activation_response_is_handle_only
    (query : OriginalTwoGroupPrefixExecution.Query Seed A Q) (dec : Activation Side A Q)
    (reply : Reply Seed Side H W A Q m) (N : ℕ) (seed : Seed) (side : Side)
    (handle : Fin 1 → H) (tail : Fin m → W)
    (hact : firstActivationUntil query dec reply N seed side < N) :
    let tau := firstActivationUntil query dec reply N seed side
    (run query dec reply (tau + 1) seed side handle tail).1 = 1 ∧
      (run query dec reply (tau + 1) seed side handle tail).2.1 = 0 := by
  intro tau
  have hz := actual_counts_zero_before_activation query dec reply N seed side handle tail tau le_rfl
  have heq := run_before_activation_equals_zero_columns_run query dec reply N seed side handle tail tau le_rfl
  have hb : decisionAt query dec reply seed side handle tail tau = true := by
    unfold decisionAt
    rw [heq]
    exact firstHit_is_hit_when_lt N _ hact
  change dec tau side (run query dec reply tau seed side handle tail)
    (query tau seed (run query dec reply tau seed side handle tail).2.2) = true at hb
  change OriginalPrefixOracleReplay.advance 1 _ _ = 1 ∧ OriginalPrefixOracleReplay.advance m _ _ = 0
  simp only [hb, tailDecision, hz.1, hz.2, Nat.zero_lt_one, Nat.lt_irrefl, decide_false,
    OriginalPrefixOracleReplay.advance, and_true, if_true, Bool.false_eq_true, and_false, if_false]

theorem actual_post_activation_counts
    (query : OriginalTwoGroupPrefixExecution.Query Seed A Q) (dec : Activation Side A Q)
    (reply : Reply Seed Side H W A Q m) (N : ℕ) (seed : Seed) (side : Side)
    (handle : Fin 1 → H) (tail : Fin m → W)
    (hact : firstActivationUntil query dec reply N seed side < N) (j : ℕ) :
    let tau := firstActivationUntil query dec reply N seed side
    (run query dec reply (tau + 1 + j) seed side handle tail).1 = 1 ∧
      (run query dec reply (tau + 1 + j) seed side handle tail).2.1 = min j m := by
  intro tau
  induction j with
  | zero => simpa only [Nat.add_zero, Nat.zero_min] using activation_response_is_handle_only query dec reply N seed side handle tail hact
  | succ j ih =>
      have hBound := count_step_bounds query dec reply (tau + 1 + j) seed side handle tail
      have hCap := counts_bounded query dec reply (tau + 1 + (j + 1)) seed side handle tail
      have hh : (run query dec reply (tau + 1 + (j + 1)) seed side handle tail).1 = 1 := by
        have hmono : 1 ≤ (run query dec reply (tau + 1 + (j + 1)) seed side handle tail).1 := by
          calc
            1 = (run query dec reply (tau + 1 + j) seed side handle tail).1 := ih.1.symm
            _ ≤ _ := hBound.1
        exact le_antisymm hCap.1 hmono
      have ht := post_activation_tail_schedule query dec reply (tau + 1 + j) seed side handle tail ih.1
      change (run query dec reply (tau + 1 + (j + 1)) seed side handle tail).2.1 = _ at ht
      rw [ih.2] at ht
      refine ⟨hh, ?_⟩
      split_ifs at ht <;> omega

theorem early_actual_path_count
    (query : OriginalTwoGroupPrefixExecution.Query Seed A Q) (dec : Activation Side A Q)
    (reply : Reply Seed Side H W A Q m) (N : ℕ) (seed : Seed) (side : Side)
    (handle : Fin 1 → H) (tail : Fin m → W)
    (hact : firstActivationUntil query dec reply N seed side < N) (q j : ℕ) (hj : j ≤ q / 8) :
    let tau := firstActivationUntil query dec reply N seed side
    1 + (run query dec reply (tau + 1 + j) seed side handle tail).2.1 ≤ q / 8 + 1 := by
  have hcounts := actual_post_activation_counts query dec reply N seed side handle tail hact j
  dsimp only at hcounts ⊢
  rw [hcounts.2]
  omega

theorem floor_eighth_nat (q : ℕ) : Nat.floor ((q : ℝ) / 8) = q / 8 := by
  simpa only [Nat.floor_natCast, Nat.cast_ofNat] using (Nat.floor_div_natCast (q : ℝ) 8)

theorem early_prefix_le_quarter (q k : ℕ) (hq : 8 ≤ q) (hk : k ≤ q / 8 + 1) : 4 * k ≤ q := by
  omega

theorem early_unrevealed_bulk_three_quarters (q k : ℕ) (hq : 8 ≤ q) (hk : k ≤ q / 8 + 1) :
    (3 : ℝ) * (q : ℝ) / 4 ≤ ((q - k : ℕ) : ℝ) := by
  have hh := early_prefix_le_quarter q k hq hk
  have hn : 3 * q ≤ 4 * (q - k) := by omega
  have hr : (3 : ℝ) * (q : ℝ) ≤ 4 * ((q - k : ℕ) : ℝ) := by exact_mod_cast hn
  linarith only [hr]

theorem terminal_before_activation_is_public
    (query : OriginalTwoGroupPrefixExecution.Query Seed A Q) (dec : Activation Side A Q)
    (reply : Reply Seed Side H W A Q m) (out : Seed → OriginalTwoGroupPrefixExecution.History A → Q)
    (N : ℕ) (seed : Seed) (side : Side) (handle : Fin 1 → H) (tail : Fin m → W)
    (hno : firstActivationUntil query dec reply N seed side = N) :
    out seed (run query dec reply N seed side handle tail).2.2 =
      out seed (run query dec reply N seed side 0 0).2.2 := by
  rw [run_before_activation_equals_zero_columns_run query dec reply N seed side handle tail N (by omega)]

theorem terminal_queryOrOutput_is_actual_output
    (query : OriginalTwoGroupPrefixExecution.Query Seed A Q)
    (out : Seed → OriginalTwoGroupPrefixExecution.History A → Q) (N : ℕ)
    (seed : Seed) (hist : OriginalTwoGroupPrefixExecution.History A) :
    OriginalTwoGroupHaarExecution.queryOrOutput query out N (Fin.last N) (seed, hist) = out seed hist := by
  simp only [OriginalTwoGroupHaarExecution.queryOrOutput, Fin.val_last, Nat.lt_irrefl, if_false]

theorem activation_zero_if_initial_decision
    (query : OriginalTwoGroupPrefixExecution.Query Seed A Q) (dec : Activation Side A Q)
    (reply : Reply Seed Side H W A Q m) (N : ℕ) (seed : Seed) (side : Side)
    (hfirst : dec 0 side (0, 0, 0) (query 0 seed 0) = true) :
    firstActivationUntil query dec reply N seed side = 0 := by
  cases N with
  | zero => rfl
  | succ N => simp [firstActivationUntil, firstHitUntil, decisionAt, OriginalTwoGroupPrefixExecution.run, hfirst]


def disclosedPathCount (st : OriginalTwoGroupPrefixExecution.State A) : ℕ := st.1 + st.2.1

theorem actual_early_prefix_count_bound
    (query : OriginalTwoGroupPrefixExecution.Query Seed A Q) (dec : Activation Side A Q)
    (reply : Reply Seed Side H W A Q m) (N : ℕ) (seed : Seed) (side : Side)
    (handle : Fin 1 → H) (tail : Fin m → W) (q n : ℕ) (hnN : n ≤ N)
    (hearly : n ≤ firstActivationUntil query dec reply N seed side + 1 + q / 8) :
    disclosedPathCount (run query dec reply n seed side handle tail) ≤ q / 8 + 1 := by
  let tau := firstActivationUntil query dec reply N seed side
  by_cases hn : n ≤ tau
  · have hz := actual_counts_zero_before_activation query dec reply N seed side handle tail n hn
    simp only [disclosedPathCount, hz.1, hz.2, zero_add]
    omega
  · have hact : firstActivationUntil query dec reply N seed side < N := by dsimp only [tau] at hn; omega
    let j := n - (tau + 1)
    have hindex : tau + 1 + j = n := by dsimp only [j]; omega
    have hj : j ≤ q / 8 := by dsimp only [j, tau] at *; omega
    have hc := actual_post_activation_counts query dec reply N seed side handle tail hact j
    change (run query dec reply (tau + 1 + j) seed side handle tail).1 = 1 ∧
      (run query dec reply (tau + 1 + j) seed side handle tail).2.1 = min j m at hc
    rw [hindex] at hc
    simp only [disclosedPathCount, hc.1, hc.2]
    omega

theorem query_and_extra_terminal_candidate_have_early_bulk
    (query : OriginalTwoGroupPrefixExecution.Query Seed A Q) (dec : Activation Side A Q)
    (reply : Reply Seed Side H W A Q m) (N : ℕ) (seed : Seed) (side : Side)
    (handle : Fin 1 → H) (tail : Fin m → W) (q : ℕ) (hq : 8 ≤ q)
    (n : Fin (N + 1))
    (hearly : n.val ≤ firstActivationUntil query dec reply N seed side + 1 + q / 8) :
    let k := disclosedPathCount (run query dec reply n.val seed side handle tail)
    k ≤ Nat.floor ((q : ℝ) / 8) + 1 ∧
      (3 : ℝ) * (q : ℝ) / 4 ≤ ((q - k : ℕ) : ℝ) := by
  intro k
  have hk := actual_early_prefix_count_bound query dec reply N seed side handle tail q n.val (by omega) hearly
  exact ⟨by simpa only [floor_eighth_nat] using hk, early_unrevealed_bulk_three_quarters q k hq hk⟩


section Measurability

variable [MeasurableSpace Seed] [MeasurableSpace Side] [MeasurableSpace H]
  [MeasurableSpace W] [MeasurableSpace Q] [MeasurableSpace A]

structure BorelKernel (query : OriginalTwoGroupPrefixExecution.Query Seed A Q)
    (dec : Activation Side A Q) (reply : Reply Seed Side H W A Q m) : Prop where
  query_measurable : ∀ n, Measurable (fun x : Seed × OriginalTwoGroupPrefixExecution.History A => query n x.1 x.2)
  decision_measurable : ∀ n, Measurable (fun x : Side × OriginalTwoGroupPrefixExecution.State A × Q => dec n x.1 x.2.1 x.2.2)
  reply_measurable : ∀ n, Measurable
    (fun x : Seed × Side × OriginalTwoGroupPrefixExecution.State A × ℕ × ℕ × (Fin 1 → H) × (Fin m → W) × Q =>
      reply n x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2)

theorem zero_columns_run_measurable
    (query : OriginalTwoGroupPrefixExecution.Query Seed A Q) (dec : Activation Side A Q)
    (reply : Reply Seed Side H W A Q m) (h : BorelKernel query dec reply) (n : ℕ) :
    Measurable (fun x : Seed × Side => run query dec reply n x.1 x.2 (0 : Fin 1 → H) (0 : Fin m → W)) := by
  have hr := run_measurable query dec reply h.query_measurable h.decision_measurable h.reply_measurable n
  exact hr.comp (measurable_id.prodMk (measurable_const.prodMk measurable_const))

theorem zero_columns_decision_measurable
    (query : OriginalTwoGroupPrefixExecution.Query Seed A Q) (dec : Activation Side A Q)
    (reply : Reply Seed Side H W A Q m) (h : BorelKernel query dec reply) (n : ℕ) :
    Measurable (fun x : Seed × Side => decisionAt query dec reply x.1 x.2 (0 : Fin 1 → H) (0 : Fin m → W) n) := by
  have hs := zero_columns_run_measurable query dec reply h n
  have hh := measurable_snd.comp (measurable_snd.comp hs)
  have hz := (h.query_measurable n).comp (measurable_fst.prodMk hh)
  exact (h.decision_measurable n).comp (measurable_snd.prodMk (hs.prodMk hz))

theorem finite_firstHit_measurable {Ω : Type*} [MeasurableSpace Ω]
    (b : ℕ → Ω → Bool) (hb : ∀ n, Measurable (b n)) (N : ℕ) :
    Measurable (fun x => firstHitUntil N (fun n => b n x)) := by
  induction N generalizing b with
  | zero => exact measurable_const
  | succ N ih =>
      have ht := ih (fun n x => b (n + 1) x) (fun n => hb (n + 1))
      have hs : MeasurableSet {x | b 0 x = true} := (hb 0) (measurableSet_singleton true)
      change Measurable (fun x => if b 0 x = true then 0 else firstHitUntil N (fun n => b (n + 1) x) + 1)
      exact Measurable.ite hs measurable_const (ht.add_const 1)

theorem firstActivationUntil_measurable
    (query : OriginalTwoGroupPrefixExecution.Query Seed A Q) (dec : Activation Side A Q)
    (reply : Reply Seed Side H W A Q m) (h : BorelKernel query dec reply) (N : ℕ) :
    Measurable (fun x : Seed × Side => firstActivationUntil query dec reply N x.1 x.2) :=
  finite_firstHit_measurable
    (fun (n : ℕ) (x : Seed × Side) => decisionAt query dec reply x.1 x.2 0 0 n)
    (fun n => zero_columns_decision_measurable query dec reply h n) N

def cappedSlot (N n : ℕ) : Fin (N + 1) := ⟨min n N, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

def finiteActivationSlot (query : OriginalTwoGroupPrefixExecution.Query Seed A Q)
    (dec : Activation Side A Q) (reply : Reply Seed Side H W A Q m)
    (N : ℕ) (x : Seed × Side) : Fin (N + 1) :=
  cappedSlot N (firstActivationUntil query dec reply N x.1 x.2)

theorem finiteActivationSlot_val
    (query : OriginalTwoGroupPrefixExecution.Query Seed A Q) (dec : Activation Side A Q)
    (reply : Reply Seed Side H W A Q m) (N : ℕ) (x : Seed × Side) :
    (finiteActivationSlot query dec reply N x).val = firstActivationUntil query dec reply N x.1 x.2 := by
  change min (firstActivationUntil query dec reply N x.1 x.2) N = _
  exact Nat.min_eq_left (firstHitUntil_le N _)

theorem finiteActivationSlot_measurable
    (query : OriginalTwoGroupPrefixExecution.Query Seed A Q) (dec : Activation Side A Q)
    (reply : Reply Seed Side H W A Q m) (h : BorelKernel query dec reply) (N : ℕ) :
    Measurable (finiteActivationSlot query dec reply N) :=
  (measurable_of_countable (cappedSlot N)).comp (firstActivationUntil_measurable query dec reply h N)

/-- The first activation is a finite, measurable function of the independent
    algorithm seed and conditioning side only.  Actual hidden columns are not
    arguments of this function; replay and zero counts are conclusions. -/
theorem first_activation_is_a_public_finite_random_time
    (query : OriginalTwoGroupPrefixExecution.Query Seed A Q) (dec : Activation Side A Q)
    (reply : Reply Seed Side H W A Q m) (h : BorelKernel query dec reply) (N : ℕ) :
    Measurable (finiteActivationSlot query dec reply N) ∧
      ∀ (seed : Seed) (side : Side) (handle : Fin 1 → H) (tail : Fin m → W),
        firstHitUntil N (decisionAt query dec reply seed side handle tail) =
          (finiteActivationSlot query dec reply N (seed, side)).val ∧
        ∀ n ≤ (finiteActivationSlot query dec reply N (seed, side)).val,
          run query dec reply n seed side handle tail = run query dec reply n seed side 0 0 ∧
          (run query dec reply n seed side handle tail).1 = 0 ∧
          (run query dec reply n seed side handle tail).2.1 = 0 := by
  refine ⟨finiteActivationSlot_measurable query dec reply h N, ?_⟩
  intro seed side handle tail
  rw [finiteActivationSlot_val]
  refine ⟨actual_first_activation_equals_public_activation query dec reply N seed side handle tail, ?_⟩
  intro n hn
  exact ⟨run_before_activation_equals_zero_columns_run query dec reply N seed side handle tail n hn,
    actual_counts_zero_before_activation query dec reply N seed side handle tail n hn⟩

end Measurability

end FangqingFirstActivationEarlyCount
end

section
-- Source component: RealTwoGroupExecutionMeasurability.lean

namespace FangqingRealTwoGroupExecutionMeasurability

open MeasureTheory OriginalTwoGroupPrefixExecution FangqingFirstActivationEarlyCount

set_option maxHeartbeats 3500000

variable {Seed Side H W Q A : Type*} {m : ℕ} [Zero H] [Zero W] [Zero A]
  [MeasurableSpace Seed] [MeasurableSpace Side] [MeasurableSpace H]
  [MeasurableSpace W] [MeasurableSpace Q] [MeasurableSpace A]

theorem fullRun_measurable
    (query : Query Seed A Q) (dec : Activation Side A Q) (reply : Reply Seed Side H W A Q m)
    (h : BorelKernel query dec reply) (n : ℕ) :
    Measurable (fun x : Input Seed Side H W m => fullRun query dec reply n x.1.1 x.1.2 x.2.1 x.2.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hseed : Measurable (fun x : Input Seed Side H W m => x.1.1) := measurable_fst.comp measurable_fst
      have hside : Measurable (fun x : Input Seed Side H W m => x.1.2) := measurable_snd.comp measurable_fst
      have hkh := measurable_fst.comp ih
      have hkt := measurable_fst.comp (measurable_snd.comp ih)
      have hhist := measurable_snd.comp (measurable_snd.comp ih)
      have hz := (h.query_measurable n).comp (hseed.prodMk hhist)
      have hb := (h.decision_measurable n).comp (hside.prodMk (ih.prodMk hz))
      have hnewh : Measurable (fun x : Input Seed Side H W m =>
          nextHandle dec n x.1.2 (fullRun query dec reply n x.1.1 x.1.2 x.2.1 x.2.2)
            (query n x.1.1 (fullRun query dec reply n x.1.1 x.1.2 x.2.1 x.2.2).2.2)) := by
        apply Measurable.ite
          ((measurableSet_lt hkh measurable_const).inter (hb (measurableSet_singleton true)))
          (hkh.add_const 1) hkh
      have hnewt : Measurable (fun x : Input Seed Side H W m =>
          nextTail (m := m) (fullRun query dec reply n x.1.1 x.1.2 x.2.1 x.2.2)) := by
        have hba : Measurable (fun x : Input Seed Side H W m =>
            tailDecision (fullRun query dec reply n x.1.1 x.1.2 x.2.1 x.2.2)) := by
          apply Measurable.ite (measurableSet_lt measurable_const hkh) measurable_const measurable_const
        apply Measurable.ite
          ((measurableSet_lt hkt measurable_const).inter (hba (measurableSet_singleton true)))
          (hkt.add_const 1) hkt
      have hh : Measurable (fun x : Input Seed Side H W m => x.2.1) := measurable_fst.comp measurable_snd
      have ht : Measurable (fun x : Input Seed Side H W m => x.2.2) := measurable_snd.comp measurable_snd
      have ha := (h.reply_measurable n).comp (hseed.prodMk (hside.prodMk (ih.prodMk
        (hnewh.prodMk (hnewt.prodMk (hh.prodMk (ht.prodMk hz)))))))
      apply hnewh.prodMk
      apply hnewt.prodMk
      apply measurable_pi_lambda
      intro i
      by_cases hi : i = n
      · subst i
        convert! ha using 1
        funext x
        simp [fullStep, fullRun, Function.update_apply]
      · convert! (measurable_pi_apply i).comp hhist using 1
        funext x
        simp [fullStep, fullRun, Function.update_apply, hi]

def actualCandidate
    (query : Query Seed A Q) (dec : Activation Side A Q) (reply : Reply Seed Side H W A Q m)
    (out : Seed → History A → Q) (N : ℕ) (n : Fin (N + 1)) (x : Input Seed Side H W m) : Q :=
  OriginalTwoGroupHaarExecution.queryOrOutput query out N n
    (x.1.1, (fullRun query dec reply n.val x.1.1 x.1.2 x.2.1 x.2.2).2.2)

theorem actualCandidate_measurable
    (query : Query Seed A Q) (dec : Activation Side A Q) (reply : Reply Seed Side H W A Q m)
    (h : BorelKernel query dec reply) (out : Seed → History A → Q)
    (hout : Measurable (fun x : Seed × History A => out x.1 x.2))
    (N : ℕ) (n : Fin (N + 1)) : Measurable (actualCandidate query dec reply out N n) := by
  have hs := fullRun_measurable query dec reply h n.val
  have hh := measurable_snd.comp (measurable_snd.comp hs)
  have hseed : Measurable (fun x : Input Seed Side H W m => x.1.1) := measurable_fst.comp measurable_fst
  change Measurable (fun x : Input Seed Side H W m => if n.val < N
    then query n.val x.1.1 (fullRun query dec reply n.val x.1.1 x.1.2 x.2.1 x.2.2).2.2
    else out x.1.1 (fullRun query dec reply n.val x.1.1 x.1.2 x.2.1 x.2.2).2.2)
  by_cases hn : n.val < N
  · simp only [if_pos hn]
    exact (h.query_measurable n.val).comp (hseed.prodMk hh)
  · simp only [if_neg hn]
    exact hout.comp (hseed.prodMk hh)

def actualBadCandidates
    (query : Query Seed A Q) (dec : Activation Side A Q) (reply : Reply Seed Side H W A Q m)
    (out : Seed → History A → Q) (hit : Input Seed Side H W m → Q → Bool) (N : ℕ) :
    Set (Input Seed Side H W m) :=
  ⋃ n : Fin (N + 1), {x | hit x (actualCandidate query dec reply out N n x) = true}

theorem actualBadCandidates_measurable
    (query : Query Seed A Q) (dec : Activation Side A Q) (reply : Reply Seed Side H W A Q m)
    (h : BorelKernel query dec reply) (out : Seed → History A → Q)
    (hout : Measurable (fun x : Seed × History A => out x.1 x.2))
    (hit : Input Seed Side H W m → Q → Bool)
    (hhit : Measurable (fun x : Input Seed Side H W m × Q => hit x.1 x.2)) (N : ℕ) :
    MeasurableSet (actualBadCandidates query dec reply out hit N) := by
  apply MeasurableSet.iUnion
  intro n
  exact (hhit.comp (measurable_id.prodMk (actualCandidate_measurable query dec reply h out hout N n)))
    (measurableSet_singleton true)

theorem actualBadCandidates_indicator_integrable
    (query : Query Seed A Q) (dec : Activation Side A Q) (reply : Reply Seed Side H W A Q m)
    (h : BorelKernel query dec reply) (out : Seed → History A → Q)
    (hout : Measurable (fun x : Seed × History A => out x.1 x.2))
    (hit : Input Seed Side H W m → Q → Bool)
    (hhit : Measurable (fun x : Input Seed Side H W m × Q => hit x.1 x.2))
    (N : ℕ) (mu : Measure (Input Seed Side H W m)) [IsFiniteMeasure mu] :
    Integrable (Set.indicator (actualBadCandidates query dec reply out hit N) (fun _ => (1 : ℝ))) mu :=
  (integrable_const 1).indicator (actualBadCandidates_measurable query dec reply h out hout hit hhit N)

theorem actualCandidate_at_terminal
    (query : Query Seed A Q) (dec : Activation Side A Q) (reply : Reply Seed Side H W A Q m)
    (out : Seed → History A → Q) (N : ℕ) (x : Input Seed Side H W m) :
    actualCandidate query dec reply out N (Fin.last N) x =
      out x.1.1 (fullRun query dec reply N x.1.1 x.1.2 x.2.1 x.2.2).2.2 := by
  simp only [actualCandidate, OriginalTwoGroupHaarExecution.queryOrOutput, Fin.val_last, Nat.lt_irrefl, if_false]

end FangqingRealTwoGroupExecutionMeasurability
end

section
-- Source component: HaarFrameLawSupport.lean

open MeasureTheory

namespace FangqingHaarFrameLawSupport

open FangqingAdaptiveHaarOriginal FangqingAdaptiveHaarProduct FangqingAdaptiveHaarConcrete

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem measurableSet_orthonormal_frames (m : ℕ) :
    MeasurableSet {V : Fin m → E | Orthonormal ℝ V} := by
  have he : {V : Fin m → E | Orthonormal ℝ V} =
      ⋂ i : Fin m, ⋂ j : Fin m,
        {V | inner ℝ (V i) (V j) = if i = j then 1 else 0} := by
    ext V
    simp only [Set.mem_setOf_eq, Set.mem_iInter, orthonormal_iff_ite]
  rw [he]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  have hc : Continuous (fun V : Fin m → E => inner ℝ (V i) (V j)) :=
    (continuous_apply i).inner (continuous_apply j)
  exact (isClosed_eq hc continuous_const).measurableSet

theorem actual_frameLaw_ae_orthonormal (b : OrthonormalBasis (Fin d) ℝ E) (hmd : m ≤ d) :
    ∀ᵐ V ∂frameLaw b hmd, Orthonormal ℝ V := by
  unfold frameLaw
  apply (ae_map_iff (measurable_frame _).aemeasurable (measurableSet_orthonormal_frames m)).mpr
  exact Filter.Eventually.of_forall (frame_orthonormal b hmd)

theorem independent_product_ae_frame_support
    {A W : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [FiniteDimensional ℝ A] [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] [Nontrivial W]
    (a b : ℕ) (mu : Measure (Fin a → A)) (nu : Measure (Fin b → W))
    [SFinite mu] [SFinite nu]
    (hA : ∀ᵐ V ∂mu, Orthonormal ℝ V) (hW : ∀ᵐ V ∂nu, Orthonormal ℝ V) :
    ∀ᵐ p ∂mu.prod nu, Orthonormal ℝ p.1 ∧ Orthonormal ℝ p.2 := by
  have h0 : MeasurableSet {p : (Fin a → A) × (Fin b → W) | Orthonormal ℝ p.1} :=
    (measurableSet_orthonormal_frames (E := A) a).preimage measurable_fst
  have h1 : MeasurableSet {p : (Fin a → A) × (Fin b → W) | Orthonormal ℝ p.2} :=
    (measurableSet_orthonormal_frames (E := W) b).preimage measurable_snd
  apply (Measure.ae_prod_iff_ae_ae (h0.inter h1)).mpr
  filter_upwards [hA] with v hv
  filter_upwards [hW] with w hw
  exact ⟨hv, hw⟩

end FangqingHaarFrameLawSupport
end

section
-- Source component: ActualRelayHaarEvent.lean

open MeasureTheory ProbabilityTheory
open scoped Topology

namespace FangqingActualRelayHaarEvent

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingCanonicalSuppressedRelay FangqingActualPaddedRelayReplies FangqingActualRelayCandidates
  OriginalTwoGroupPrefixExecution OriginalTwoGroupHaarExecution

noncomputable section
set_option maxHeartbeats 3500000

variable {A B W Seed : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
  [MeasurableSpace W] [BorelSpace W] [Nontrivial W]
  {outer nt : ℕ}

abbrev RelayInput (Seed A W : Type*) (outer nt : ℕ) := Input Seed (Parameters A W outer nt) A W (nt+2)

def handleBad (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B)
    (m0 m1 : Fin (outer+1) → ℝ) (packet : Fin (outer+1))
    (query : Query Seed (AugResponse A B W outer nt) (Point A B W outer))
    (out : Seed → History (AugResponse A B W outer nt) → Point A B W outer) (N : ℕ) (Rclip : ℝ) :
    Set (RelayInput Seed A W outer nt) :=
  ⋃ n : Fin (N+1), ⋃ j : Fin 3, ⋃ i : Fin 1,
    {x | (run query (activation c C packet) (virtualReply c C m0 m1 packet) n.val x.1.1 x.1.2 x.2.1 x.2.2).1 ≤ i.val ∧
      c.delta/8 < |inner ℝ (x.2.1 i) (generatedCandidate query (activation c C packet) (virtualReply c C m0 m1 packet)
        out N 3 (handleComponent C packet) Rclip n j x)|}

def tailBad (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B)
    (m0 m1 : Fin (outer+1) → ℝ) (packet : Fin (outer+1))
    (query : Query Seed (AugResponse A B W outer nt) (Point A B W outer))
    (out : Seed → History (AugResponse A B W outer nt) → Point A B W outer) (N : ℕ) (Rclip : ℝ) :
    Set (RelayInput Seed A W outer nt) :=
  ⋃ n : Fin (N+1), ⋃ j : Fin 3, ⋃ i : Fin (nt+2),
    {x | (run query (activation c C packet) (virtualReply c C m0 m1 packet) n.val x.1.1 x.1.2 x.2.1 x.2.2).2.1 ≤ i.val ∧
      c.delta/8 < |inner ℝ (x.2.2 i) (generatedCandidate query (activation c C packet) (virtualReply c C m0 m1 packet)
        out N 3 (tailComponent c packet) Rclip n j x)|}

theorem good_complement_gives_all_clipped_projection_bounds
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ) (packet : Fin (outer+1))
    (query : Query Seed (AugResponse A B W outer nt) (Point A B W outer))
    (out : Seed → History (AugResponse A B W outer nt) → Point A B W outer) (N : ℕ) (Rclip : ℝ)
    (x : RelayInput Seed A W outer nt)
    (hx : x ∉ handleBad c C m0 m1 packet query out N Rclip ∪ tailBad c C m0 m1 packet query out N Rclip)
    (n : Fin (N+1)) (j : Fin 3) :
    ((run query (activation c C packet) (virtualReply c C m0 m1 packet) n.val x.1.1 x.1.2 x.2.1 x.2.2).1 = 0 →
      |inner ℝ (x.2.1 0) (generatedCandidate query (activation c C packet) (virtualReply c C m0 m1 packet)
        out N 3 (handleComponent C packet) Rclip n j x)| ≤ c.delta/8) ∧
    (∀ i, (run query (activation c C packet) (virtualReply c C m0 m1 packet) n.val x.1.1 x.1.2 x.2.1 x.2.2).2.1 ≤ i.val →
      |inner ℝ (x.2.2 i) (generatedCandidate query (activation c C packet) (virtualReply c C m0 m1 packet)
        out N 3 (tailComponent c packet) Rclip n j x)| ≤ c.delta/8) := by
  constructor
  · intro hk
    apply le_of_not_gt
    intro hb
    exact hx (Or.inl (Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨0,⟨hk.le,hb⟩⟩⟩⟩))
  · intro i hi
    apply le_of_not_gt
    intro hb
    exact hx (Or.inr (Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨i,⟨hi,hb⟩⟩⟩⟩))

theorem good_complement_gives_actual_dual_flatness
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ) (packet : Fin (outer+1))
    (query : Query Seed (AugResponse A B W outer nt) (Point A B W outer))
    (out : Seed → History (AugResponse A B W outer nt) → Point A B W outer) (N : ℕ) (Rclip : ℝ)
    (hR : 2*c.R ≤ Rclip) (x : RelayInput Seed A W outer nt)
    (hx : x ∉ handleBad c C m0 m1 packet query out N Rclip ∪ tailBad c C m0 m1 packet query out N Rclip) :
    ∀ n < N,
      let st := run query (activation c C packet) (virtualReply c C m0 m1 packet) n x.1.1 x.1.2 x.2.1 x.2.2
      let z := query n x.1.1 st.2.2
      ‖z (1,packet)‖ ≤ 2*c.R →
        (st.1 = 0 → |inner ℝ (x.2.1 0) ((C packet).symm (z (1,packet)).fst.snd)| ≤ c.delta/8) ∧
        (∀ i, st.2.1 ≤ i.val → |inner ℝ (x.2.2 i) (z (1,packet)).snd| ≤ c.delta/8) := by
  intro n hn
  dsimp only
  intro hy
  let kn : Fin (N+1) := ⟨n,by omega⟩
  have hg := good_complement_gives_all_clipped_projection_bounds c C m0 m1 packet query out N Rclip x hx kn 0
  simp only [generatedCandidate,queryOrOutput,kn,if_pos hn] at hg
  constructor
  · intro hh
    exact (clipped_dual_projection_good c C packet (x.2.1 0) x.2.2 _ Rclip hR hy (hg.1 hh) _ hg.2).1
  · intro i hi
    by_cases hh : (run query (activation c C packet) (virtualReply c C m0 m1 packet) n x.1.1 x.1.2 x.2.1 x.2.2).1 = 0
    · exact (clipped_dual_projection_good c C packet (x.2.1 0) x.2.2 _ Rclip hR hy (hg.1 hh) _ hg.2).2 i hi
    · have hb := dual_components_bounded_by_packet_norm (C packet)
        (query n x.1.1 (run query (activation c C packet) (virtualReply c C m0 m1 packet) n x.1.1 x.1.2 x.2.1 x.2.2).2.2 (1,packet))
      have hi' := hg.2 i hi
      simpa only [tailComponent,mappedPacketPoint,if_true,
        OriginalPrefixOracleHaarBridge.zeroClip_eq Rclip _ (hb.2.trans (hy.trans hR))] using hi'

section Probability
variable [MeasurableSpace Seed]
  [SecondCountableTopology A] [SecondCountableTopology W]
  [MeasurableSpace (PhysicalSpace A B W)] [BorelSpace (PhysicalSpace A B W)]
  [SecondCountableTopology (PhysicalSpace A B W)]
  [MeasurableSpace (Point A B W outer)] [BorelSpace (Point A B W outer)]
  [MeasurableSpace (Point A B W outer →L[ℝ] Point A B W outer)] [BorelSpace (Point A B W outer →L[ℝ] Point A B W outer)]

theorem actual_full_relay_haar_bad_probability
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ) (packet : Fin (outer+1))
    (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hp : ContDiff ℝ 3 c.phi)
    (sigma : Measure (Seed × Parameters A W outer nt)) [IsProbabilityMeasure sigma]
    {dA dW : ℕ} (bA : OrthonormalBasis (Fin dA) ℝ A) (hA : 1 ≤ dA)
    (bW : OrthonormalBasis (Fin dW) ℝ W) (hW : nt+2 ≤ dW)
    (query : Query Seed (AugResponse A B W outer nt) (Point A B W outer))
    (hq : ∀ n, Measurable (fun x : Seed × History (AugResponse A B W outer nt) => query n x.1 x.2))
    (out : Seed → History (AugResponse A B W outer nt) → Point A B W outer)
    (hout : Measurable (fun x : Seed × History (AugResponse A B W outer nt) => out x.1 x.2))
    (N : ℕ) (Rclip zeta : ℝ) (hRc : 0 < Rclip) (hz : 0 < zeta)
    (hbudgetA : 2*Rclip^2/(c.delta/8)^2*Real.log ((2*3*(N+1)*1)/(zeta/2)) ≤ ((dA-1:ℕ):ℝ))
    (hbudgetW : 2*Rclip^2/(c.delta/8)^2*Real.log ((2*3*(N+1)*(nt+2))/(zeta/2)) ≤ ((dW-(nt+2):ℕ):ℝ)) :
    let mu := packetLaw sigma bA hA bW hW
    mu.real (handleBad c C m0 m1 packet query out N Rclip ∪ tailBad c C m0 m1 packet query out N Rclip) ≤ zeta := by
  haveI : IsProbabilityMeasure (FangqingAdaptiveHaarOriginal.frameLaw bA hA) :=
    Measure.isProbabilityMeasure_map (FangqingAdaptiveHaarProduct.measurable_frame _).aemeasurable
  haveI : IsProbabilityMeasure (FangqingAdaptiveHaarOriginal.frameLaw bW hW) :=
    Measure.isProbabilityMeasure_map (FangqingAdaptiveHaarProduct.measurable_frame _).aemeasurable
  have hh := actual_handle_and_tail_haar_calls sigma bA hA bW hW query (activation c C packet) (virtualReply c C m0 m1 packet)
    hq (activation_measurable c C packet) (actual_virtual_reply_measurable c C m0 m1 packet hd hdw hp) out hout N 3
    (handleComponent C packet) (tailComponent c packet)
    (fun j => (handleComponent_continuous C packet j).measurable)
    (fun j => (tailComponent_continuous c packet j).measurable)
    Rclip Rclip (c.delta/8) (c.delta/8) hRc hRc (by positivity) (by positivity)
  dsimp only at hh ⊢
  have hH := hh.1.2 (zeta/2) (by positivity) (by norm_num) (by norm_num) (by positivity)
    (by simpa only [Nat.cast_ofNat,Nat.cast_one,Nat.cast_add] using hbudgetA)
  have hT := hh.2.2 (zeta/2) (by positivity) (by norm_num) (by omega) (by positivity)
    (by simpa only [Nat.cast_ofNat,Nat.cast_one,Nat.cast_add] using hbudgetW)
  have hu := measureReal_union_le (μ := packetLaw sigma bA hA bW hW)
    (handleBad c C m0 m1 packet query out N Rclip) (tailBad c C m0 m1 packet query out N Rclip)
  change (packetLaw sigma bA hA bW hW).real (handleBad c C m0 m1 packet query out N Rclip) ≤ zeta/2 at hH
  change (packetLaw sigma bA hA bW hW).real (tailBad c C m0 m1 packet query out N Rclip) ≤ zeta/2 at hT
  linarith only [hu,hH,hT]

end Probability
end
end FangqingActualRelayHaarEvent
end

section
-- Source component: ActualRelayEarlyGeometry.lean

open MeasureTheory
open scoped Topology

namespace FangqingActualRelayEarlyGeometry

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingCanonicalSuppressedRelay FangqingActualPaddedRelayReplies FangqingActualRelayCandidates
  FangqingActualRelayHaarEvent FangqingFirstActivationEarlyCount
  OriginalTwoGroupPrefixExecution OriginalTwoGroupHaarExecution OriginalPacketOrientationNormalization
  OriginalPacketDistanceGapBounds

noncomputable section
set_option maxHeartbeats 3500000

variable {A B W Seed : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
  [MeasurableSpace W] [BorelSpace W] [Nontrivial W]
  {outer nt : ℕ}

theorem actual_early_tail_count
    (query : Query Seed (AugResponse A B W outer nt) (Point A B W outer))
    (dec : Activation (Parameters A W outer nt) (AugResponse A B W outer nt) (Point A B W outer))
    (reply : Reply Seed (Parameters A W outer nt) A W (AugResponse A B W outer nt) (Point A B W outer) (nt+2))
    (N : ℕ) (x : RelayInput Seed A W outer nt) (q n : ℕ) (hn : n ≤ N)
    (hearly : n ≤ firstActivationUntil query dec reply N x.1.1 x.1.2 + 1 + q/8) :
    (run query dec reply n x.1.1 x.1.2 x.2.1 x.2.2).2.1 ≤ q/8 := by
  let tau := firstActivationUntil query dec reply N x.1.1 x.1.2
  by_cases hbefore : n ≤ tau
  · have hz := actual_counts_zero_before_activation query dec reply N x.1.1 x.1.2 x.2.1 x.2.2 n hbefore
    omega
  · have hact : firstActivationUntil query dec reply N x.1.1 x.1.2 < N := by dsimp only [tau] at hbefore; omega
    let j := n - (tau+1)
    have hj : j ≤ q/8 := by dsimp only [j,tau] at *; omega
    have heq : tau+1+j = n := by dsimp only [j]; omega
    have hc := actual_post_activation_counts query dec reply N x.1.1 x.1.2 x.2.1 x.2.2 hact j
    change (run query dec reply (tau+1+j) x.1.1 x.1.2 x.2.1 x.2.2).1 = 1 ∧
      (run query dec reply (tau+1+j) x.1.1 x.1.2 x.2.1 x.2.2).2.1 = min j (nt+2) at hc
    rw [heq] at hc
    omega

theorem actual_early_generated_candidate_avoids_private_chambers
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ) (packet : Fin (outer+1))
    (query : Query Seed (AugResponse A B W outer nt) (Point A B W outer))
    (out : Seed → History (AugResponse A B W outer nt) → Point A B W outer) (N q : ℕ)
    (hq : 8 ≤ q) (hfit : q ≤ nt+2) (Rclip Cmin : ℝ)
    (hd : 0 ≤ c.delta) (hdw : c.delta ≤ c.omega) (hw : 0 < c.omega)
    (hb : 0 < c.beta) (hl : 0 < c.lam) (ha : 0 < c.a)
    (hell : c.ell = c.lam/c.beta * distanceScale q c.omega)
    (x : RelayInput Seed A W outer nt) (hh : ‖x.2.1 0‖ = 1) (ht : Orthonormal ℝ x.2.2)
    (hZ : ‖Z c (C packet) (x.2.1 0) x.2.2‖ ≤ Cmin * distanceScale q c.omega)
    (hclip : (Cmin+3) * distanceScale q c.omega ≤ Rclip)
    (hbulk : ∀ j : Fin (nt+3), (j.val : ℝ) ≤ q → 3*(q:ℝ)*c.omega ≤
      inner ℝ (physicalFrame (C packet) (x.2.1 0) nt x.2.2 j) (Z c (C packet) (x.2.1 0) x.2.2))
    (hx : x ∉ handleBad c C m0 m1 packet query out N Rclip ∪ tailBad c C m0 m1 packet query out N Rclip)
    (n : Fin (N+1))
    (hearly : n.val ≤ firstActivationUntil query (activation c C packet) (virtualReply c C m0 m1 packet) N x.1.1 x.1.2 + 1+q/8) :
    let z := queryOrOutput query out N n (x.1.1,
      (run query (activation c C packet) (virtualReply c C m0 m1 packet) n.val x.1.1 x.1.2 x.2.1 x.2.2).2.2)
    ownRelayHit c C packet x.2.1 x.2.2 z = false ∧ packetOutputHit c C packet x.2.1 x.2.2 z = false := by
  intro z
  let st := run query (activation c C packet) (virtualReply c C m0 m1 packet) n.val x.1.1 x.1.2 x.2.1 x.2.2
  have hk := actual_early_tail_count query (activation c C packet) (virtualReply c C m0 m1 packet) N x q n.val (by omega) hearly
  have hsep (j : Fin 3) : 2 * distanceScale q c.omega <
      ‖Z c (C packet) (x.2.1 0) x.2.2 - mappedPacketPoint c packet j z‖ := by
    have hg := (good_complement_gives_all_clipped_projection_bounds c C m0 m1 packet query out N Rclip x hx n j).2
    apply early_distance_from_clipped_tail_projection (C packet) (x.2.1 0) hh q st.2.1 x.2.2 ht hq hfit hk
      c.delta c.omega Cmin Rclip hd hdw hw _ _ hZ hclip hbulk
    intro i hi
    exact hg i hi
  have hX := hsep 1
  have hS := hsep 2
  simp only [mappedPacketPoint, show (1:Fin 3) ≠ 0 by decide, if_false, if_true] at hX
  simp only [mappedPacketPoint, show (2:Fin 3) ≠ 0 by decide, show (2:Fin 3) ≠ 1 by decide, if_false] at hS
  rw [fenchel_distance_identity c.beta c.lam hb hl] at hX
  rw [relay_distance_identity c.beta c.lam c.a hb hl ha] at hS
  have hD : 0 < distanceScale q c.omega := by unfold distanceScale; positivity
  have hnormX : 2*c.ell < ‖z (0,packet) - center c (C packet) (x.2.1 0,x.2.2)‖ := by
    unfold center
    rw [hell]
    apply (mul_lt_mul_iff_right₀ (div_pos hb hl)).mp
    have halg : (c.beta/c.lam) * (2*(c.lam/c.beta*distanceScale q c.omega)) = 2*distanceScale q c.omega := by field_simp <;> ring
    rw [halg]
    exact hX
  have hnormS : 2*(c.a*c.ell) < ‖z (2,packet) - c.a • center c (C packet) (x.2.1 0,x.2.2)‖ := by
    unfold center
    rw [hell]
    apply (mul_lt_mul_iff_right₀ (div_pos hb (mul_pos ha hl))).mp
    have halg : (c.beta/(c.a*c.lam)) * (2*(c.a*(c.lam/c.beta*distanceScale q c.omega))) = 2*distanceScale q c.omega := by field_simp <;> ring
    rw [halg]
    exact hS
  constructor
  · exact decide_eq_false (not_lt_of_ge hnormS.le)
  · exact decide_eq_false (not_lt_of_ge hnormX.le)

end
end FangqingActualRelayEarlyGeometry
end

section
-- Source component: StoppedUniformFirstHit.lean

namespace FangqingStoppedUniformFirstHit

open OriginalPrefixOracleReplay OriginalTwoGroupPrefixExecution
  FangqingStoppedTwoGroupReplay FangqingFirstActivationEarlyCount

set_option maxHeartbeats 3000000

variable {Seed Side H W Q R : Type*} [Zero H] [Zero W] [Zero R] {m : ℕ}

def realActivationUntil (query : OriginalTwoGroupPrefixExecution.Query Seed R Q) (dec : Activation Side R Q)
    (reply : Reply Seed Side H W R Q m) (N : ℕ) (seed : Seed) (side : Side)
    (handle : Fin 1 → H) (tail : Fin m → W) : ℕ :=
  firstHitUntil N (fun n =>
    let st := fullRun query dec reply n seed side handle tail
    dec n side st (query n seed st.2.2))

theorem stopped_replay_and_virtual_early_exclusion_give_actual_increment
    (query : OriginalTwoGroupPrefixExecution.Query Seed R Q) (dec : Activation Side R Q)
    (realReply virtualReply : Reply Seed Side H W R Q m)
    (hit outputHit : Q → Bool) (out : Seed → OriginalTwoGroupPrefixExecution.History R → Q)
    (N B : ℕ) (seed : Seed) (side : Side) (handle : Fin 1 → H) (tail : Fin m → W)
    (hlocal : ∀ n < N,
      let st := run query dec virtualReply n seed side handle tail
      let z := query n seed st.2.2
      hit z = false →
      let kh := nextHandle dec n side st z
      let kt := nextTail (m:=m) st
      realReply n seed side st kh kt handle tail z =
        virtualReply n seed side st kh kt (FangqingPrefixAdaptedModel.mask kh handle)
          (FangqingPrefixAdaptedModel.mask kt tail) z)
    (hearly : ∀ n < N, n ≤ firstActivationUntil query dec virtualReply N seed side + 1+B →
      hit (query n seed (run query dec virtualReply n seed side handle tail).2.2) = false)
    (hout : N ≤ firstActivationUntil query dec virtualReply N seed side+1+B →
      outputHit (out seed (run query dec virtualReply N seed side handle tail).2.2) = false) :
    realActivationUntil query dec realReply N seed side handle tail =
      firstActivationUntil query dec virtualReply N seed side ∧
    (∀ n < N, n ≤ realActivationUntil query dec realReply N seed side handle tail+1+B →
      hit (query n seed (fullRun query dec realReply n seed side handle tail).2.2) = false) ∧
    (N ≤ realActivationUntil query dec realReply N seed side handle tail+1+B →
      outputHit (out seed (fullRun query dec realReply N seed side handle tail).2.2) = false) := by
  let tau := firstActivationUntil query dec virtualReply N seed side
  let vh := fun n => hit (query n seed (run query dec virtualReply n seed side handle tail).2.2)
  let stop := firstHitUntil N vh
  have hrep := literal_replay_stopped_at_virtual_first_hit query dec realReply virtualReply hit out N seed side handle tail hlocal
  change (∀ n ≤ stop, fullRun query dec realReply n seed side handle tail = run query dec virtualReply n seed side handle tail) ∧ _ at hrep
  have htauN : tau ≤ N := firstHitUntil_le N _
  have hstopN : stop ≤ N := firstHitUntil_le N vh
  have hstopLower : min N (tau+2+B) ≤ stop := by
    apply firstHitUntil_lower_bound N (min N (tau+2+B)) vh (Nat.min_le_left _ _)
    intro n hn
    exact hearly n (by omega) (by dsimp only [tau] at *; omega)
  have htauStop : tau ≤ stop := by omega
  have hdEq (n : ℕ) (hn : n ≤ stop) :
      (let st := fullRun query dec realReply n seed side handle tail
       dec n side st (query n seed st.2.2)) =
      decisionAt query dec virtualReply seed side handle tail n := by
    simp only [hrep.1 n hn,decisionAt]
  have hvAct := actual_first_activation_equals_public_activation query dec virtualReply N seed side handle tail
  change firstHitUntil N (decisionAt query dec virtualReply seed side handle tail) = tau at hvAct
  have hrLower : tau ≤ realActivationUntil query dec realReply N seed side handle tail := by
    apply firstHitUntil_lower_bound N tau _ htauN
    intro n hn
    rw [hdEq n (by omega)]
    exact before_firstHit_is_false N (decisionAt query dec virtualReply seed side handle tail) n (by rw [hvAct]; exact hn)
  have hact : realActivationUntil query dec realReply N seed side handle tail = tau := by
    by_cases heq : tau = N
    · have hh : realActivationUntil query dec realReply N seed side handle tail ≤ N := firstHitUntil_le N _
      omega
    · have ht : tau < N := by omega
      have hh : decisionAt query dec virtualReply seed side handle tail tau = true := by
        have ht' : firstHitUntil N (decisionAt query dec virtualReply seed side handle tail) < N := by rw [hvAct]; exact ht
        simpa only [hvAct] using firstHit_is_hit_when_lt N (decisionAt query dec virtualReply seed side handle tail) ht'
      have hr : (let st := fullRun query dec realReply tau seed side handle tail
          dec tau side st (query tau seed st.2.2)) = true := (hdEq tau htauStop).trans hh
      exact le_antisymm (firstHit_le_of_hit N _ tau ht hr) hrLower
  refine ⟨hact,?_,?_⟩
  · intro n hn he
    rw [hact] at he
    have hnstop : n ≤ stop := by omega
    rw [hrep.1 n hnstop]
    exact hearly n hn he
  · intro he
    rw [hact] at he
    have hstop : stop = N := by omega
    rw [hrep.2.2 hstop]
    exact hout he

end FangqingStoppedUniformFirstHit
end

section
-- Source component: ActualUniformFirstHit.lean

open MeasureTheory
open scoped Topology

namespace FangqingActualUniformFirstHit

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingCanonicalSuppressedRelay FangqingActualPaddedRelayReplies FangqingActualRelayCandidates
  FangqingActualRelayHaarEvent FangqingActualRelayEarlyGeometry FangqingFirstActivationEarlyCount
  FangqingActualPaddedRelayLocalReplay FangqingStoppedUniformFirstHit
  OriginalTwoGroupPrefixExecution OriginalTwoGroupHaarExecution OriginalPacketOrientationNormalization
  OriginalPacketDistanceGapBounds

noncomputable section
set_option maxHeartbeats 3500000

variable {A B W Seed : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
  [MeasurableSpace W] [BorelSpace W] [Nontrivial W]
  {outer nt : ℕ}

def realTau (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ) (packet : Fin (outer+1))
    (query : Query Seed (AugResponse A B W outer nt) (Point A B W outer)) (N : ℕ)
    (x : RelayInput Seed A W outer nt) : ℕ :=
  realActivationUntil query (activation c C packet) (realReply c C m0 m1 packet) N x.1.1 x.1.2 x.2.1 x.2.2

def virtualTau (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ) (packet : Fin (outer+1))
    (query : Query Seed (AugResponse A B W outer nt) (Point A B W outer)) (N : ℕ)
    (x : RelayInput Seed A W outer nt) : ℕ :=
  firstActivationUntil query (activation c C packet) (virtualReply c C m0 m1 packet) N x.1.1 x.1.2

def actualCandidate (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ) (packet : Fin (outer+1))
    (query : Query Seed (AugResponse A B W outer nt) (Point A B W outer))
    (out : Seed → History (AugResponse A B W outer nt) → Point A B W outer) (N : ℕ) (n : Fin (N+1))
    (x : RelayInput Seed A W outer nt) : Point A B W outer :=
  queryOrOutput query out N n (x.1.1,
    (fullRun query (activation c C packet) (realReply c C m0 m1 packet) n.val x.1.1 x.1.2 x.2.1 x.2.2).2.2)

def actualBad (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ) (packet : Fin (outer+1))
    (query : Query Seed (AugResponse A B W outer nt) (Point A B W outer))
    (out : Seed → History (AugResponse A B W outer nt) → Point A B W outer) (N q : ℕ) :
    Set (RelayInput Seed A W outer nt) :=
  {x | realTau c C m0 m1 packet query N x ≠ virtualTau c C m0 m1 packet query N x} ∪
  (⋃ n : Fin N, {x | n.val ≤ realTau c C m0 m1 packet query N x+1+q/8 ∧
    ownRelayHit c C packet x.2.1 x.2.2 (actualCandidate c C m0 m1 packet query out N n.castSucc x) = true}) ∪
  {x | N ≤ realTau c C m0 m1 packet query N x+1+q/8 ∧
    packetOutputHit c C packet x.2.1 x.2.2 (actualCandidate c C m0 m1 packet query out N (Fin.last N) x) = true}

theorem actual_bad_implies_projection_failure_on_true_frames
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ) (packet : Fin (outer+1))
    (query : Query Seed (AugResponse A B W outer nt) (Point A B W outer))
    (out : Seed → History (AugResponse A B W outer nt) → Point A B W outer) (N q : ℕ)
    (hq : 8 ≤ q) (hfit : q ≤ nt+2) (Rclip Cmin : ℝ)
    (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hR : 0 < c.R)
    (hb : 0 < c.beta) (hl : 0 < c.lam) (ha : 0 < c.a)
    (hell : c.ell = c.lam/c.beta * distanceScale q c.omega)
    (x : RelayInput Seed A W outer nt) (hh : ‖x.2.1 0‖ = 1) (ht : Orthonormal ℝ x.2.2)
    (hZ : ‖Z c (C packet) (x.2.1 0) x.2.2‖ ≤ Cmin * distanceScale q c.omega)
    (hclip : (Cmin+3) * distanceScale q c.omega ≤ Rclip) (hRshell : 2*c.R ≤ Rclip)
    (hbulk : ∀ j : Fin (nt+3), (j.val : ℝ) ≤ q → 3*(q:ℝ)*c.omega ≤
      inner ℝ (physicalFrame (C packet) (x.2.1 0) nt x.2.2 j) (Z c (C packet) (x.2.1 0) x.2.2)) :
    x ∈ actualBad c C m0 m1 packet query out N q →
      x ∈ handleBad c C m0 m1 packet query out N Rclip ∪ tailBad c C m0 m1 packet query out N Rclip := by
  contrapose!
  intro hgood
  have hw : 0 < c.omega := hd.trans_le hdw
  have he : 0 < c.ell := by rw [hell]; unfold distanceScale; positivity
  have hflat := good_complement_gives_actual_dual_flatness c C m0 m1 packet query out N Rclip hRshell x hgood
  have hearly (n : Fin (N+1)) (hn : n.val ≤ firstActivationUntil query (activation c C packet)
      (virtualReply c C m0 m1 packet) N x.1.1 x.1.2+1+q/8) :=
    actual_early_generated_candidate_avoids_private_chambers c C m0 m1 packet query out N q hq hfit Rclip Cmin
      hd.le hdw hw hb hl ha hell x hh ht hZ hclip hbulk hgood n hn
  have hresult := stopped_replay_and_virtual_early_exclusion_give_actual_increment query (activation c C packet)
    (realReply c C m0 m1 packet) (virtualReply c C m0 m1 packet)
    (ownRelayHit c C packet x.2.1 x.2.2) (packetOutputHit c C packet x.2.1 x.2.2) out
    N (q/8) x.1.1 x.1.2 x.2.1 x.2.2 (by
      intro n hn
      dsimp only
      intro hhit
      have hcounts := counts_bounded query (activation c C packet) (virtualReply c C m0 m1 packet) n x.1.1 x.1.2 x.2.1 x.2.2
      by_cases hn0 : n = 0
      · subst n
        exact actual_zero_slot_equals_virtual_masked_record c C m0 m1 packet x.1.1 x.1.2 _ x.2.1 x.2.2 _ hcounts.1
      · exact actual_paid_reply_equals_virtual_prefix_reply c C m0 m1 packet n (Nat.pos_of_ne_zero hn0)
          x.1.1 x.1.2 _ x.2.1 x.2.2 _ hd hdw hR ha he hcounts.1 hcounts.2
          (unactivated_run_has_zero_tail query (activation c C packet) (virtualReply c C m0 m1 packet) n x.1.1 x.1.2 x.2.1 x.2.2)
          hhit (hflat n hn)) (by
      intro n hn he
      simpa only [queryOrOutput,if_pos hn] using (hearly ⟨n,by omega⟩ he).1) (by
      intro he
      simpa only [queryOrOutput,Fin.val_last,lt_self_iff_false,if_false] using (hearly (Fin.last N) he).2)
  rintro ((hact | hquery) | houtput)
  · exact hact hresult.1
  · obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hquery
    have hh := hresult.2.1 n.val n.isLt hn.1
    have hb := hn.2
    simp only [actualCandidate,queryOrOutput,Fin.val_castSucc,if_pos n.isLt] at hb
    rw [hh] at hb
    contradiction
  · have hh := hresult.2.2 houtput.1
    have hb := houtput.2
    simp only [actualCandidate,queryOrOutput,Fin.val_last,lt_self_iff_false,if_false] at hb
    rw [hh] at hb
    contradiction

end
end FangqingActualUniformFirstHit
end

section
-- Source component: ConditionalEventFibers.lean

open MeasureTheory

namespace FangqingConditionalEventFibers

noncomputable section
set_option maxHeartbeats 2000000

variable {Side Frame : Type*} [MeasurableSpace Side] [MeasurableSpace Frame]

theorem bound_under_every_side_law_gives_every_fiber_bound
    (nu : Measure Frame) [IsProbabilityMeasure nu] (bad : Set (Side × Frame))
    (hbad : MeasurableSet bad) (zeta : ℝ)
    (hbound : ∀ (sigma : Measure Side) [IsProbabilityMeasure sigma], (sigma.prod nu).real bad ≤ zeta) :
    ∀ s : Side, nu.real (Prod.mk s ⁻¹' bad) ≤ zeta := by
  intro s
  have h := hbound (Measure.dirac s)
  rw [Measure.dirac_prod] at h
  change ((Measure.map (Prod.mk s) nu) bad).toReal ≤ zeta at h
  rw [Measure.map_apply measurable_prodMk_left hbad] at h
  exact h

theorem every_side_law_bound_gives_actual_conditional_event_bound
    (sigma : Measure Side) (nu : Measure Frame) [IsProbabilityMeasure sigma] [IsProbabilityMeasure nu]
    (bad : Set (Side × Frame)) (hbad : MeasurableSet bad) (zeta : ℝ)
    (hbound : ∀ (rho : Measure Side) [IsProbabilityMeasure rho], (rho.prod nu).real bad ≤ zeta) :
    ∀ᵐ p ∂sigma.prod nu,
      (sigma.prod nu)[bad.indicator (fun _ => (1:ℝ)) |
        MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Side)] p ≤ zeta := by
  have hf : StronglyMeasurable (bad.indicator (fun _ => (1:ℝ))) :=
    (measurable_const.indicator hbad).stronglyMeasurable
  have hfi : Integrable (bad.indicator (fun _ => (1:ℝ))) (sigma.prod nu) :=
    (integrable_const 1).indicator hbad
  apply FangqingConditionalFrameFibers.uniform_fiber_bound_gives_side_conditional_bound sigma nu _ hf hfi zeta
  intro s
  have hs : MeasurableSet (Prod.mk s ⁻¹' bad) := hbad.preimage measurable_prodMk_left
  have he : (fun v => bad.indicator (fun _ => (1:ℝ)) (s,v)) =
      (Prod.mk s ⁻¹' bad).indicator (fun _ => (1:ℝ)) := by
    funext v
    by_cases hv : (s,v) ∈ bad <;> simp [Set.indicator,hv]
  rw [he]
  change (∫ v, (Prod.mk s ⁻¹' bad).indicator (1 : Frame → ℝ) v ∂nu) ≤ zeta
  rw [integral_indicator_one hs]
  exact bound_under_every_side_law_gives_every_fiber_bound nu bad hbad zeta hbound s

end
end FangqingConditionalEventFibers
end

section
-- Source component: FirstHitCubicDimensionBudget.lean

namespace FangqingFirstHitCubicDimensionBudget

open OriginalPacketDistanceGapBounds

set_option maxHeartbeats 3000000

theorem clipped_physical_radius_ratio_is_q_cubed
    (q omega CR cdelta : ℝ) (hq : 0 ≤ q) (hw : 0 < omega) (hd : 0 < cdelta) :
    2*(CR*distanceScale q omega)^2/(cdelta*omega/8)^2 = (128*CR^2/cdelta^2)*q^3 := by
  rw [mul_pow, distanceScale_sq q omega hq]
  field_simp
  <;> ring

theorem original_dimension_budget_controls_padded_haar_budget
    (N : ℕ) (m : ℕ) (hm : 0 < m) (q omega CR cdelta Cm C zeta : ℝ)
    (hq : 1 ≤ q) (hw : 0 < omega) (hd : 0 < cdelta)
    (hmq : (m:ℝ) ≤ Cm*q) (hC : 1 ≤ C) (hCratio : 128*CR^2/cdelta^2 ≤ C)
    (hClog : 12*Cm ≤ C) (hz : 0 < zeta) (hz1 : zeta ≤ 1) :
    2*(CR*distanceScale q omega)^2/(cdelta*omega/8)^2 *
      Real.log ((2*3*((N+1:ℕ)+1)*m)/(zeta/2)) ≤
      C*q^3*Real.log (C*((N:ℝ)+2)*q/zeta) := by
  rw [clipped_physical_radius_ratio_is_q_cubed q omega CR cdelta (by linarith only [hq]) hw hd]
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hN : 1 ≤ (N:ℝ)+2 := by have hh := Nat.cast_nonneg (α:=ℝ) N; linarith only [hh]
  have hbig : 1 ≤ C*((N:ℝ)+2)*q :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC hN) hq
  have hlog0 : 0 ≤ Real.log (C*((N:ℝ)+2)*q/zeta) :=
    Real.log_nonneg ((le_div_iff₀ hz).mpr (by simpa only [one_mul] using hz1.trans hbig))
  have hsmallpos : 0 < (2*3*((N+1:ℕ)+1)*m:ℝ)/(zeta/2) := by positivity
  have harg : (2*3*((N+1:ℕ)+1)*m:ℝ)/(zeta/2) ≤ C*((N:ℝ)+2)*q/zeta := by
    have h12m : 12*(m:ℝ) ≤ C*q := by nlinarith only [hmq,mul_le_mul_of_nonneg_right hClog hq0.le]
    rw [show (2*3*((N+1:ℕ)+1)*m:ℝ)/(zeta/2) = ((N:ℝ)+2)*(12*(m:ℝ))/zeta by push_cast; ring]
    rw [mul_right_comm C ((N:ℝ)+2) q]
    have hmul := mul_le_mul_of_nonneg_left h12m (show (0:ℝ) ≤ (N:ℝ)+2 by positivity)
    convert! div_le_div_of_nonneg_right hmul hz.le using 1 <;> ring
  calc
    _ ≤ (128*CR^2/cdelta^2)*q^3*Real.log (C*((N:ℝ)+2)*q/zeta) :=
      mul_le_mul_of_nonneg_left (Real.log_le_log hsmallpos harg) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCratio (by positivity)) hlog0

end FangqingFirstHitCubicDimensionBudget
end

section
-- Source component: FullRunActivationMeasurability.lean

open MeasureTheory

namespace FangqingFullRunActivationMeasurability

open OriginalTwoGroupPrefixExecution FangqingFirstActivationEarlyCount
  FangqingRealTwoGroupExecutionMeasurability FangqingStoppedUniformFirstHit

variable {Seed Side H W Q R : Type*} {m : ℕ} [Zero H] [Zero W] [Zero R]
  [MeasurableSpace Seed] [MeasurableSpace Side] [MeasurableSpace H]
  [MeasurableSpace W] [MeasurableSpace Q] [MeasurableSpace R]

set_option maxHeartbeats 2000000

theorem full_decision_at_measurable
    (query : Query Seed R Q) (dec : Activation Side R Q) (reply : Reply Seed Side H W R Q m)
    (h : BorelKernel query dec reply) (n : ℕ) :
    Measurable (fun x : Input Seed Side H W m =>
      let st := fullRun query dec reply n x.1.1 x.1.2 x.2.1 x.2.2
      dec n x.1.2 st (query n x.1.1 st.2.2)) := by
  have hs := fullRun_measurable query dec reply h n
  have hseed : Measurable (fun x : Input Seed Side H W m => x.1.1) := measurable_fst.fst
  have hside : Measurable (fun x : Input Seed Side H W m => x.1.2) := measurable_fst.snd
  have hz := (h.query_measurable n).comp (hseed.prodMk hs.snd.snd)
  exact (h.decision_measurable n).comp (hside.prodMk (hs.prodMk hz))

theorem real_activation_until_measurable
    (query : Query Seed R Q) (dec : Activation Side R Q) (reply : Reply Seed Side H W R Q m)
    (h : BorelKernel query dec reply) (N : ℕ) :
    Measurable (fun x : Input Seed Side H W m =>
      realActivationUntil query dec reply N x.1.1 x.1.2 x.2.1 x.2.2) :=
  finite_firstHit_measurable _ (fun n => full_decision_at_measurable query dec reply h n) N

end FangqingFullRunActivationMeasurability
end

section
-- Source component: ActualFirstHitMeasurability.lean

open MeasureTheory

namespace FangqingActualFirstHitMeasurability

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingCanonicalSuppressedRelay FangqingActualPaddedRelayReplies FangqingActualRelayHaarEvent
  FangqingActualUniformFirstHit FangqingStoppedUniformFirstHit FangqingFirstActivationEarlyCount
  OriginalTwoGroupPrefixExecution

noncomputable section
set_option maxHeartbeats 3000000

variable {A B W Seed : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
  [MeasurableSpace W] [BorelSpace W] [Nontrivial W]
  [MeasurableSpace Seed] [SecondCountableTopology A] [SecondCountableTopology W]
  [MeasurableSpace (PhysicalSpace A B W)] [BorelSpace (PhysicalSpace A B W)]
  [SecondCountableTopology (PhysicalSpace A B W)]
  {outer nt : ℕ}
  [MeasurableSpace (Point A B W outer)] [BorelSpace (Point A B W outer)]
  [MeasurableSpace (Point A B W outer →L[ℝ] Point A B W outer)] [BorelSpace (Point A B W outer →L[ℝ] Point A B W outer)]

variable (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ) (packet : Fin (outer+1))
    (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hp : ContDiff ℝ 3 c.phi)
    (query : Query Seed (AugResponse A B W outer nt) (Point A B W outer))
    (hq : ∀ n, Measurable (fun x : Seed × History (AugResponse A B W outer nt) => query n x.1 x.2))

include hd hdw hp hq

private theorem realKernel : BorelKernel query (activation c C packet) (realReply c C m0 m1 packet) :=
  ⟨hq,activation_measurable c C packet,actual_real_reply_measurable c C m0 m1 packet hd hdw hp⟩

private theorem virtualKernel : BorelKernel query (activation c C packet) (virtualReply c C m0 m1 packet) :=
  ⟨hq,activation_measurable c C packet,actual_virtual_reply_measurable c C m0 m1 packet hd hdw hp⟩

theorem realTau_measurable (N : ℕ) : Measurable (realTau c C m0 m1 packet query N) := by
  exact FangqingFullRunActivationMeasurability.real_activation_until_measurable query (activation c C packet)
    (realReply c C m0 m1 packet) (realKernel c C m0 m1 packet hd hdw hp query hq) N

theorem virtualTau_measurable (N : ℕ) : Measurable (virtualTau c C m0 m1 packet query N) :=
  (firstActivationUntil_measurable query (activation c C packet) (virtualReply c C m0 m1 packet)
    (virtualKernel c C m0 m1 packet hd hdw hp query hq) N).comp measurable_fst

theorem actualCandidate_measurable
    (out : Seed → History (AugResponse A B W outer nt) → Point A B W outer)
    (ho : Measurable (fun x : Seed × History (AugResponse A B W outer nt) => out x.1 x.2))
    (N : ℕ) (n : Fin (N+1)) :
    Measurable (FangqingActualUniformFirstHit.actualCandidate c C m0 m1 packet query out N n) :=
  FangqingRealTwoGroupExecutionMeasurability.actualCandidate_measurable query (activation c C packet) (realReply c C m0 m1 packet)
    (realKernel c C m0 m1 packet hd hdw hp query hq) out ho N n

theorem actualBad_measurable
    (out : Seed → History (AugResponse A B W outer nt) → Point A B W outer)
    (ho : Measurable (fun x : Seed × History (AugResponse A B W outer nt) => out x.1 x.2)) (N q : ℕ) :
    MeasurableSet (actualBad c C m0 m1 packet query out N q) := by
  have hr := realTau_measurable c C m0 m1 packet hd hdw hp query hq N
  have hv := virtualTau_measurable c C m0 m1 packet hd hdw hp query hq N
  have hh : Measurable (fun x : RelayInput Seed A W outer nt => x.2.1) := measurable_snd.fst
  have ht : Measurable (fun x : RelayInput Seed A W outer nt => x.2.2) := measurable_snd.snd
  have hquery : ∀ n : Fin N, MeasurableSet {x : RelayInput Seed A W outer nt |
      n.val ≤ realTau c C m0 m1 packet query N x+1+q/8 ∧
      ownRelayHit c C packet x.2.1 x.2.2 (FangqingActualUniformFirstHit.actualCandidate c C m0 m1 packet query out N n.castSucc x) = true} := by
    intro n
    have hc := actualCandidate_measurable c C m0 m1 packet hd hdw hp query hq out ho N n.castSucc
    have hb := (ownRelayHit_measurable c C packet).comp (hh.prodMk (ht.prodMk hc))
    exact (measurableSet_le measurable_const ((hr.add_const 1).add_const (q/8))).inter (hb (measurableSet_singleton true))
  have houtput : MeasurableSet {x : RelayInput Seed A W outer nt |
      N ≤ realTau c C m0 m1 packet query N x+1+q/8 ∧
      packetOutputHit c C packet x.2.1 x.2.2 (FangqingActualUniformFirstHit.actualCandidate c C m0 m1 packet query out N (Fin.last N) x) = true} := by
    have hc := actualCandidate_measurable c C m0 m1 packet hd hdw hp query hq out ho N (Fin.last N)
    have hb := (packetOutputHit_measurable c C packet).comp (hh.prodMk (ht.prodMk hc))
    exact (measurableSet_le measurable_const ((hr.add_const 1).add_const (q/8))).inter (hb (measurableSet_singleton true))
  exact ((measurableSet_eq_fun hr hv).compl.union (MeasurableSet.iUnion hquery)).union houtput

end
end FangqingActualFirstHitMeasurability
end

section
-- Source component: ActualFirstHitProbability.lean

open MeasureTheory
open scoped Topology

namespace FangqingActualFirstHitProbability

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingCanonicalSuppressedRelay FangqingActualPaddedRelayReplies FangqingActualRelayHaarEvent
  FangqingActualUniformFirstHit FangqingActualFirstHitMeasurability FangqingHaarFrameLawSupport
  FangqingConditionalEventFibers FangqingAdaptiveHaarOriginal
  OriginalTwoGroupPrefixExecution OriginalTwoGroupHaarExecution OriginalPacketOrientationNormalization
  OriginalPacketDistanceGapBounds

noncomputable section
set_option maxHeartbeats 3500000

variable {A B W Seed : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
  [MeasurableSpace W] [BorelSpace W] [Nontrivial W]
  [MeasurableSpace Seed] [SecondCountableTopology A] [SecondCountableTopology W]
  [MeasurableSpace (PhysicalSpace A B W)] [BorelSpace (PhysicalSpace A B W)]
  [SecondCountableTopology (PhysicalSpace A B W)]
  {outer nt : ℕ}
  [MeasurableSpace (Point A B W outer)] [BorelSpace (Point A B W outer)]
  [MeasurableSpace (Point A B W outer →L[ℝ] Point A B W outer)] [BorelSpace (Point A B W outer →L[ℝ] Point A B W outer)]

variable (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ) (packet : Fin (outer+1))
    (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hp : ContDiff ℝ 3 c.phi)
    (hR : 0 < c.R) (hb : 0 < c.beta) (hl : 0 < c.lam) (ha : 0 < c.a)
    (q : ℕ) (hq : 8 ≤ q) (hfit : q ≤ nt+2)
    (hell : c.ell = c.lam/c.beta * distanceScale q c.omega)
    (Cmin Rclip : ℝ) (hRc : 0 < Rclip)
    (hclip : (Cmin+3)*distanceScale q c.omega ≤ Rclip) (hRshell : 2*c.R ≤ Rclip)
    (hPacket : ∀ (h : A) (tail : Fin (nt+2) → W), ‖h‖=1 → Orthonormal ℝ tail →
      ‖Z c (C packet) h tail‖ ≤ Cmin*distanceScale q c.omega ∧
      ∀ j : Fin (nt+3), (j.val : ℝ) ≤ q → 3*(q:ℝ)*c.omega ≤
        inner ℝ (physicalFrame (C packet) h nt tail j) (Z c (C packet) h tail))
    {dA dW : ℕ} (bA : OrthonormalBasis (Fin dA) ℝ A) (hA : 1 ≤ dA)
    (bW : OrthonormalBasis (Fin dW) ℝ W) (hW : nt+2 ≤ dW)
    (query : Query Seed (AugResponse A B W outer nt) (Point A B W outer))
    (hqMeas : ∀ n, Measurable (fun x : Seed × History (AugResponse A B W outer nt) => query n x.1 x.2))
    (out : Seed → History (AugResponse A B W outer nt) → Point A B W outer)
    (hout : Measurable (fun x : Seed × History (AugResponse A B W outer nt) => out x.1 x.2))
    (N : ℕ) (zeta : ℝ) (hz : 0 < zeta)
    (hbudgetA : 2*Rclip^2/(c.delta/8)^2*Real.log ((2*3*(N+1)*1)/(zeta/2)) ≤ ((dA-1:ℕ):ℝ))
    (hbudgetW : 2*Rclip^2/(c.delta/8)^2*Real.log ((2*3*(N+1)*(nt+2))/(zeta/2)) ≤ ((dW-(nt+2):ℕ):ℝ))

include hd hdw hp hR hb hl ha hq hfit hell hRc hclip hRshell hPacket hqMeas hout hz hbudgetA hbudgetW

theorem actual_first_hit_bad_probability_under_every_side_law
    (sigma : Measure (Seed × Parameters A W outer nt)) [IsProbabilityMeasure sigma] :
    (packetLaw sigma bA hA bW hW).real (actualBad c C m0 m1 packet query out N q) ≤ zeta := by
  haveI : IsProbabilityMeasure (frameLaw bA hA) :=
    Measure.isProbabilityMeasure_map (FangqingAdaptiveHaarProduct.measurable_frame _).aemeasurable
  haveI : IsProbabilityMeasure (frameLaw bW hW) :=
    Measure.isProbabilityMeasure_map (FangqingAdaptiveHaarProduct.measurable_frame _).aemeasurable
  haveI : IsProbabilityMeasure (packetLaw sigma bA hA bW hW) :=
    inferInstanceAs (IsProbabilityMeasure (sigma.prod ((frameLaw bA hA).prod (frameLaw bW hW))))
  have hsupport := independent_product_ae_frame_support 1 (nt+2) (frameLaw bA hA) (frameLaw bW hW)
    (actual_frameLaw_ae_orthonormal bA hA) (actual_frameLaw_ae_orthonormal bW hW)
  have hset : MeasurableSet {x : RelayInput Seed A W outer nt | Orthonormal ℝ x.2.1 ∧ Orthonormal ℝ x.2.2} :=
    ((measurableSet_orthonormal_frames (E:=A) 1).preimage measurable_snd.fst).inter
      ((measurableSet_orthonormal_frames (E:=W) (nt+2)).preimage measurable_snd.snd)
  have hs : ∀ᵐ x ∂packetLaw sigma bA hA bW hW, Orthonormal ℝ x.2.1 ∧ Orthonormal ℝ x.2.2 := by
    apply (Measure.ae_prod_iff_ae_ae hset).mpr
    exact Filter.Eventually.of_forall (fun _ => hsupport)
  have hinc : ∀ᵐ x ∂packetLaw sigma bA hA bW hW,
      x ∈ actualBad c C m0 m1 packet query out N q →
      x ∈ handleBad c C m0 m1 packet query out N Rclip ∪ tailBad c C m0 m1 packet query out N Rclip := by
    filter_upwards [hs] with x hx
    have hh : ‖x.2.1 0‖ = 1 := hx.1.norm_eq_one 0
    have hdta := hPacket (x.2.1 0) x.2.2 hh hx.2
    exact actual_bad_implies_projection_failure_on_true_frames c C m0 m1 packet query out N q hq hfit Rclip Cmin
      hd hdw hR hb hl ha hell x hh hx.2 hdta.1 hclip hRshell hdta.2
  have hm := measure_mono_ae hinc
  have hmr : (packetLaw sigma bA hA bW hW).real (actualBad c C m0 m1 packet query out N q) ≤
      (packetLaw sigma bA hA bW hW).real (handleBad c C m0 m1 packet query out N Rclip ∪ tailBad c C m0 m1 packet query out N Rclip) :=
    ENNReal.toReal_mono (by finiteness) hm
  exact hmr.trans (actual_full_relay_haar_bad_probability c C m0 m1 packet hd hdw hp sigma bA hA bW hW query hqMeas out hout N Rclip zeta hRc hz hbudgetA hbudgetW)

theorem actual_first_hit_conditional_probability
    (sigma : Measure (Seed × Parameters A W outer nt)) [IsProbabilityMeasure sigma] :
    let nu := (frameLaw bA hA).prod (frameLaw bW hW)
    (∀ s : Seed × Parameters A W outer nt,
      nu.real (Prod.mk s ⁻¹' actualBad c C m0 m1 packet query out N q) ≤ zeta) ∧
    ∀ᵐ x ∂packetLaw sigma bA hA bW hW,
      (packetLaw sigma bA hA bW hW)[(actualBad c C m0 m1 packet query out N q).indicator (fun _ => (1:ℝ)) |
        MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace (Seed × Parameters A W outer nt))] x ≤ zeta := by
  intro nu
  haveI : IsProbabilityMeasure (frameLaw bA hA) :=
    Measure.isProbabilityMeasure_map (FangqingAdaptiveHaarProduct.measurable_frame _).aemeasurable
  haveI : IsProbabilityMeasure (frameLaw bW hW) :=
    Measure.isProbabilityMeasure_map (FangqingAdaptiveHaarProduct.measurable_frame _).aemeasurable
  haveI : IsProbabilityMeasure nu := inferInstanceAs (IsProbabilityMeasure ((frameLaw bA hA).prod (frameLaw bW hW)))
  have hbad := actualBad_measurable c C m0 m1 packet hd hdw hp query hqMeas out hout N q
  have hbound (rho : Measure (Seed × Parameters A W outer nt)) [IsProbabilityMeasure rho] :
      (rho.prod nu).real (actualBad c C m0 m1 packet query out N q) ≤ zeta :=
    actual_first_hit_bad_probability_under_every_side_law c C m0 m1 packet hd hdw hp hR hb hl ha q hq hfit hell
      Cmin Rclip hRc hclip hRshell hPacket bA hA bW hW query hqMeas out hout N zeta hz hbudgetA hbudgetW rho
  exact ⟨bound_under_every_side_law_gives_every_fiber_bound nu _ hbad zeta hbound,
    every_side_law_bound_gives_actual_conditional_event_bound sigma nu _ hbad zeta hbound⟩

end
end FangqingActualFirstHitProbability
end

section
-- Source component: ActualFirstHitOriginalDimension.lean

open MeasureTheory

namespace FangqingActualFirstHitOriginalDimension

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingActualPaddedRelayReplies FangqingActualRelayHaarEvent FangqingActualUniformFirstHit
  FangqingActualFirstHitProbability FangqingFirstHitCubicDimensionBudget FangqingAdaptiveHaarOriginal
  OriginalTwoGroupPrefixExecution OriginalTwoGroupHaarExecution OriginalPacketOrientationNormalization
  OriginalPacketDistanceGapBounds

noncomputable section
set_option maxHeartbeats 3500000

variable {A B W Seed : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
  [MeasurableSpace W] [BorelSpace W] [Nontrivial W]
  [MeasurableSpace Seed] [SecondCountableTopology A] [SecondCountableTopology W]
  [MeasurableSpace (PhysicalSpace A B W)] [BorelSpace (PhysicalSpace A B W)]
  [SecondCountableTopology (PhysicalSpace A B W)]
  {outer nt : ℕ}
  [MeasurableSpace (Point A B W outer)] [BorelSpace (Point A B W outer)]
  [MeasurableSpace (Point A B W outer →L[ℝ] Point A B W outer)] [BorelSpace (Point A B W outer →L[ℝ] Point A B W outer)]

def dimensionConstant (CR cdelta Cm : ℝ) : ℝ := max 1 (max (128*CR^2/cdelta^2) (12*Cm))

theorem actual_conditional_first_hit_from_original_cubic_dimension
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ) (packet : Fin (outer+1))
    (hp : ContDiff ℝ 3 c.phi) (hR : 0 < c.R) (hb : 0 < c.beta) (hl : 0 < c.lam) (ha : 0 < c.a)
    (q : ℕ) (hq : 8 ≤ q) (hfit : q ≤ nt+2) (hw : 0 < c.omega)
    (hell : c.ell = c.lam/c.beta * distanceScale q c.omega)
    (Cmin CR cdelta Cm : ℝ) (hCR : 0 < CR) (hcd : 0 < cdelta) (hcd1 : cdelta ≤ 1) (hCm : 1 ≤ Cm)
    (hcDelta : c.delta = cdelta*c.omega) (hclip : Cmin+3 ≤ CR)
    (hRshell : 2*c.R ≤ CR*distanceScale q c.omega) (hm : (nt+2:ℕ) ≤ Cm*(q:ℝ))
    (hPacket : ∀ (h : A) (tail : Fin (nt+2) → W), ‖h‖=1 → Orthonormal ℝ tail →
      ‖Z c (C packet) h tail‖ ≤ Cmin*distanceScale q c.omega ∧
      ∀ j : Fin (nt+3), (j.val : ℝ) ≤ q → 3*(q:ℝ)*c.omega ≤
        inner ℝ (physicalFrame (C packet) h nt tail j) (Z c (C packet) h tail))
    {dA dW : ℕ} (bA : OrthonormalBasis (Fin dA) ℝ A) (hA : 1 ≤ dA)
    (bW : OrthonormalBasis (Fin dW) ℝ W) (hW : nt+2 ≤ dW)
    (query : Query Seed (AugResponse A B W outer nt) (Point A B W outer))
    (hqMeas : ∀ n, Measurable (fun x : Seed × History (AugResponse A B W outer nt) => query n x.1 x.2))
    (out : Seed → History (AugResponse A B W outer nt) → Point A B W outer)
    (hout : Measurable (fun x : Seed × History (AugResponse A B W outer nt) => out x.1 x.2))
    (Npaid : ℕ) (zeta : ℝ) (hz : 0 < zeta) (hz1 : zeta ≤ 1)
    (hDimA : dimensionConstant CR cdelta Cm*(q:ℝ)^3*
      Real.log (dimensionConstant CR cdelta Cm*((Npaid:ℝ)+2)*(q:ℝ)/zeta) ≤ ((dA-1:ℕ):ℝ))
    (hDimW : dimensionConstant CR cdelta Cm*(q:ℝ)^3*
      Real.log (dimensionConstant CR cdelta Cm*((Npaid:ℝ)+2)*(q:ℝ)/zeta) ≤ ((dW-(nt+2):ℕ):ℝ))
    (sigma : Measure (Seed × Parameters A W outer nt)) [IsProbabilityMeasure sigma] :
    let nu := (frameLaw bA hA).prod (frameLaw bW hW)
    (∀ s : Seed × Parameters A W outer nt,
      nu.real (Prod.mk s ⁻¹' actualBad c C m0 m1 packet query out (Npaid+1) q) ≤ zeta) ∧
    ∀ᵐ x ∂packetLaw sigma bA hA bW hW,
      (packetLaw sigma bA hA bW hW)[(actualBad c C m0 m1 packet query out (Npaid+1) q).indicator (fun _ => (1:ℝ)) |
        MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace (Seed × Parameters A W outer nt))] x ≤ zeta := by
  let CD := dimensionConstant CR cdelta Cm
  have hCD1 : 1 ≤ CD := le_max_left _ _
  have hCDratio : 128*CR^2/cdelta^2 ≤ CD := (le_max_left _ _).trans (le_max_right _ _)
  have hCDlog : 12*Cm ≤ CD := (le_max_right _ _).trans (le_max_right _ _)
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hq0 : (0:ℝ) ≤ q := by positivity
  have hD : 0 < distanceScale q c.omega := by unfold distanceScale; positivity
  have hdelta : 0 < c.delta := by rw [hcDelta]; positivity
  have hdw : c.delta ≤ c.omega := by rw [hcDelta]; simpa only [one_mul] using mul_le_mul_of_nonneg_right hcd1 hw.le
  have hbudgetA : 2*(CR*distanceScale q c.omega)^2/(c.delta/8)^2*
      Real.log ((2*3*((Npaid+1:ℕ)+1)*1)/(zeta/2)) ≤ ((dA-1:ℕ):ℝ) := by
    rw [hcDelta]
    simpa only [Nat.cast_one,Nat.cast_add,Nat.cast_ofNat] using (original_dimension_budget_controls_padded_haar_budget Npaid 1 (by omega) q c.omega CR cdelta Cm CD zeta hq1 hw hcd
      (by simpa only [Nat.cast_one] using one_le_mul_of_one_le_of_one_le hCm hq1)
      hCD1 hCDratio hCDlog hz hz1).trans hDimA
  have hbudgetW : 2*(CR*distanceScale q c.omega)^2/(c.delta/8)^2*
      Real.log ((2*3*((Npaid+1:ℕ)+1)*(nt+2))/(zeta/2)) ≤ ((dW-(nt+2):ℕ):ℝ) := by
    rw [hcDelta]
    simpa only [Nat.cast_one,Nat.cast_add,Nat.cast_ofNat] using (original_dimension_budget_controls_padded_haar_budget Npaid (nt+2) (by omega) q c.omega CR cdelta Cm CD zeta hq1 hw hcd
      (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hm) hCD1 hCDratio hCDlog hz hz1).trans hDimW
  exact actual_first_hit_conditional_probability c C m0 m1 packet hdelta hdw hp hR hb hl ha q hq hfit hell
    Cmin (CR*distanceScale q c.omega) (mul_pos hCR hD)
    (mul_le_mul_of_nonneg_right hclip hD.le) hRshell hPacket bA hA bW hW query hqMeas out hout
    (Npaid+1) zeta hz hbudgetA hbudgetW sigma

end
end FangqingActualFirstHitOriginalDimension
end

section
-- Source component: ActualPaddedProgramEmbedding.lean

namespace FangqingActualPaddedProgramEmbedding

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingCanonicalSuppressedRelay FangqingActualPaddedRelayReplies FangqingPreHitRelayLocality
  FangqingPaddedPublicInputProgram OriginalTwoGroupPrefixExecution

noncomputable section
set_option maxHeartbeats 3000000

variable {A B W Seed : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {outer nt : ℕ}

def decodePublic (answer : AugResponse A B W outer nt) : Point A B W outer := answer.1.2.1

def oracleView (answer : AugResponse A B W outer nt) : Response A B W outer := answer.1

theorem actual_paid_program_and_unqueried_output_are_preserved
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ) (packet : Fin (outer+1))
    (query : PublicQuery Seed (Point A B W outer) (Response A B W outer) (Point A B W outer))
    (out : Seed → Point A B W outer → (ℕ → Response A B W outer) → Point A B W outer)
    (seed : Seed) (side : Parameters A W outer nt) (handle : Fin 1 → A) (tail : Fin (nt+2) → W) (Npaid : ℕ) :
    let publicInput := publicInitialPoint c (initialHandle packet side handle tail)
    let oracle := fullReply (realFamily c C m0 m1 packet side (handle 0,tail))
    let qpad := paddedQuery query decodePublic oracleView (0 : Point A B W outer)
    let st := fullRun qpad (activation c C packet) (realReply c C m0 m1 packet) (Npaid+1) seed side handle tail
    decodePublic (st.2.2 0) = publicInput ∧
    paidHistory oracleView st.2.2 = ordinaryRun query oracle seed publicInput Npaid ∧
    paddedOutput out decodePublic oracleView seed st.2.2 = out seed publicInput (ordinaryRun query oracle seed publicInput Npaid) := by
  intro publicInput oracle qpad st
  have hzero : oracleView (0 : AugResponse A B W outer nt) = (0 : Response A B W outer) := rfl
  have hpublic : ∀ st kh kt point,
      decodePublic (realReply c C m0 m1 packet 0 seed side st kh kt handle tail point) = publicInput := by
    intro st kh kt point
    simp [decodePublic,realReply,kernelReply,publicRecord,publicInput]
  have hpaid : ∀ n, 0 < n → ∀ st kh kt point,
      oracleView (realReply c C m0 m1 packet n seed side st kh kt handle tail point) = oracle point := by
    intro n hn st kh kt point
    exact real_paid_reply_is_literal_full_bundle c C m0 m1 packet n hn seed side st kh kt handle tail point
  have hstate := zero_cost_public_input_embedding query oracle decodePublic oracleView (0 : Point A B W outer)
    (activation c C packet) (realReply c C m0 m1 packet) seed side handle tail publicInput hzero hpublic hpaid Npaid
  exact ⟨hstate.1,hstate.2,original_output_equals_padded_output query oracle out decodePublic oracleView (0 : Point A B W outer)
    (activation c C packet) (realReply c C m0 m1 packet) seed side handle tail publicInput hzero hpublic hpaid Npaid⟩

end
end FangqingActualPaddedProgramEmbedding
end

section
-- Source component: HierarchyCanonicalPacketGeometry.lean

namespace FangqingHierarchyCanonicalPacketGeometry

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingPacketLeakage
  OriginalPacketOrientationNormalization OriginalCanonicalPacketTailSupport OriginalPhysicalPacketMinimizer
  OriginalPacketDistanceGapBounds

noncomputable section

universe u

variable {A B W : Type u}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

theorem canonical_geometry_from_actual_raw_minimum (n : ℕ) (c : Config n)
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1) (tail : Fin (n + 2) → W)
    (ht : Orthonormal ℝ tail) (Cmin : ℝ)
    (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hq : 0 ≤ c.q)
    (hs : 0 < c.scale) (hb : 0 < c.barlam) (Zraw : PhysicalSpace A B W)
    (hmin : ∀ Y,
      rawPacket C h n tail (FlatCubic.edge c.profile c.delta c.omega) c.q
        (c.scale * c.barlam) c.scale (c.scale * (2 * c.omega ^ 2 / Real.sqrt c.q)) Zraw ≤
      rawPacket C h n tail (FlatCubic.edge c.profile c.delta c.omega) c.q
        (c.scale * c.barlam) c.scale (c.scale * (2 * c.omega ^ 2 / Real.sqrt c.q)) Y)
    (hnorm : ‖Zraw‖ ≤ Cmin * distanceScale c.q c.omega)
    (hbulk : ∀ j : Fin (n + 3), (j.val : ℝ) ≤ c.q →
      3 * c.q * c.omega ≤ inner ℝ (physicalFrame C h n tail j) Zraw) :
    ‖FangqingCanonicalLateGateFamily.Z c C h tail‖ ≤ Cmin * distanceScale c.q c.omega ∧
      ∀ j : Fin (n + 3), (j.val : ℝ) ≤ c.q →
        3 * c.q * c.omega ≤ inner ℝ (physicalFrame C h n tail j)
          (FangqingCanonicalLateGateFamily.Z c C h tail) := by
  have he : Zraw = FangqingCanonicalLateGateFamily.Z c C h tail :=
    actual_raw_minimizer_uses_public_coefficients c.profile C h hh n tail ht c.delta c.omega c.q
      c.scale c.barlam hd hdw hq hs hb Zraw hmin
  rw [he] at hnorm hbulk
  exact ⟨hnorm, hbulk⟩

end
end FangqingHierarchyCanonicalPacketGeometry
end

section
-- Source component: HierarchyFirstHitPacketGeometry.lean

open scoped NNReal

namespace FangqingHierarchyFirstHitPacketGeometry

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingHierarchyLateGateWorldFactory
  FangqingHierarchyCanonicalPacketGeometry FangqingPrivateConstantHierarchy FangqingHierarchyAlignment
  FangqingActualRelayScaling FangqingThirdGroupScaling FangqingRelayStationarity
  FangqingPathEdgeRegularity FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
  OriginalPacketDistanceGapBounds OriginalPacketOrientationNormalization OriginalCanonicalPacketTailSupport

noncomputable section
set_option maxHeartbeats 7000000

universe u

theorem same_hierarchy_constants_give_all_canonical_packet_geometries
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw : ℝ)
    (hCm : 0 ≤ Cm) (hCw : 4*(Cm+2) ≤ Cw)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left)
    (hr : ∀ t, Bp < t → phi t = right) (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ Ce : ℝ≥0, 1 ≤ Ce ∧ ∃ K Ks KD csigma Cdelta cL cq cg cT : ℝ,
      0 ≤ K ∧ 0 ≤ Ks ∧ 1 ≤ KD ∧ 0 < csigma ∧ 0 ≤ Cdelta ∧
      0 < cL ∧ cL ≤ 1/256 ∧ 0 < cq ∧ cq ≤ 1 ∧ 0 < cg ∧ cg ≤ 1 ∧ 0 < cT ∧
      AlignmentAvailable cq cL Cw cg KD ∧
      ∀ (A B W : Type u)
        [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
        [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
        [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W],
      ∀ (nt : ℕ) (C : A ≃ₗᵢ[ℝ] B) (L mu eps r rhop q delta omega : ℝ),
      0 < L → 0 < mu → 0 < eps → 1 ≤ r → 0 < rhop → rhop ≤ rho L mu eps r →
      1 ≤ q → q^2 ≤ cq^2*(L/mu) → 0 < delta → delta ≤ omega → ((nt+2:ℕ):ℝ) ≤ Cm*q →
      omega = Cw*((8*(2*mu))/(cg*rhop))*q^2 → distanceScale q omega = packetD (2*cL*L) (2*mu) KD eps →
      let c := originalConfig2 P phi nt Ce K Ks Cm Cw KD csigma Cdelta cL cg L mu eps r rhop q delta omega
      let Cmin := 2*Cw*(Cm+2)
      let CA := 3+8*Ks*(2*Cw)+Cmin
      let CR := 4*CA+Cmin+3
      0 < c.R ∧ 0 < c.beta ∧ 0 < c.lam ∧ 0 < c.a ∧
      c.ell = c.lam/c.beta*distanceScale q omega ∧ 0 < CR ∧ Cmin+3 ≤ CR ∧
      2*c.R ≤ CR*distanceScale q omega ∧
      ∀ (h : A) (tail : Fin (nt+2) → W), ‖h‖=1 → Orthonormal ℝ tail →
        (∀ y, FangqingCanonicalLateGateFamily.H0 c C h tail 0 ≤ FangqingCanonicalLateGateFamily.H0 c C h tail y) ∧
        (∀ y, FangqingCanonicalLateGateFamily.H1 c C h tail (Z c C h tail) ≤ FangqingCanonicalLateGateFamily.H1 c C h tail y) ∧
        ‖Z c C h tail‖ ≤ Cmin*distanceScale q omega ∧
        ∀ j : Fin (nt+3), (j.val : ℝ) ≤ q → 3*q*omega ≤ inner ℝ (physicalFrame C h nt tail j) (Z c C h tail) := by
  obtain ⟨Ce,hCe,K,Kc,Ks,KD,csigma,Cglobal,Cdelta,Ctheta,Clink,Cgap,
    hK,hKc,hKs,hKD,hKDl,hcs,hCG,hCD,hCt,hClink,hGap,hDeriv,
    cL,cq,cg,cT,hcL,hcL256,hcq,hcq1,hcg,hcg1,hcT,hAlignment,hBuilder⟩ :=
    actual_private_constant_hierarchy.{u} P phi Bp left right Cm Cw 10 hCm hCw (by norm_num) hp hl hr hcore
  refine ⟨Ce,hCe,K,Ks,KD,csigma,Cdelta,cL,cq,cg,cT,hK,hKs,hKD,hcs,hCD,hcL,hcL256,hcq,hcq1,hcg,hcg1,hcT,hAlignment,?_⟩
  intro A B W instA instA' instA'' instB instB' instB'' instW instW' instW'' nt C L mu eps r rhop q delta omega
    hL hmu heps hr hrhop hrho hq hqcap hd hdw hn homega hDscale c Cmin CA CR
  let Li := 2*cL*L
  let mui := 2*mu
  let scale := cg*rhop
  let barlam := 8*mui/scale
  have hLi : 0 < Li := by dsimp [Li]; positivity
  have hmui : 0 < mui := by dsimp [mui]; positivity
  have hs : 0 < scale := by dsimp [scale]; positivity
  have hb : 0 < barlam := by dsimp [barlam]; positivity
  have hw : 0 < omega := hd.trans_le hdw
  have hD : 0 < distanceScale q omega := by unfold distanceScale; positivity
  have hCw0 : 0 < Cw := by linarith only [hCm,hCw]
  have hCmin : 0 < Cmin := by dsimp [Cmin]; positivity
  have hCA : 0 < CA := by dsimp [CA]; positivity
  have hCR : 0 < CR := by dsimp [CR]; positivity
  have hBeta : 0 < c.beta := hLi
  have hLam : 0 < c.lam := by change 0 < lam Li mui; unfold lam; positivity
  have hRadius : 0 < c.R := by change 0 < 2*(CA*distanceScale q omega); positivity
  have hAmp : 0 < c.a := by
    change 0 < relayAmplitude 1 (Li/mui) (r/(4*Real.sqrt cL))
    unfold relayAmplitude
    simpa only [one_mul] using (lt_of_lt_of_le zero_lt_one (le_max_left 1 (((Li/mui)^(3/2:ℝ)/(r/(4*Real.sqrt cL)))^(1/3:ℝ))))
  have hEll : c.ell = c.lam/c.beta*distanceScale q omega := by
    change width Li mui KD eps = lam Li mui/Li*distanceScale q omega
    rw [hDscale]
    unfold width
    ring
  refine ⟨hRadius,hBeta,hLam,hAmp,hEll,hCR,?_,?_,?_⟩
  · dsimp [CR]
    linarith only [hCA]
  · change 2*(2*(CA*distanceScale q omega)) ≤ CR*distanceScale q omega
    dsimp [CR]
    nlinarith only [hCmin,hD]
  · intro h tail hh ht
    let Delta := energy L eps/cT
    have hE : 0 < energy L eps := by unfold energy; positivity
    have hDelta : 0 ≤ Delta := by dsimp [Delta]; positivity
    have hCount : ((0+1:ℕ):ℝ) ≤ cT*Delta/energy L eps := by
      dsimp [Delta]
      norm_num
      field_simp [hcT.ne',hE.ne']
      <;> norm_num
    obtain ⟨Zraw,hH0,hH1,hMin0,hMin1,hNorm,hLocalGap,hBulk,hRawMin,hChamber,hReserve,hTable,hCenters⟩ :=
      hBuilder A B W 0 nt C (fun _ => h) (fun _ => tail) L mu eps r rhop q delta omega Delta
        (fun _ => hh) (fun _ => ht) hL hmu heps hr hrhop hrho hq hqcap hd hdw hn hDelta hCount homega hDscale
    have hCanon : Zraw 0 = Z c C h tail :=
      actual_raw_minimizer_uses_public_coefficients P C h hh nt tail ht delta omega q scale barlam
        hd hdw (by linarith only [hq]) hs hb (Zraw 0) (hRawMin 0)
    have hGeom := canonical_geometry_from_actual_raw_minimum nt c C h hh tail ht Cmin hd hdw
      (by change 0 ≤ q; linarith only [hq]) hs hb (Zraw 0) (hRawMin 0) (hNorm 0) (hBulk 0)
    refine ⟨?_,?_,hGeom.1,hGeom.2⟩
    · simpa only [c,originalConfig2,Li,mui,scale,barlam,FangqingCanonicalLateGateFamily.H0] using! hMin0 0
    · have hm1 := hMin1 0
      rw [hCanon] at hm1
      simpa only [c,originalConfig2,Li,mui,scale,barlam,FangqingCanonicalLateGateFamily.H1,FangqingCanonicalLateGateFamily.H0] using! hm1

end
end FangqingHierarchyFirstHitPacketGeometry
end

section
-- Source component: ActualRelayPublicNormalizers.lean

open MeasureTheory

namespace FangqingActualRelayPublicNormalizers

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingPreHitShellNormalizers
  OriginalPacketOrientationNormalization OriginalPhysicalPairedShellPrefix

noncomputable section
set_option maxHeartbeats 3000000

variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {nt : ℕ}

def publicZeroNormalizer (c : Config nt) (C : A ≃ₗᵢ[ℝ] B) (hRef : A) (tailRef : Fin (nt+2) → W) : ℝ :=
  sInf (Set.range (FangqingCanonicalLateGateFamily.H0 c C hRef tailRef))

def publicOneNormalizer (c : Config nt) (C : A ≃ₗᵢ[ℝ] B) (hRef : A) (tailRef : Fin (nt+2) → W) : ℝ :=
  sInf (Set.range (FangqingCanonicalLateGateFamily.H1 c C hRef tailRef))

theorem actual_public_normalizers_are_actual_endpoint_minima
    (c : Config nt) (C : A ≃ₗᵢ[ℝ] B) (hRef : A) (hhRef : ‖hRef‖=1)
    (tailRef : Fin (nt+2) → W) (htRef : Orthonormal ℝ tailRef)
    (h : A) (hh : ‖h‖=1) (tail : Fin (nt+2) → W) (ht : Orthonormal ℝ tail)
    (hMin0 : ∀ y, FangqingCanonicalLateGateFamily.H0 c C h tail 0 ≤ FangqingCanonicalLateGateFamily.H0 c C h tail y)
    (hMin1 : ∀ y, FangqingCanonicalLateGateFamily.H1 c C h tail (Z c C h tail) ≤ FangqingCanonicalLateGateFamily.H1 c C h tail y) :
    FangqingCanonicalLateGateFamily.H0 c C h tail 0 = publicZeroNormalizer c C hRef tailRef ∧
      FangqingCanonicalLateGateFamily.H1 c C h tail (Z c C h tail) = publicOneNormalizer c C hRef tailRef := by
  have hrot := actual_paired_normalizers_are_frame_independent c.profile c.delta c.omega nt C h hRef hh hhRef
    tail tailRef ht htRef c.phi c.q (c.scale*c.barlam) c.scale c.R c.gain c.A (c.seed*c.A)
  have hz : sInf (Set.range (FangqingCanonicalLateGateFamily.H0 c C h tail)) = publicZeroNormalizer c C hRef tailRef := by
    simpa only [publicZeroNormalizer,FangqingCanonicalLateGateFamily.H0,actualInactive] using! hrot.1
  have ho : sInf (Set.range (FangqingCanonicalLateGateFamily.H1 c C h tail)) = publicOneNormalizer c C hRef tailRef := by
    simpa only [publicOneNormalizer,FangqingCanonicalLateGateFamily.H0,FangqingCanonicalLateGateFamily.H1,actualInactive,actualActive] using! hrot.2
  exact ⟨(attained_minimum_equals_infimum _ _ hMin0).trans hz,(attained_minimum_equals_infimum _ _ hMin1).trans ho⟩

def referenceHandle {dA : ℕ} (bA : OrthonormalBasis (Fin dA) ℝ A) (hA : 1 ≤ dA) : A :=
  bA ⟨0,by omega⟩

def referenceTail {dW : ℕ} (bW : OrthonormalBasis (Fin dW) ℝ W) (hW : nt+2 ≤ dW) : Fin (nt+2) → W :=
  fun j => bW (j.castLE hW)

theorem reference_handle_norm {dA : ℕ} (bA : OrthonormalBasis (Fin dA) ℝ A) (hA : 1 ≤ dA) :
    ‖referenceHandle bA hA‖ = 1 := bA.orthonormal.norm_eq_one _

theorem reference_tail_orthonormal {dW : ℕ} (bW : OrthonormalBasis (Fin dW) ℝ W) (hW : nt+2 ≤ dW) :
    Orthonormal ℝ (referenceTail bW hW) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [referenceTail,bW.inner_eq_ite,Fin.castLE_inj]

end
end FangqingActualRelayPublicNormalizers
end

section
-- Source component: PaperFirstHitEvents.lean

open MeasureTheory

namespace FangqingPaperFirstHitEvents

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingActualPaddedRelayReplies FangqingActualRelayHaarEvent FangqingActualUniformFirstHit
  FangqingActualFirstHitMeasurability FangqingAdaptiveHaarOriginal
  OriginalTwoGroupPrefixExecution OriginalTwoGroupHaarExecution

noncomputable section
set_option maxHeartbeats 3500000

variable {A B W Seed : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
  [MeasurableSpace W] [BorelSpace W] [Nontrivial W]
  {outer nt : ℕ}

def paperEarly (tau N q n : ℕ) : Prop := tau = N ∨ (n:ℝ) < (tau:ℝ)+(q:ℝ)/16-2

def paperBad (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ) (packet : Fin (outer+1))
    (query : Query Seed (AugResponse A B W outer nt) (Point A B W outer))
    (out : Seed → History (AugResponse A B W outer nt) → Point A B W outer) (N q : ℕ) :
    Set (RelayInput Seed A W outer nt) :=
  {x | realTau c C m0 m1 packet query N x ≠ virtualTau c C m0 m1 packet query N x} ∪
  (⋃ n : Fin N, {x | paperEarly (realTau c C m0 m1 packet query N x) N q n.val ∧
    ownRelayHit c C packet x.2.1 x.2.2 (FangqingActualUniformFirstHit.actualCandidate c C m0 m1 packet query out N n.castSucc x) = true}) ∪
  {x | paperEarly (realTau c C m0 m1 packet query N x) N q N ∧
    packetOutputHit c C packet x.2.1 x.2.2 (FangqingActualUniformFirstHit.actualCandidate c C m0 m1 packet query out N (Fin.last N) x) = true}

theorem real_paper_window_is_inside_discrete_safe_window (tau q n : ℕ)
    (h : (n:ℝ) < (tau:ℝ)+(q:ℝ)/16-2) : n ≤ tau+1+q/8 := by
  have hq : q ≤ 8*(q/8)+7 := by omega
  have hq' : (q:ℝ) ≤ 8*((q/8:ℕ):ℝ)+7 := by exact_mod_cast hq
  have hd : (0:ℝ) ≤ ((q/8:ℕ):ℝ) := Nat.cast_nonneg _
  by_contra hn
  have hn' : (tau:ℝ)+1+((q/8:ℕ):ℝ) < (n:ℝ) := by exact_mod_cast (lt_of_not_ge hn)
  nlinarith only [h,hq',hd,hn']

theorem paper_bad_subset_actual_stronger_bad
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ) (packet : Fin (outer+1))
    (query : Query Seed (AugResponse A B W outer nt) (Point A B W outer))
    (out : Seed → History (AugResponse A B W outer nt) → Point A B W outer) (N q : ℕ) :
    paperBad c C m0 m1 packet query out N q ⊆ actualBad c C m0 m1 packet query out N q := by
  intro x hx
  rcases hx with ((ha | hquery) | hout)
  · exact Or.inl (Or.inl ha)
  · obtain ⟨n,he,hhit⟩ := Set.mem_iUnion.mp hquery
    apply Or.inl
    apply Or.inr
    apply Set.mem_iUnion.mpr
    refine ⟨n,?_,hhit⟩
    rcases he with hnone | hearly
    · rw [hnone]
      omega
    · exact real_paper_window_is_inside_discrete_safe_window _ _ _ hearly
  · apply Or.inr
    refine ⟨?_,hout.2⟩
    rcases hout.1 with hnone | hearly
    · rw [hnone]
      omega
    · exact real_paper_window_is_inside_discrete_safe_window _ _ _ hearly

section Measurable
variable [MeasurableSpace Seed] [SecondCountableTopology A] [SecondCountableTopology W]
  [MeasurableSpace (PhysicalSpace A B W)] [BorelSpace (PhysicalSpace A B W)]
  [SecondCountableTopology (PhysicalSpace A B W)]
  [MeasurableSpace (Point A B W outer)] [BorelSpace (Point A B W outer)]
  [MeasurableSpace (Point A B W outer →L[ℝ] Point A B W outer)] [BorelSpace (Point A B W outer →L[ℝ] Point A B W outer)]

theorem paperBad_measurable
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ) (packet : Fin (outer+1))
    (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hp : ContDiff ℝ 3 c.phi)
    (query : Query Seed (AugResponse A B W outer nt) (Point A B W outer))
    (hq : ∀ n, Measurable (fun x : Seed × History (AugResponse A B W outer nt) => query n x.1 x.2))
    (out : Seed → History (AugResponse A B W outer nt) → Point A B W outer)
    (ho : Measurable (fun x : Seed × History (AugResponse A B W outer nt) => out x.1 x.2)) (N q : ℕ) :
    MeasurableSet (paperBad c C m0 m1 packet query out N q) := by
  have hr := realTau_measurable c C m0 m1 packet hd hdw hp query hq N
  have hv := virtualTau_measurable c C m0 m1 packet hd hdw hp query hq N
  have hrR : Measurable (fun x => (realTau c C m0 m1 packet query N x : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp hr
  have he (n : ℕ) : MeasurableSet {x : RelayInput Seed A W outer nt | paperEarly (realTau c C m0 m1 packet query N x) N q n} :=
    (measurableSet_eq_fun hr measurable_const).union
      (measurableSet_lt measurable_const ((hrR.add_const ((q:ℝ)/16)).sub_const 2))
  have hh : Measurable (fun x : RelayInput Seed A W outer nt => x.2.1) := measurable_snd.fst
  have ht : Measurable (fun x : RelayInput Seed A W outer nt => x.2.2) := measurable_snd.snd
  have hquery : ∀ n : Fin N, MeasurableSet {x : RelayInput Seed A W outer nt |
      paperEarly (realTau c C m0 m1 packet query N x) N q n.val ∧
      ownRelayHit c C packet x.2.1 x.2.2 (FangqingActualUniformFirstHit.actualCandidate c C m0 m1 packet query out N n.castSucc x) = true} := by
    intro n
    have hc := actualCandidate_measurable c C m0 m1 packet hd hdw hp query hq out ho N n.castSucc
    exact (he n.val).inter (((ownRelayHit_measurable c C packet).comp (hh.prodMk (ht.prodMk hc))) (measurableSet_singleton true))
  have houtput : MeasurableSet {x : RelayInput Seed A W outer nt |
      paperEarly (realTau c C m0 m1 packet query N x) N q N ∧
      packetOutputHit c C packet x.2.1 x.2.2 (FangqingActualUniformFirstHit.actualCandidate c C m0 m1 packet query out N (Fin.last N) x) = true} := by
    have hc := actualCandidate_measurable c C m0 m1 packet hd hdw hp query hq out ho N (Fin.last N)
    exact (he N).inter (((packetOutputHit_measurable c C packet).comp (hh.prodMk (ht.prodMk hc))) (measurableSet_singleton true))
  exact ((measurableSet_eq_fun hr hv).compl.union (MeasurableSet.iUnion hquery)).union houtput

theorem every_fiber_probability_bound_gives_actual_event_conditional_bound
    {Side Frame : Type*} [MeasurableSpace Side] [MeasurableSpace Frame]
    (sigma : Measure Side) (nu : Measure Frame) [IsProbabilityMeasure sigma] [IsProbabilityMeasure nu]
    (bad : Set (Side × Frame)) (hbad : MeasurableSet bad) (zeta : ℝ)
    (hbound : ∀ s : Side, nu.real (Prod.mk s ⁻¹' bad) ≤ zeta) :
    ∀ᵐ x ∂sigma.prod nu,
      (sigma.prod nu)[bad.indicator (fun _ => (1:ℝ)) |
        MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Side)] x ≤ zeta := by
  apply FangqingConditionalFrameFibers.uniform_fiber_bound_gives_side_conditional_bound sigma nu _
    ((measurable_const.indicator hbad).stronglyMeasurable) ((integrable_const 1).indicator hbad) zeta
  intro s
  have hs : MeasurableSet (Prod.mk s ⁻¹' bad) := hbad.preimage measurable_prodMk_left
  have he : (fun v => bad.indicator (fun _ => (1:ℝ)) (s,v)) = (Prod.mk s ⁻¹' bad).indicator (1 : Frame → ℝ) := by
    funext v
    by_cases hv : (s,v) ∈ bad <;> simp [Set.indicator,hv]
  rw [he,integral_indicator_one hs]
  exact hbound s

end Measurable
end
end FangqingPaperFirstHitEvents
end

section
-- Source component: PrivateHandleFirstHit.lean

open MeasureTheory
open scoped NNReal

namespace FangqingPrivateHandleFirstHit

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingActualPaddedRelayReplies FangqingActualRelayHaarEvent FangqingActualUniformFirstHit
  FangqingActualFirstHitOriginalDimension FangqingActualRelayPublicNormalizers
  FangqingHierarchyFirstHitPacketGeometry FangqingHierarchyLateGateWorldFactory FangqingHierarchyAlignment
  FangqingActualRelayScaling FangqingThirdGroupScaling FangqingAdaptiveHaarOriginal FangqingPaperFirstHitEvents OriginalTwoGroupPrefixExecution
  OriginalTwoGroupHaarExecution OriginalPacketOrientationNormalization OriginalPacketDistanceGapBounds

noncomputable section
set_option maxHeartbeats 7000000

universe u v

section Guarantee

variable {A B W : Type u}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
  [MeasurableSpace W] [BorelSpace W] [Nontrivial W]
  [SecondCountableTopology A] [SecondCountableTopology W]
  [MeasurableSpace (PhysicalSpace A B W)] [BorelSpace (PhysicalSpace A B W)]
  [SecondCountableTopology (PhysicalSpace A B W)]
  {outer nt dA dW : ℕ}
  [MeasurableSpace (Point A B W outer)] [BorelSpace (Point A B W outer)]
  [MeasurableSpace (Point A B W outer →L[ℝ] Point A B W outer)] [BorelSpace (Point A B W outer →L[ℝ] Point A B W outer)]

def AllAlgorithms (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B)
    (m0 m1 : Fin (outer+1) → ℝ) (q : ℕ) (CD : ℝ)
    (bA : OrthonormalBasis (Fin dA) ℝ A) (hA : 1 ≤ dA)
    (bW : OrthonormalBasis (Fin dW) ℝ W) (hW : nt+2 ≤ dW) : Prop :=
  ∀ (Seed : Type v) [MeasurableSpace Seed] (packet : Fin (outer+1))
    (query : Query Seed (AugResponse A B W outer nt) (Point A B W outer))
    (out : Seed → History (AugResponse A B W outer nt) → Point A B W outer),
    (∀ n, Measurable (fun x : Seed × History (AugResponse A B W outer nt) => query n x.1 x.2)) →
    Measurable (fun x : Seed × History (AugResponse A B W outer nt) => out x.1 x.2) →
    ∀ (Npaid : ℕ) (zeta : ℝ), 0 < zeta → zeta ≤ 1 →
    CD*(q:ℝ)^3*Real.log (CD*((Npaid:ℝ)+2)*(q:ℝ)/zeta) ≤ ((dA-1:ℕ):ℝ) →
    CD*(q:ℝ)^3*Real.log (CD*((Npaid:ℝ)+2)*(q:ℝ)/zeta) ≤ ((dW-(nt+2):ℕ):ℝ) →
    ∀ (sigma : Measure (Seed × Parameters A W outer nt)) [IsProbabilityMeasure sigma],
    let nu := (frameLaw bA hA).prod (frameLaw bW hW)
    (∀ s : Seed × Parameters A W outer nt,
      nu.real (Prod.mk s ⁻¹' paperBad c C m0 m1 packet query out (Npaid+1) q) ≤ zeta) ∧
    ∀ᵐ x ∂packetLaw sigma bA hA bW hW,
      (packetLaw sigma bA hA bW hW)[(paperBad c C m0 m1 packet query out (Npaid+1) q).indicator (fun _ => (1:ℝ)) |
        MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace (Seed × Parameters A W outer nt))] x ≤ zeta

end Guarantee

theorem original_uniform_conditional_first_hit
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw : ℝ)
    (hCm : 1 ≤ Cm) (hCw : 4*(Cm+2) ≤ Cw)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left)
    (hr : ∀ t, Bp < t → phi t = right) (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ Ce : ℝ≥0, 1 ≤ Ce ∧ ∃ K Ks KD csigma Cdelta cL cq cg cT CD : ℝ,
      0 ≤ K ∧ 0 ≤ Ks ∧ 1 ≤ KD ∧ 0 < csigma ∧ 0 ≤ Cdelta ∧
      0 < cL ∧ cL ≤ 1/256 ∧ 0 < cq ∧ cq ≤ 1 ∧ 0 < cg ∧ cg ≤ 1 ∧ 0 < cT ∧ 1 ≤ CD ∧
      AlignmentAvailable cq cL Cw cg KD ∧
      ∀ (A B W : Type u)
        [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
        [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
        [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
        [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
        [MeasurableSpace W] [BorelSpace W] [Nontrivial W]
        [SecondCountableTopology A] [SecondCountableTopology W]
        [MeasurableSpace (PhysicalSpace A B W)] [BorelSpace (PhysicalSpace A B W)]
        [SecondCountableTopology (PhysicalSpace A B W)],
      ∀ (nt : ℕ) (C : A ≃ₗᵢ[ℝ] B) (L mu eps r rhop omega : ℝ) (q : ℕ),
      0 < L → 0 < mu → 0 < eps → 1 ≤ r → 0 < rhop → rhop ≤ rho L mu eps r →
      8 ≤ q → q ≤ nt+2 → (q:ℝ)^2 ≤ cq^2*(L/mu) → 0 < omega → ((nt+2:ℕ):ℝ) ≤ Cm*(q:ℝ) →
      omega = Cw*((8*(2*mu))/(cg*rhop))*(q:ℝ)^2 →
      distanceScale q omega = packetD (2*cL*L) (2*mu) KD eps →
      let c := originalConfig2 P phi nt Ce K Ks Cm Cw KD csigma Cdelta cL cg L mu eps r rhop q ((1/8)*omega) omega
      ∀ (dA dW : ℕ) (bA : OrthonormalBasis (Fin dA) ℝ A) (hA : 1 ≤ dA)
        (bW : OrthonormalBasis (Fin dW) ℝ W) (hW : nt+2 ≤ dW),
      let hRef := referenceHandle bA hA
      let tailRef := referenceTail bW hW
      let mZero := publicZeroNormalizer c C hRef tailRef
      let mOne := publicOneNormalizer c C hRef tailRef
      (∀ (h : A) (tail : Fin (nt+2) → W), ‖h‖=1 → Orthonormal ℝ tail →
        FangqingCanonicalLateGateFamily.H0 c C h tail 0 = mZero ∧
        FangqingCanonicalLateGateFamily.H1 c C h tail (Z c C h tail) = mOne) ∧
      ∀ (outer : ℕ)
        [MeasurableSpace (Point A B W outer)] [BorelSpace (Point A B W outer)]
        [MeasurableSpace (Point A B W outer →L[ℝ] Point A B W outer)] [BorelSpace (Point A B W outer →L[ℝ] Point A B W outer)],
        AllAlgorithms.{u,v} (outer:=outer) c (fun _ => C) (fun _ => mZero) (fun _ => mOne) q CD bA hA bW hW := by
  obtain ⟨Ce,hCe,K,Ks,KD,csigma,Cdelta,cL,cq,cg,cT,hK,hKs,hKD,hcs,hCD,hcL,hcL256,hcq,hcq1,hcg,hcg1,hcT,hAlign,hGeom⟩ :=
    same_hierarchy_constants_give_all_canonical_packet_geometries.{u} P phi Bp left right Cm Cw
      (by linarith only [hCm]) hCw hp hl hr hcore
  let Cmin := 2*Cw*(Cm+2)
  let CA := 3+8*Ks*(2*Cw)+Cmin
  let CR := 4*CA+Cmin+3
  let CD := dimensionConstant CR (1/8) Cm
  have hCD1 : 1 ≤ CD := le_max_left _ _
  refine ⟨Ce,hCe,K,Ks,KD,csigma,Cdelta,cL,cq,cg,cT,CD,hK,hKs,hKD,hcs,hCD,hcL,hcL256,hcq,hcq1,hcg,hcg1,hcT,hCD1,hAlign,?_⟩
  intro A B W iA iA' iA'' iB iB' iB'' iW iW' iW'' mA bAinst nA mW bWinst nW scA scW mPhys bPhys scPhys
    nt C L mu eps r rhop omega q hL hmu heps hr hrhop hrho hq hfit hqcap hw hn homega hScale c
    dA dW bA hA bW hW hRef tailRef mZero mOne
  have hd : 0 < (1/8:ℝ)*omega := by positivity
  have hdw : (1/8:ℝ)*omega ≤ omega := by linarith only [hw]
  obtain ⟨hR,hBeta,hLam,hAmp,hEll,hCR,hClip,hShell,hPacket⟩ :=
    hGeom A B W nt C L mu eps r rhop q ((1/8)*omega) omega hL hmu heps hr hrhop hrho
      (by exact_mod_cast (show 1 ≤ q by omega)) hqcap hd hdw hn homega hScale
  have hRefNorm : ‖hRef‖=1 := reference_handle_norm bA hA
  have htRef : Orthonormal ℝ tailRef := reference_tail_orthonormal bW hW
  constructor
  · intro h tail hh ht
    have hg := hPacket h tail hh ht
    exact actual_public_normalizers_are_actual_endpoint_minima c C hRef hRefNorm tailRef htRef h hh tail ht hg.1 hg.2.1
  · intro outer mPoint bPoint mHess bHess
    intro Seed mSeed packet query out hqMeas hout Npaid zeta hz hz1 hDimA hDimW sigma probSigma
    have hActual := actual_conditional_first_hit_from_original_cubic_dimension c (fun _ : Fin (outer+1) => C)
      (fun _ => mZero) (fun _ => mOne) packet hp hR hBeta hLam hAmp q hq hfit hw hEll
      Cmin CR (1/8) Cm hCR (by norm_num) (by norm_num) hCm rfl hClip hShell hn
      (fun h tail hh ht => ⟨(hPacket h tail hh ht).2.2.1,(hPacket h tail hh ht).2.2.2⟩)
      bA hA bW hW query hqMeas out hout Npaid zeta hz hz1 hDimA hDimW sigma

    let nu := (frameLaw bA hA).prod (frameLaw bW hW)
    haveI : IsProbabilityMeasure (frameLaw bA hA) :=
      Measure.isProbabilityMeasure_map (FangqingAdaptiveHaarProduct.measurable_frame _).aemeasurable
    haveI : IsProbabilityMeasure (frameLaw bW hW) :=
      Measure.isProbabilityMeasure_map (FangqingAdaptiveHaarProduct.measurable_frame _).aemeasurable
    haveI : IsProbabilityMeasure nu := inferInstanceAs (IsProbabilityMeasure ((frameLaw bA hA).prod (frameLaw bW hW)))
    have hFiber : ∀ s : Seed × Parameters A W outer nt,
        nu.real (Prod.mk s ⁻¹' paperBad c (fun _ => C) (fun _ => mZero) (fun _ => mOne) packet query out (Npaid+1) q) ≤ zeta := by
      intro s
      have hSub := Set.preimage_mono (f:=Prod.mk s)
        (paper_bad_subset_actual_stronger_bad c (fun _ : Fin (outer+1) => C) (fun _ => mZero) (fun _ => mOne) packet query out (Npaid+1) q)
      exact (measureReal_mono hSub (by finiteness)).trans (hActual.1 s)
    have hMeas := paperBad_measurable c (fun _ : Fin (outer+1) => C) (fun _ => mZero) (fun _ => mOne) packet
      hd hdw hp query hqMeas out hout (Npaid+1) q
    exact ⟨hFiber,every_fiber_probability_bound_gives_actual_event_conditional_bound sigma nu _ hMeas zeta hFiber⟩

end
end FangqingPrivateHandleFirstHit
end

section
-- Source component: PrivateHandleFirstHitVariableC.lean

open MeasureTheory
open scoped NNReal

namespace FangqingPrivateHandleFirstHitVariableC

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingActualPaddedRelayReplies FangqingActualRelayHaarEvent FangqingActualUniformFirstHit
  FangqingActualFirstHitOriginalDimension FangqingActualRelayPublicNormalizers
  FangqingHierarchyFirstHitPacketGeometry FangqingHierarchyLateGateWorldFactory FangqingHierarchyAlignment
  FangqingPrivateHandleFirstHit FangqingActualRelayScaling FangqingThirdGroupScaling FangqingAdaptiveHaarOriginal FangqingPaperFirstHitEvents OriginalTwoGroupPrefixExecution
  OriginalTwoGroupHaarExecution OriginalPacketOrientationNormalization OriginalPacketDistanceGapBounds

noncomputable section
set_option maxHeartbeats 7000000

universe u v

theorem original_uniform_conditional_first_hit_variable_public_isometries
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw : ℝ)
    (hCm : 1 ≤ Cm) (hCw : 4*(Cm+2) ≤ Cw)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left)
    (hr : ∀ t, Bp < t → phi t = right) (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ Ce : ℝ≥0, 1 ≤ Ce ∧ ∃ K Ks KD csigma Cdelta cL cq cg cT CD : ℝ,
      0 ≤ K ∧ 0 ≤ Ks ∧ 1 ≤ KD ∧ 0 < csigma ∧ 0 ≤ Cdelta ∧
      0 < cL ∧ cL ≤ 1/256 ∧ 0 < cq ∧ cq ≤ 1 ∧ 0 < cg ∧ cg ≤ 1 ∧ 0 < cT ∧ 1 ≤ CD ∧
      AlignmentAvailable cq cL Cw cg KD ∧
      ∀ (A B W : Type u)
        [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
        [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
        [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
        [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
        [MeasurableSpace W] [BorelSpace W] [Nontrivial W]
        [SecondCountableTopology A] [SecondCountableTopology W]
        [MeasurableSpace (PhysicalSpace A B W)] [BorelSpace (PhysicalSpace A B W)]
        [SecondCountableTopology (PhysicalSpace A B W)],
      ∀ (nt : ℕ) (L mu eps r rhop omega : ℝ) (q : ℕ),
      0 < L → 0 < mu → 0 < eps → 1 ≤ r → 0 < rhop → rhop ≤ rho L mu eps r →
      8 ≤ q → q ≤ nt+2 → (q:ℝ)^2 ≤ cq^2*(L/mu) → 0 < omega → ((nt+2:ℕ):ℝ) ≤ Cm*(q:ℝ) →
      omega = Cw*((8*(2*mu))/(cg*rhop))*(q:ℝ)^2 →
      distanceScale q omega = packetD (2*cL*L) (2*mu) KD eps →
      let c := originalConfig2 P phi nt Ce K Ks Cm Cw KD csigma Cdelta cL cg L mu eps r rhop q ((1/8)*omega) omega
      ∀ (dA dW : ℕ) (bA : OrthonormalBasis (Fin dA) ℝ A) (hA : 1 ≤ dA)
        (bW : OrthonormalBasis (Fin dW) ℝ W) (hW : nt+2 ≤ dW),
      let hRef := referenceHandle bA hA
      let tailRef := referenceTail bW hW
      ∀ (outer : ℕ)
        [MeasurableSpace (Point A B W outer)] [BorelSpace (Point A B W outer)]
        [MeasurableSpace (Point A B W outer →L[ℝ] Point A B W outer)] [BorelSpace (Point A B W outer →L[ℝ] Point A B W outer)]
        (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B),
      let mZero := fun t => publicZeroNormalizer c (C t) hRef tailRef
      let mOne := fun t => publicOneNormalizer c (C t) hRef tailRef
      (∀ t (h : A) (tail : Fin (nt+2) → W), ‖h‖=1 → Orthonormal ℝ tail →
        FangqingCanonicalLateGateFamily.H0 c (C t) h tail 0 = mZero t ∧
        FangqingCanonicalLateGateFamily.H1 c (C t) h tail (Z c (C t) h tail) = mOne t) ∧
        AllAlgorithms.{u,v} (outer:=outer) c C mZero mOne q CD bA hA bW hW := by
  obtain ⟨Ce,hCe,K,Ks,KD,csigma,Cdelta,cL,cq,cg,cT,hK,hKs,hKD,hcs,hCD,hcL,hcL256,hcq,hcq1,hcg,hcg1,hcT,hAlign,hGeom⟩ :=
    same_hierarchy_constants_give_all_canonical_packet_geometries.{u} P phi Bp left right Cm Cw
      (by linarith only [hCm]) hCw hp hl hr hcore
  let Cmin := 2*Cw*(Cm+2)
  let CA := 3+8*Ks*(2*Cw)+Cmin
  let CR := 4*CA+Cmin+3
  let CD := dimensionConstant CR (1/8) Cm
  have hCD1 : 1 ≤ CD := le_max_left _ _
  refine ⟨Ce,hCe,K,Ks,KD,csigma,Cdelta,cL,cq,cg,cT,CD,hK,hKs,hKD,hcs,hCD,hcL,hcL256,hcq,hcq1,hcg,hcg1,hcT,hCD1,hAlign,?_⟩
  intro A B W iA iA' iA'' iB iB' iB'' iW iW' iW'' mA bAinst nA mW bWinst nW scA scW mPhys bPhys scPhys
    nt L mu eps r rhop omega q hL hmu heps hr hrhop hrho hq hfit hqcap hw hn homega hScale c
    dA dW bA hA bW hW hRef tailRef outer mPoint bPoint mHess bHess C mZero mOne
  have hd : 0 < (1/8:ℝ)*omega := by positivity
  have hdw : (1/8:ℝ)*omega ≤ omega := by linarith only [hw]
  obtain ⟨hR,hBeta,hLam,hAmp,hEll,hCR,hClip,hShell,hPacket⟩ :=
    hGeom A B W nt (C 0) L mu eps r rhop q ((1/8)*omega) omega hL hmu heps hr hrhop hrho
      (by exact_mod_cast (show 1 ≤ q by omega)) hqcap hd hdw hn homega hScale
  have packetData (t : Fin (outer+1)) :=
    hGeom A B W nt (C t) L mu eps r rhop q ((1/8)*omega) omega hL hmu heps hr hrhop hrho
      (by exact_mod_cast (show 1 ≤ q by omega)) hqcap hd hdw hn homega hScale
  have hRefNorm : ‖hRef‖=1 := reference_handle_norm bA hA
  have htRef : Orthonormal ℝ tailRef := reference_tail_orthonormal bW hW
  constructor
  · intro t h tail hh ht
    obtain ⟨_,_,_,_,_,_,_,_,hData⟩ := packetData t
    have hg := hData h tail hh ht
    exact actual_public_normalizers_are_actual_endpoint_minima c (C t) hRef hRefNorm tailRef htRef h hh tail ht hg.1 hg.2.1
  · intro Seed mSeed packet query out hqMeas hout Npaid zeta hz hz1 hDimA hDimW sigma probSigma
    obtain ⟨_,_,_,_,_,_,_,_,hData⟩ := packetData packet
    have hActual := actual_conditional_first_hit_from_original_cubic_dimension c C
      mZero mOne packet hp hR hBeta hLam hAmp q hq hfit hw hEll
      Cmin CR (1/8) Cm hCR (by norm_num) (by norm_num) hCm rfl hClip hShell hn
      (fun h tail hh ht => ⟨(hData h tail hh ht).2.2.1,(hData h tail hh ht).2.2.2⟩)
      bA hA bW hW query hqMeas out hout Npaid zeta hz hz1 hDimA hDimW sigma

    let nu := (frameLaw bA hA).prod (frameLaw bW hW)
    haveI : IsProbabilityMeasure (frameLaw bA hA) :=
      Measure.isProbabilityMeasure_map (FangqingAdaptiveHaarProduct.measurable_frame _).aemeasurable
    haveI : IsProbabilityMeasure (frameLaw bW hW) :=
      Measure.isProbabilityMeasure_map (FangqingAdaptiveHaarProduct.measurable_frame _).aemeasurable
    haveI : IsProbabilityMeasure nu := inferInstanceAs (IsProbabilityMeasure ((frameLaw bA hA).prod (frameLaw bW hW)))
    have hFiber : ∀ s : Seed × Parameters A W outer nt,
        nu.real (Prod.mk s ⁻¹' paperBad c C mZero mOne packet query out (Npaid+1) q) ≤ zeta := by
      intro s
      have hSub := Set.preimage_mono (f:=Prod.mk s)
        (paper_bad_subset_actual_stronger_bad c C mZero mOne packet query out (Npaid+1) q)
      exact (measureReal_mono hSub (by finiteness)).trans (hActual.1 s)
    have hMeas := paperBad_measurable c C mZero mOne packet
      hd hdw hp query hqMeas out hout (Npaid+1) q
    exact ⟨hFiber,every_fiber_probability_bound_gives_actual_event_conditional_bound sigma nu _ hMeas zeta hFiber⟩


end
end FangqingPrivateHandleFirstHitVariableC
end

section
-- Source component: OriginalFirstHitClockFacts.lean

open scoped BigOperators

namespace FangqingOriginalFirstHitClockFacts

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingActualPaddedRelayReplies FangqingActualUniformFirstHit FangqingStoppedUniformFirstHit
  OriginalPrefixOracleReplay OriginalTwoGroupPrefixExecution FangqingFirstActivationEarlyCount
  FangqingStoppedTwoGroupReplay

noncomputable section

variable {A B W Seed : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {outer nt : ℕ}

theorem actual_first_packet_query_activation_is_zero
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (query : OriginalTwoGroupPrefixExecution.Query Seed (AugResponse A B W outer nt) (Point A B W outer))
    (N : ℕ) (x : OriginalTwoGroupPrefixExecution.Input Seed (Parameters A W outer nt) A W (nt+2)) :
    realTau c C m0 m1 0 query (N+1) x = 0 := by
  simp [realTau,realActivationUntil,firstHitUntil,activation,fullRun]

theorem virtual_first_packet_query_activation_is_zero
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (query : OriginalTwoGroupPrefixExecution.Query Seed (AugResponse A B W outer nt) (Point A B W outer))
    (N : ℕ) (x : OriginalTwoGroupPrefixExecution.Input Seed (Parameters A W outer nt) A W (nt+2)) :
    virtualTau c C m0 m1 0 query (N+1) x = 0 :=
  activation_zero_if_initial_decision query (activation c C 0) (virtualReply c C m0 m1 0) (N+1) x.1.1 x.1.2
    (by simp [activation])

theorem truncated_time_equals_horizon_iff_never_activated (N : ℕ) (decision : ℕ → Bool) :
    firstHitUntil N decision = N ↔ ∀ n < N, decision n = false := by
  constructor
  · intro h n hn
    exact before_firstHit_is_false N decision n (by rw [h]; exact hn)
  · intro h
    exact le_antisymm (firstHitUntil_le N decision) (firstHitUntil_lower_bound N N decision le_rfl h)

def paidCost (slot : ℕ) : ℕ := if slot = 0 then 0 else 1

theorem padded_clock_exact_paid_cost (N : ℕ) :
    ∑ slot : Fin (N+1), paidCost slot.val = N := by
  rw [Fin.sum_univ_succ]
  simp [paidCost]

theorem common_dimension_original_reserve_gives_handle_reserve (d m : ℕ) (hm : 1 ≤ m) :
    ((d-m:ℕ):ℝ) ≤ ((d-1:ℕ):ℝ) := by exact_mod_cast (show d-m ≤ d-1 by omega)

end
end FangqingOriginalFirstHitClockFacts
end

section
-- Source component: FirstHitAllTolerances.lean

open MeasureTheory
open scoped NNReal

namespace FangqingFirstHitAllTolerances

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingActualPaddedRelayReplies FangqingActualRelayHaarEvent FangqingActualUniformFirstHit
  FangqingActualFirstHitOriginalDimension FangqingActualRelayPublicNormalizers
  FangqingHierarchyFirstHitPacketGeometry FangqingHierarchyLateGateWorldFactory FangqingHierarchyAlignment
  FangqingPrivateHandleFirstHit FangqingPrivateHandleFirstHitVariableC FangqingActualRelayScaling FangqingThirdGroupScaling FangqingAdaptiveHaarOriginal FangqingPaperFirstHitEvents OriginalTwoGroupPrefixExecution
  OriginalTwoGroupHaarExecution OriginalPacketOrientationNormalization OriginalPacketDistanceGapBounds

noncomputable section
set_option maxHeartbeats 7000000

universe u v

section Guarantee

variable {A B W : Type u}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
  [MeasurableSpace W] [BorelSpace W] [Nontrivial W]
  [SecondCountableTopology A] [SecondCountableTopology W]
  [MeasurableSpace (PhysicalSpace A B W)] [BorelSpace (PhysicalSpace A B W)]
  [SecondCountableTopology (PhysicalSpace A B W)]
  {outer nt dA dW : ℕ}
  [MeasurableSpace (Point A B W outer)] [BorelSpace (Point A B W outer)]
  [MeasurableSpace (Point A B W outer →L[ℝ] Point A B W outer)] [BorelSpace (Point A B W outer →L[ℝ] Point A B W outer)]

def AllTolerances (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B)
    (m0 m1 : Fin (outer+1) → ℝ) (q : ℕ) (CD : ℝ)
    (bA : OrthonormalBasis (Fin dA) ℝ A) (hA : 1 ≤ dA)
    (bW : OrthonormalBasis (Fin dW) ℝ W) (hW : nt+2 ≤ dW) : Prop :=
  ∀ (Seed : Type v) [MeasurableSpace Seed] (packet : Fin (outer+1))
    (query : Query Seed (AugResponse A B W outer nt) (Point A B W outer))
    (out : Seed → History (AugResponse A B W outer nt) → Point A B W outer),
    (∀ n, Measurable (fun x : Seed × History (AugResponse A B W outer nt) => query n x.1 x.2)) →
    Measurable (fun x : Seed × History (AugResponse A B W outer nt) => out x.1 x.2) →
    ∀ (Npaid : ℕ) (zeta : ℝ), 0 < zeta →
    CD*(q:ℝ)^3*Real.log (CD*((Npaid:ℝ)+2)*(q:ℝ)/zeta) ≤ ((dA-1:ℕ):ℝ) →
    CD*(q:ℝ)^3*Real.log (CD*((Npaid:ℝ)+2)*(q:ℝ)/zeta) ≤ ((dW-(nt+2):ℕ):ℝ) →
    ∀ (sigma : Measure (Seed × Parameters A W outer nt)) [IsProbabilityMeasure sigma],
    let nu := (frameLaw bA hA).prod (frameLaw bW hW)
    (∀ s : Seed × Parameters A W outer nt,
      nu.real (Prod.mk s ⁻¹' paperBad c C m0 m1 packet query out (Npaid+1) q) ≤ zeta) ∧
    ∀ᵐ x ∂packetLaw sigma bA hA bW hW,
      (packetLaw sigma bA hA bW hW)[(paperBad c C m0 m1 packet query out (Npaid+1) q).indicator (fun _ => (1:ℝ)) |
        MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace (Seed × Parameters A W outer nt))] x ≤ zeta


theorem all_tolerances_from_small_tolerances
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ) (q : ℕ) (CD : ℝ)
    (bA : OrthonormalBasis (Fin dA) ℝ A) (hA : 1 ≤ dA)
    (bW : OrthonormalBasis (Fin dW) ℝ W) (hW : nt+2 ≤ dW)
    (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hp : ContDiff ℝ 3 c.phi)
    (hSmall : FangqingPrivateHandleFirstHit.AllAlgorithms.{u,v} c C m0 m1 q CD bA hA bW hW) :
    AllTolerances.{u,v} c C m0 m1 q CD bA hA bW hW := by
  intro Seed mSeed packet query out hq ho Npaid zeta hz hDimA hDimW sigma pSigma
  by_cases hz1 : zeta ≤ 1
  · exact hSmall Seed packet query out hq ho Npaid zeta hz hz1 hDimA hDimW sigma
  · let nu := (frameLaw bA hA).prod (frameLaw bW hW)
    haveI : IsProbabilityMeasure (frameLaw bA hA) :=
      Measure.isProbabilityMeasure_map (FangqingAdaptiveHaarProduct.measurable_frame _).aemeasurable
    haveI : IsProbabilityMeasure (frameLaw bW hW) :=
      Measure.isProbabilityMeasure_map (FangqingAdaptiveHaarProduct.measurable_frame _).aemeasurable
    haveI : IsProbabilityMeasure nu := inferInstanceAs (IsProbabilityMeasure ((frameLaw bA hA).prod (frameLaw bW hW)))
    have hf : ∀ s : Seed × Parameters A W outer nt,
        nu.real (Prod.mk s ⁻¹' paperBad c C m0 m1 packet query out (Npaid+1) q) ≤ zeta := by
      intro s
      exact (measureReal_le_one (μ:=nu) (s:=Prod.mk s ⁻¹' paperBad c C m0 m1 packet query out (Npaid+1) q)).trans
        (le_of_not_ge hz1)
    exact ⟨hf,every_fiber_probability_bound_gives_actual_event_conditional_bound sigma nu _
      (paperBad_measurable c C m0 m1 packet hd hdw hp query hq out ho (Npaid+1) q) zeta hf⟩

end Guarantee

theorem original_uniform_conditional_first_hit_all_tolerances
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw : ℝ)
    (hCm : 1 ≤ Cm) (hCw : 4*(Cm+2) ≤ Cw)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left)
    (hr : ∀ t, Bp < t → phi t = right) (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ Ce : ℝ≥0, 1 ≤ Ce ∧ ∃ K Ks KD csigma Cdelta cL cq cg cT CD : ℝ,
      0 ≤ K ∧ 0 ≤ Ks ∧ 1 ≤ KD ∧ 0 < csigma ∧ 0 ≤ Cdelta ∧
      0 < cL ∧ cL ≤ 1/256 ∧ 0 < cq ∧ cq ≤ 1 ∧ 0 < cg ∧ cg ≤ 1 ∧ 0 < cT ∧ 1 ≤ CD ∧
      AlignmentAvailable cq cL Cw cg KD ∧
      ∀ (A B W : Type u)
        [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
        [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
        [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
        [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
        [MeasurableSpace W] [BorelSpace W] [Nontrivial W]
        [SecondCountableTopology A] [SecondCountableTopology W]
        [MeasurableSpace (PhysicalSpace A B W)] [BorelSpace (PhysicalSpace A B W)]
        [SecondCountableTopology (PhysicalSpace A B W)],
      ∀ (nt : ℕ) (L mu eps r rhop omega : ℝ) (q : ℕ),
      0 < L → 0 < mu → 0 < eps → 1 ≤ r → 0 < rhop → rhop ≤ rho L mu eps r →
      8 ≤ q → q ≤ nt+2 → (q:ℝ)^2 ≤ cq^2*(L/mu) → 0 < omega → ((nt+2:ℕ):ℝ) ≤ Cm*(q:ℝ) →
      omega = Cw*((8*(2*mu))/(cg*rhop))*(q:ℝ)^2 →
      distanceScale q omega = packetD (2*cL*L) (2*mu) KD eps →
      let c := originalConfig2 P phi nt Ce K Ks Cm Cw KD csigma Cdelta cL cg L mu eps r rhop q ((1/8)*omega) omega
      ∀ (dA dW : ℕ) (bA : OrthonormalBasis (Fin dA) ℝ A) (hA : 1 ≤ dA)
        (bW : OrthonormalBasis (Fin dW) ℝ W) (hW : nt+2 ≤ dW),
      let hRef := referenceHandle bA hA
      let tailRef := referenceTail bW hW
      ∀ (outer : ℕ)
        [MeasurableSpace (Point A B W outer)] [BorelSpace (Point A B W outer)]
        [MeasurableSpace (Point A B W outer →L[ℝ] Point A B W outer)] [BorelSpace (Point A B W outer →L[ℝ] Point A B W outer)]
        (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B),
      let mZero := fun t => publicZeroNormalizer c (C t) hRef tailRef
      let mOne := fun t => publicOneNormalizer c (C t) hRef tailRef
      (∀ t (h : A) (tail : Fin (nt+2) → W), ‖h‖=1 → Orthonormal ℝ tail →
        FangqingCanonicalLateGateFamily.H0 c (C t) h tail 0 = mZero t ∧
        FangqingCanonicalLateGateFamily.H1 c (C t) h tail (Z c (C t) h tail) = mOne t) ∧
        AllTolerances.{u,v} (outer:=outer) c C mZero mOne q CD bA hA bW hW := by
  obtain ⟨Ce,hCe,K,Ks,KD,csigma,Cdelta,cL,cq,cg,cT,CD,hK,hKs,hKD,hcs,hCD,hcL,hcL256,hcq,hcq1,hcg,hcg1,hcT,hCD1,hAlign,hModel⟩ :=
    original_uniform_conditional_first_hit_variable_public_isometries.{u,v} P phi Bp left right Cm Cw hCm hCw hp hl hr hcore
  refine ⟨Ce,hCe,K,Ks,KD,csigma,Cdelta,cL,cq,cg,cT,CD,hK,hKs,hKD,hcs,hCD,hcL,hcL256,hcq,hcq1,hcg,hcg1,hcT,hCD1,hAlign,?_⟩
  intro A B W iA iA' iA'' iB iB' iB'' iW iW' iW'' mA bAinst nA mW bWinst nW scA scW mPhys bPhys scPhys
    nt L mu eps r rhop omega q hL hmu heps hr hrhop hrho hq hfit hqcap hw hn homega hScale c
    dA dW bA hA bW hW hRef tailRef outer mPoint bPoint mHess bHess C mZero mOne
  have hthis := hModel A B W nt L mu eps r rhop omega q hL hmu heps hr hrhop hrho hq hfit hqcap hw hn homega hScale
    dA dW bA hA bW hW outer C
  exact ⟨hthis.1,all_tolerances_from_small_tolerances c C mZero mOne q CD bA hA bW hW
    (by change 0 < (1/8:ℝ)*omega; positivity)
    (by change (1/8:ℝ)*omega ≤ omega; linarith only [hw]) hp hthis.2⟩

end
end FangqingFirstHitAllTolerances
end

section
-- Source component: FinitePacketProductTransport.lean

open MeasureTheory

namespace OriginalFinitePacketProductTransport
noncomputable section
set_option maxHeartbeats 3000000

variable {Seed Frame : Type*} [MeasurableSpace Seed] [MeasurableSpace Frame]

def shuffle {Rest : Type*} [MeasurableSpace Rest] :
    Seed × (Frame × Rest) ≃ᵐ (Seed × Rest) × Frame :=
  ((MeasurableEquiv.refl Seed).prodCongr (MeasurableEquiv.prodComm : Frame × Rest ≃ᵐ Rest × Frame)).trans
    (MeasurableEquiv.prodAssoc : (Seed × Rest) × Frame ≃ᵐ Seed × (Rest × Frame)).symm

/-- A genuine measurable coordinate permutation, keeping the seed in the side
and separating exactly one packet from a finite product of independent packets. -/
def splitEquiv {n : ℕ} (i : Fin (n+1)) :
    (Seed × (Fin (n+1) → Frame)) ≃ᵐ (Seed × (Fin n → Frame)) × Frame :=
  ((MeasurableEquiv.refl Seed).prodCongr (MeasurableEquiv.piFinSuccAbove (fun _ => Frame) i)).trans shuffle

theorem splitEquiv_apply {n : ℕ} (i : Fin (n+1)) (z : Seed × (Fin (n+1) → Frame)) :
    splitEquiv i z = ((z.1,fun j => z.2 (i.succAbove j)),z.2 i) := rfl

/-- Independence is derived from the actual finite product measure. It is not
an additional probabilistic hypothesis about the selected packet. -/
theorem split_measure_preserving {n : ℕ}
    (seeds : Measure Seed) [IsProbabilityMeasure seeds]
    (mu : Fin (n+1) → Measure Frame) [∀ j, IsProbabilityMeasure (mu j)]
    (i : Fin (n+1)) :
    MeasurePreserving (splitEquiv (Seed := Seed) (Frame := Frame) i)
      (seeds.prod (Measure.pi mu))
      ((seeds.prod (Measure.pi (fun j : Fin n => mu (i.succAbove j)))).prod (mu i)) := by
  let rest := Measure.pi (fun j : Fin n => mu (i.succAbove j))
  have h1 := (MeasurePreserving.id seeds).prod (measurePreserving_piFinSuccAbove mu i)
  have h2 := (MeasurePreserving.id seeds).prod (Measure.measurePreserving_swap (μ := mu i) (ν := rest))
  have h3 := MeasurePreserving.symm (MeasurableEquiv.prodAssoc : (Seed × (Fin n → Frame)) × Frame ≃ᵐ Seed × ((Fin n → Frame) × Frame))
    (measurePreserving_prodAssoc seeds rest (mu i))
  convert! h3.comp (h2.comp h1) using 1

theorem split_joint_law {n : ℕ}
    (seeds : Measure Seed) [IsProbabilityMeasure seeds]
    (mu : Fin (n+1) → Measure Frame) [∀ j, IsProbabilityMeasure (mu j)] (i : Fin (n+1)) :
    (seeds.prod (Measure.pi mu)).map (splitEquiv (Seed := Seed) (Frame := Frame) i) =
      (seeds.prod (Measure.pi (fun j : Fin n => mu (i.succAbove j)))).prod (mu i) :=
  (split_measure_preserving seeds mu i).map_eq

end
end OriginalFinitePacketProductTransport
end

section
-- Source component: ConditionalExpectationProductPullback.lean

open MeasureTheory

namespace OriginalConditionalExpectationPullback
noncomputable section
set_option maxHeartbeats 3000000

variable {Omega Target : Type*} [mOmega : MeasurableSpace Omega] [mTarget : MeasurableSpace Target]

/-- Pull back an actual conditional expectation along a measure-preserving
measurable embedding. The conditioning sigma field is pulled back as well; no
independence or desired conditional probability conclusion is assumed. -/
theorem condExp_pullback
    (mu : Measure Omega) (nu : Measure Target) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (e : Omega → Target) (he : MeasurableEmbedding e) (hmp : MeasurePreserving e mu nu)
    (G : MeasurableSpace Target) (hG : G ≤ mTarget) (f : Target → ℝ) (hf : Integrable f nu) :
    (fun x => nu[f | G] (e x)) =ᵐ[mu]
      mu[(fun x => f (e x)) | MeasurableSpace.comap e G] := by
  let H := MeasurableSpace.comap e G
  letI : MeasurableSpace Omega := mOmega
  letI : MeasurableSpace Target := mTarget
  have hH : H ≤ mOmega := (MeasurableSpace.comap_mono hG).trans hmp.measurable.comap_le
  have hsrc : Integrable (fun x => f (e x)) mu :=
    (hmp.integrable_comp hf.aestronglyMeasurable).mpr hf
  have hcg : StronglyMeasurable[G] (nu[f | G]) := stronglyMeasurable_condExp
  have hcg0 : StronglyMeasurable[mTarget] (nu[f | G]) := hcg.mono hG
  have hci : Integrable (nu[f | G]) nu := integrable_condExp
  have hciSrc : Integrable (fun x => nu[f | G] (e x)) mu :=
    (hmp.integrable_comp hcg0.aestronglyMeasurable).mpr hci
  have hmeas : StronglyMeasurable[H] (fun x => nu[f | G] (e x)) :=
    hcg.comp_measurable (comap_measurable e)
  refine ae_eq_condExp_of_forall_setIntegral_eq hH hsrc
    (fun s hs hfinite => hciSrc.integrableOn) ?_ hmeas.aestronglyMeasurable
  intro s hs hfinite
  obtain ⟨B,hB,rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  have hB0 : MeasurableSet B := hG B hB
  have hpre : MeasurableSet (e ⁻¹' B) := hB0.preimage hmp.measurable
  rw [← integral_indicator hpre,← integral_indicator hpre]
  have hleft : (e ⁻¹' B).indicator (fun x => nu[f | G] (e x)) =
      fun x => (B.indicator (nu[f | G])) (e x) := by
    funext x
    by_cases hx : e x ∈ B <;> simp [Set.indicator,hx]
  have hright : (e ⁻¹' B).indicator (fun x => f (e x)) =
      fun x => (B.indicator f) (e x) := by
    funext x
    by_cases hx : e x ∈ B <;> simp [Set.indicator,hx]
  rw [hleft,hright,hmp.integral_comp he,hmp.integral_comp he,
    integral_indicator hB0,integral_indicator hB0]
  exact setIntegral_condExp hG hf hB

theorem condExp_bound_pullback
    (mu : Measure Omega) (nu : Measure Target) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (e : Omega → Target) (he : MeasurableEmbedding e) (hmp : MeasurePreserving e mu nu)
    (G : MeasurableSpace Target) (hG : G ≤ mTarget) (f : Target → ℝ) (hf : Integrable f nu)
    (zeta : ℝ) (hbound : ∀ᵐ y ∂nu, nu[f | G] y ≤ zeta) :
    ∀ᵐ x ∂mu, mu[(fun x => f (e x)) | MeasurableSpace.comap e G] x ≤ zeta := by
  letI : MeasurableSpace Omega := mOmega
  letI : MeasurableSpace Target := mTarget
  have hpull := hmp.quasiMeasurePreserving.ae hbound
  filter_upwards [condExp_pullback mu nu e he hmp G hG f hf,hpull] with x hx hb
  rw [← hx]
  exact hb

end
end OriginalConditionalExpectationPullback
end

section
-- Source component: FinitePacketSideEncoding.lean

open MeasureTheory

namespace OriginalFinitePacketProductTransport
noncomputable section
set_option maxHeartbeats 3000000

variable {Seed Frame Side : Type*} [MeasurableSpace Seed] [MeasurableSpace Frame] [MeasurableSpace Side]

def encodedSplit {n : ℕ} (i : Fin (n+1)) (encode : Seed × (Fin n → Frame) → Side)
    (z : Seed × (Fin (n+1) → Frame)) : Side × Frame :=
  (encode (splitEquiv i z).1,(splitEquiv i z).2)

def encodedSideLaw {n : ℕ} (seeds : Measure Seed) (mu : Fin (n+1) → Measure Frame)
    (i : Fin (n+1)) (encode : Seed × (Fin n → Frame) → Side) : Measure Side :=
  (seeds.prod (Measure.pi (fun j : Fin n => mu (i.succAbove j)))).map encode

theorem encoded_split_measure_preserving {n : ℕ}
    (seeds : Measure Seed) [IsProbabilityMeasure seeds]
    (mu : Fin (n+1) → Measure Frame) [∀ j, IsProbabilityMeasure (mu j)] (i : Fin (n+1))
    (encode : Seed × (Fin n → Frame) → Side) (hencode : Measurable encode) :
    MeasurePreserving (encodedSplit i encode) (seeds.prod (Measure.pi mu))
      ((encodedSideLaw seeds mu i encode).prod (mu i)) := by
  let sigma := seeds.prod (Measure.pi (fun j : Fin n => mu (i.succAbove j)))
  have hm : MeasurePreserving encode sigma (sigma.map encode) := ⟨hencode,rfl⟩
  exact (hm.prod (MeasurePreserving.id (mu i))).comp (split_measure_preserving seeds mu i)

theorem encoded_split_measurableEmbedding {n : ℕ} (i : Fin (n+1))
    (encode : Seed × (Fin n → Frame) → Side) (hencode : MeasurableEmbedding encode) :
    MeasurableEmbedding (encodedSplit i encode) :=
  (hencode.prodMap MeasurableEmbedding.id).comp (splitEquiv i).measurableEmbedding

theorem encoded_side_law_probability {n : ℕ}
    (seeds : Measure Seed) [IsProbabilityMeasure seeds]
    (mu : Fin (n+1) → Measure Frame) [∀ j, IsProbabilityMeasure (mu j)] (i : Fin (n+1))
    (encode : Seed × (Fin n → Frame) → Side) (hencode : Measurable encode) :
    IsProbabilityMeasure (encodedSideLaw seeds mu i encode) :=
  Measure.isProbabilityMeasure_map hencode.aemeasurable

section ZeroFill
variable [Zero Frame] [MeasurableSingletonClass Frame]

def fillZero {n : ℕ} (i : Fin (n+1)) (rest : Fin n → Frame) : Fin (n+1) → Frame :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => Frame) i).symm (0,rest)

theorem fillZero_measurableEmbedding {n : ℕ} (i : Fin (n+1)) :
    MeasurableEmbedding (fillZero (Frame := Frame) i) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => Frame) i).symm.measurableEmbedding.comp
    (measurableEmbedding_prodMk_left (0 : Frame))

theorem fillZero_at_selected {n : ℕ} (i : Fin (n+1)) (rest : Fin n → Frame) :
    fillZero i rest i = 0 := by
  simp [fillZero, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

theorem fillZero_at_other {n : ℕ} (i : Fin (n+1)) (rest : Fin n → Frame) (j : Fin n) :
    fillZero i rest (i.succAbove j) = rest j := by
  simp [fillZero, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

variable {Param : Type*} [MeasurableSpace Param]

def encodeSide {n : ℕ} (i : Fin (n+1)) (equiv : Frame ≃ᵐ Param)
    (s : Seed × (Fin n → Frame)) : Seed × (Fin (n+1) → Param) :=
  (s.1,fun j => equiv (fillZero i s.2 j))

theorem encodeSide_measurableEmbedding {n : ℕ} (i : Fin (n+1)) (equiv : Frame ≃ᵐ Param) :
    MeasurableEmbedding (encodeSide (Seed := Seed) i equiv) := by
  have h := (MeasurableEquiv.piCongrRight (fun _ : Fin (n+1) => equiv)).measurableEmbedding.comp
    (fillZero_measurableEmbedding (Frame := Frame) i)
  exact MeasurableEmbedding.id.prodMap h

theorem encodedSplit_selected_side_placeholder {n : ℕ} (i : Fin (n+1)) (equiv : Frame ≃ᵐ Param)
    (z : Seed × (Fin (n+1) → Frame)) :
    (encodedSplit i (encodeSide i equiv) z).1.2 i = equiv 0 := by
  exact congrArg equiv (fillZero_at_selected i _)

theorem encodedSplit_other_side_coordinates {n : ℕ} (i : Fin (n+1)) (equiv : Frame ≃ᵐ Param)
    (z : Seed × (Fin (n+1) → Frame)) (j : Fin n) :
    (encodedSplit i (encodeSide i equiv) z).1.2 (i.succAbove j) = equiv (z.2 (i.succAbove j)) := by
  exact congrArg equiv (fillZero_at_other i _ j)

end ZeroFill
end
end OriginalFinitePacketProductTransport
end

section
-- Source component: FinitePacketConditionalTransport.lean

open MeasureTheory

namespace OriginalFinitePacketProductTransport
noncomputable section
set_option maxHeartbeats 3000000

variable {Seed Frame Side : Type*} [MeasurableSpace Seed] [MeasurableSpace Frame] [MeasurableSpace Side]

/-- Transport the already-proved per-side product CE to the original complete
finite-product world. The conditioning sigma field is literally generated by the
encoded side coordinates. The actual full product law, not an independence
premise, supplies the joint law used by the transport. -/
theorem encoded_conditional_event_bound {n : ℕ}
    (seeds : Measure Seed) [IsProbabilityMeasure seeds]
    (mu : Fin (n+1) → Measure Frame) [∀ j, IsProbabilityMeasure (mu j)] (i : Fin (n+1))
    (encode : Seed × (Fin n → Frame) → Side) (hencode : MeasurableEmbedding encode)
    (bad : Set (Side × Frame)) (hbad : MeasurableSet bad) (zeta : ℝ)
    (hbound : ∀ᵐ p ∂(encodedSideLaw seeds mu i encode).prod (mu i),
      ((encodedSideLaw seeds mu i encode).prod (mu i))[
        bad.indicator (fun _ => (1:ℝ)) |
        MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Side)] p ≤ zeta) :
    ∀ᵐ z ∂seeds.prod (Measure.pi mu),
      (seeds.prod (Measure.pi mu))[
        ((encodedSplit i encode) ⁻¹' bad).indicator (fun _ => (1:ℝ)) |
        MeasurableSpace.comap (fun z => (encodedSplit i encode z).1)
          (inferInstance : MeasurableSpace Side)] z ≤ zeta := by
  haveI : IsProbabilityMeasure (encodedSideLaw seeds mu i encode) :=
    encoded_side_law_probability seeds mu i encode hencode.measurable
  have hf : Integrable (bad.indicator (fun _ => (1:ℝ)))
      ((encodedSideLaw seeds mu i encode).prod (mu i)) :=
    (integrable_const 1).indicator hbad
  have h := OriginalConditionalExpectationPullback.condExp_bound_pullback
    (seeds.prod (Measure.pi mu)) ((encodedSideLaw seeds mu i encode).prod (mu i))
    (encodedSplit i encode) (encoded_split_measurableEmbedding i encode hencode)
    (encoded_split_measure_preserving seeds mu i encode hencode.measurable)
    (MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Side))
    measurable_fst.comap_le (bad.indicator (fun _ => (1:ℝ))) hf zeta hbound
  have heq : (fun z => bad.indicator (fun _ => (1:ℝ)) (encodedSplit i encode z)) =
      ((encodedSplit i encode) ⁻¹' bad).indicator (fun _ => (1:ℝ)) := by
    funext z
    by_cases hz : encodedSplit i encode z ∈ bad <;> simp [Set.indicator,hz]
  rw [heq] at h
  simpa only [MeasurableSpace.comap_comp,Function.comp_def] using h

end
end OriginalFinitePacketProductTransport
end

section
-- Source component: OriginalPacketWorldTransportV2.lean

open MeasureTheory

namespace FangqingOriginalPacketWorld
noncomputable section
set_option maxHeartbeats 3000000

variable {Seed A W : Type*} [MeasurableSpace Seed] [MeasurableSpace A] [MeasurableSpace W]

abbrev OwnFrame (A W : Type*) (nt : ℕ) := (Fin 1 → A) × (Fin (nt+2) → W)
abbrev RawPacket (A W : Type*) (nt : ℕ) := A × (Fin (nt+2) → W)
abbrev World (Seed A W : Type*) (outer nt : ℕ) := Seed × (Fin (outer+1) → OwnFrame A W nt)
abbrev Side (Seed A W : Type*) (outer nt : ℕ) := Seed × (Fin (outer+1) → RawPacket A W nt)
abbrev PacketInput (Seed A W : Type*) (outer nt : ℕ) := Side Seed A W outer nt × OwnFrame A W nt

/-- The actual handle frame has exactly one column; the physical parameter is its
column zero together with the same independent tail frame. -/
def frameParameterEquiv (nt : ℕ) : OwnFrame A W nt ≃ᵐ RawPacket A W nt :=
  (MeasurableEquiv.funUnique (Fin 1) A).prodCongr (MeasurableEquiv.refl (Fin (nt+2) → W))

theorem frameParameterEquiv_apply (nt : ℕ) (frame : OwnFrame A W nt) :
    frameParameterEquiv nt frame = (frame.1 0,frame.2) := rfl

variable [Zero A] [Zero W] [MeasurableSingletonClass A] [MeasurableSingletonClass W]

def sideEncoder {outer nt : ℕ} (packet : Fin (outer+1)) :
    Seed × (Fin outer → OwnFrame A W nt) → Side Seed A W outer nt :=
  OriginalFinitePacketProductTransport.encodeSide packet (frameParameterEquiv nt)

def worldToPacket {outer nt : ℕ} (packet : Fin (outer+1)) :
    World Seed A W outer nt → PacketInput Seed A W outer nt :=
  OriginalFinitePacketProductTransport.encodedSplit packet (sideEncoder packet)

def sideLaw {outer nt : ℕ} (seeds : Measure Seed)
    (laws : Fin (outer+1) → Measure (OwnFrame A W nt)) (packet : Fin (outer+1)) :
    Measure (Side Seed A W outer nt) :=
  OriginalFinitePacketProductTransport.encodedSideLaw seeds laws packet (sideEncoder packet)

theorem sideEncoder_measurableEmbedding {outer nt : ℕ} (packet : Fin (outer+1)) :
    MeasurableEmbedding (sideEncoder (Seed := Seed) (A := A) (W := W) (nt := nt) packet) :=
  OriginalFinitePacketProductTransport.encodeSide_measurableEmbedding packet (frameParameterEquiv nt)

theorem worldToPacket_measurableEmbedding {outer nt : ℕ} (packet : Fin (outer+1)) :
    MeasurableEmbedding (worldToPacket (Seed := Seed) (A := A) (W := W) (nt := nt) packet) :=
  OriginalFinitePacketProductTransport.encoded_split_measurableEmbedding packet _
    (sideEncoder_measurableEmbedding packet)

/-- The original random seed is retained literally and never replaced by a
frame-dependent input. -/
theorem seed_coordinate {outer nt : ℕ} (packet : Fin (outer+1))
    (z : World Seed A W outer nt) : (worldToPacket packet z).1.1 = z.1 := rfl

theorem own_coordinate {outer nt : ℕ} (packet : Fin (outer+1))
    (z : World Seed A W outer nt) : (worldToPacket packet z).2 = z.2 packet := rfl

theorem selected_side_coordinate_is_zero {outer nt : ℕ} (packet : Fin (outer+1))
    (z : World Seed A W outer nt) : (worldToPacket packet z).1.2 packet = 0 := by
  exact OriginalFinitePacketProductTransport.encodedSplit_selected_side_placeholder packet
    (frameParameterEquiv nt) z

theorem other_side_coordinate_is_actual {outer nt : ℕ} (packet : Fin (outer+1))
    (z : World Seed A W outer nt) (j : Fin outer) :
    (worldToPacket packet z).1.2 (packet.succAbove j) =
      ((z.2 (packet.succAbove j)).1 0,(z.2 (packet.succAbove j)).2) := by
  exact OriginalFinitePacketProductTransport.encodedSplit_other_side_coordinates packet
    (frameParameterEquiv nt) z j

theorem side_is_zero_filled_actual_parameters {outer nt : ℕ} (packet : Fin (outer+1))
    (z : World Seed A W outer nt) :
    (worldToPacket packet z).1 =
      (z.1,Function.update (fun j => ((z.2 j).1 0,(z.2 j).2)) packet 0) := by
  apply Prod.ext (seed_coordinate packet z)
  apply funext
  refine packet.forall_iff_succAbove.mpr ⟨?_,?_⟩
  · simpa only [Function.update_self] using selected_side_coordinate_is_zero packet z
  · intro k
    simpa only [Function.update_of_ne (Fin.succAbove_ne packet k)] using
      other_side_coordinate_is_actual packet z k

/-- Derived from the original seed-times-finite-Pi product law. This is not an
assumed independence premise. Every packet law can in particular be its actual
independent handle-Haar times tail-Haar law. -/
theorem original_world_packet_joint_law {outer nt : ℕ}
    (seeds : Measure Seed) [IsProbabilityMeasure seeds]
    (laws : Fin (outer+1) → Measure (OwnFrame A W nt))
    [∀ j, IsProbabilityMeasure (laws j)] (packet : Fin (outer+1)) :
    MeasurePreserving (worldToPacket packet) (seeds.prod (Measure.pi laws))
      ((sideLaw seeds laws packet).prod (laws packet)) :=
  OriginalFinitePacketProductTransport.encoded_split_measure_preserving seeds laws packet _
    (sideEncoder_measurableEmbedding packet).measurable

theorem original_side_probability {outer nt : ℕ}
    (seeds : Measure Seed) [IsProbabilityMeasure seeds]
    (laws : Fin (outer+1) → Measure (OwnFrame A W nt))
    [∀ j, IsProbabilityMeasure (laws j)] (packet : Fin (outer+1)) :
    IsProbabilityMeasure (sideLaw seeds laws packet) :=
  OriginalFinitePacketProductTransport.encoded_side_law_probability seeds laws packet _
    (sideEncoder_measurableEmbedding packet).measurable

/-- Pull the independently proved per-side first-hit estimate back to the literal
original joint experiment. The sigma field is exactly that generated by the
original seed and all other physical packet frames, with own coordinate zeroed.
No assertion about the algorithm's smaller transcript sigma field is needed. -/
theorem original_world_conditional_event_bound {outer nt : ℕ}
    (seeds : Measure Seed) [IsProbabilityMeasure seeds]
    (laws : Fin (outer+1) → Measure (OwnFrame A W nt))
    [∀ j, IsProbabilityMeasure (laws j)] (packet : Fin (outer+1))
    (bad : Set (PacketInput Seed A W outer nt)) (hbad : MeasurableSet bad) (zeta : ℝ)
    (hbound : ∀ᵐ p ∂(sideLaw seeds laws packet).prod (laws packet),
      ((sideLaw seeds laws packet).prod (laws packet))[
        bad.indicator (fun _ => (1:ℝ)) |
        MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace (Side Seed A W outer nt))] p ≤ zeta) :
    ∀ᵐ z ∂seeds.prod (Measure.pi laws),
      (seeds.prod (Measure.pi laws))[
        ((worldToPacket packet) ⁻¹' bad).indicator (fun _ => (1:ℝ)) |
        MeasurableSpace.comap (fun z => (worldToPacket packet z).1)
          (inferInstance : MeasurableSpace (Side Seed A W outer nt))] z ≤ zeta := by
  exact OriginalFinitePacketProductTransport.encoded_conditional_event_bound seeds laws packet
    (sideEncoder packet) (sideEncoder_measurableEmbedding packet) bad hbad zeta hbound

end
end FangqingOriginalPacketWorld
end

section
-- Source component: OriginalWorldFirstHit.lean

open MeasureTheory

namespace FangqingOriginalWorldFirstHit

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingCanonicalSuppressedRelay FangqingActualPaddedRelayReplies FangqingActualPaddedProgramEmbedding
  FangqingPaddedPublicInputProgram FangqingPaperFirstHitEvents FangqingFirstHitAllTolerances
  FangqingAdaptiveHaarOriginal OriginalTwoGroupPrefixExecution OriginalTwoGroupHaarExecution
  FangqingOriginalPacketWorld

noncomputable section
set_option maxHeartbeats 5000000

universe u v

section LiteralWorld
variable {Seed A W : Type*} [MeasurableSpace Seed] [MeasurableSpace A] [MeasurableSpace W]
  [Zero A] [Zero W] [MeasurableSingletonClass A] [MeasurableSingletonClass W] {outer nt : ℕ}

def originalSideSigma (packet : Fin (outer+1)) : MeasurableSpace (World Seed A W outer nt) :=
  MeasurableSpace.comap (fun z : World Seed A W outer nt => (z.1,fun j : Fin outer => z.2 (packet.succAbove j))) inferInstance

theorem original_side_sigma_is_exact (packet : Fin (outer+1)) :
    MeasurableSpace.comap (fun z : World Seed A W outer nt => (worldToPacket packet z).1)
      (inferInstance : MeasurableSpace (FangqingOriginalPacketWorld.Side Seed A W outer nt)) =
      originalSideSigma packet := by
  change MeasurableSpace.comap
    ((sideEncoder packet) ∘ (fun z : World Seed A W outer nt => (z.1,fun j : Fin outer => z.2 (packet.succAbove j)))) _ = _
  rw [← MeasurableSpace.comap_comp,(sideEncoder_measurableEmbedding (Seed:=Seed) (A:=A) (W:=W) (nt:=nt) packet).comap_eq]
  rfl

def globalParameters (z : World Seed A W outer nt) : Parameters A W outer nt :=
  fun j => ((z.2 j).1 0,(z.2 j).2)

theorem true_frame_override_recovers_entire_original_instance (packet : Fin (outer+1)) (z : World Seed A W outer nt) :
    frameOverride (worldToPacket packet z).1.2 packet ((worldToPacket packet z).2.1 0,(worldToPacket packet z).2.2) =
      globalParameters z := by
  have hs := congrArg Prod.snd (side_is_zero_filled_actual_parameters packet z)
  change (worldToPacket packet z).1.2 = Function.update (globalParameters z) packet 0 at hs
  rw [hs,own_coordinate]
  funext t
  by_cases ht : t = packet
  · subst t
    simp [frameOverride,globalParameters]
  · simp only [frameOverride,Function.update_of_ne ht]

end LiteralWorld

section Algorithms
variable {A B W : Type u}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
  [MeasurableSpace W] [BorelSpace W] [Nontrivial W]
  [SecondCountableTopology A] [SecondCountableTopology W]
  [MeasurableSpace (PhysicalSpace A B W)] [BorelSpace (PhysicalSpace A B W)]
  [SecondCountableTopology (PhysicalSpace A B W)]
  {outer nt dA dW : ℕ}
  [MeasurableSpace (Point A B W outer)] [BorelSpace (Point A B W outer)]
  [MeasurableSpace (Point A B W outer →L[ℝ] Point A B W outer)] [BorelSpace (Point A B W outer →L[ℝ] Point A B W outer)]

theorem literal_real_family_is_the_original_full_instance
    {Seed : Type*} [MeasurableSpace Seed] (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B)
    (m0 m1 : Fin (outer+1) → ℝ) (packet : Fin (outer+1)) (z : World Seed A W outer nt) :
    realFamily c C m0 m1 packet (worldToPacket packet z).1.2
      ((worldToPacket packet z).2.1 0,(worldToPacket packet z).2.2) =
      FangqingCanonicalRelayParameterFamily.family c C m0 m1 (globalParameters z) := by
  unfold realFamily
  rw [true_frame_override_recovers_entire_original_instance]


theorem original_full_instance_paid_history_and_unqueried_output
    {Seed : Type*} [MeasurableSpace Seed] (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B)
    (m0 m1 : Fin (outer+1) → ℝ) (packet : Fin (outer+1))
    (query : PublicQuery Seed (Point A B W outer) (Response A B W outer) (Point A B W outer))
    (out : Seed → Point A B W outer → (ℕ → Response A B W outer) → Point A B W outer)
    (z : World Seed A W outer nt) (Npaid : ℕ) :
    let e := worldToPacket packet z
    let publicInput := publicInitialPoint (B:=B) c ((globalParameters z 0).1)
    let oracle := FangqingPreHitRelayLocality.fullReply (FangqingCanonicalRelayParameterFamily.family c C m0 m1 (globalParameters z))
    let qpad := paddedQuery query decodePublic oracleView (0 : Point A B W outer)
    let st := fullRun qpad (activation c C packet) (realReply c C m0 m1 packet) (Npaid+1) z.1 e.1.2 e.2.1 e.2.2
    decodePublic (st.2.2 0) = publicInput ∧
    paidHistory oracleView st.2.2 = ordinaryRun query oracle z.1 publicInput Npaid ∧
    paddedOutput out decodePublic oracleView z.1 st.2.2 = out z.1 publicInput (ordinaryRun query oracle z.1 publicInput Npaid) := by
  intro e publicInput oracle qpad st
  have hi : initialHandle packet e.1.2 e.2.1 e.2.2 = (globalParameters z 0).1 :=
    congrArg (fun p : Parameters A W outer nt => (p 0).1)
      (true_frame_override_recovers_entire_original_instance packet z)
  have hf : realFamily c C m0 m1 packet e.1.2 (e.2.1 0,e.2.2) =
      FangqingCanonicalRelayParameterFamily.family c C m0 m1 (globalParameters z) :=
    literal_real_family_is_the_original_full_instance c C m0 m1 packet z
  have h := actual_paid_program_and_unqueried_output_are_preserved c C m0 m1 packet query out z.1 e.1.2 e.2.1 e.2.2 Npaid
  simpa only [hi,hf] using! h

def OriginalWorldAlgorithms (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B)
    (m0 m1 : Fin (outer+1) → ℝ) (q : ℕ) (CD : ℝ)
    (bA : OrthonormalBasis (Fin dA) ℝ A) (hA : 1 ≤ dA)
    (bW : OrthonormalBasis (Fin dW) ℝ W) (hW : nt+2 ≤ dW) : Prop :=
  ∀ (Seed : Type v) [MeasurableSpace Seed] (packet : Fin (outer+1))
    (query : PublicQuery Seed (Point A B W outer) (Response A B W outer) (Point A B W outer))
    (out : Seed → Point A B W outer → (ℕ → Response A B W outer) → Point A B W outer),
    (∀ n, Measurable (fun x : Seed × Point A B W outer × (ℕ → Response A B W outer) => query n x.1 x.2.1 x.2.2)) →
    Measurable (fun x : Seed × Point A B W outer × (ℕ → Response A B W outer) => out x.1 x.2.1 x.2.2) →
    ∀ (Npaid : ℕ) (zeta : ℝ), 0 < zeta →
    CD*(q:ℝ)^3*Real.log (CD*((Npaid:ℝ)+2)*(q:ℝ)/zeta) ≤ ((dA-1:ℕ):ℝ) →
    CD*(q:ℝ)^3*Real.log (CD*((Npaid:ℝ)+2)*(q:ℝ)/zeta) ≤ ((dW-(nt+2):ℕ):ℝ) →
    ∀ (seeds : Measure Seed) [IsProbabilityMeasure seeds],
    let nu := (frameLaw bA hA).prod (frameLaw bW hW)
    let laws := fun _ : Fin (outer+1) => nu
    let bad := paperBad c C m0 m1 packet
      (paddedQuery query decodePublic oracleView (0 : Point A B W outer))
      (paddedOutput out decodePublic oracleView) (Npaid+1) q
    (∀ rawSide : Seed × (Fin outer → OwnFrame A W nt),
      nu.real (Prod.mk (sideEncoder packet rawSide) ⁻¹' bad) ≤ zeta) ∧
    ∀ᵐ z ∂seeds.prod (Measure.pi laws),
      (seeds.prod (Measure.pi laws))[
        ((worldToPacket packet) ⁻¹' bad).indicator (fun _ => (1:ℝ)) | originalSideSigma packet] z ≤ zeta

theorem all_tolerances_give_literal_original_product_world
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ) (q : ℕ) (CD : ℝ)
    (bA : OrthonormalBasis (Fin dA) ℝ A) (hA : 1 ≤ dA)
    (bW : OrthonormalBasis (Fin dW) ℝ W) (hW : nt+2 ≤ dW)
    (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hp : ContDiff ℝ 3 c.phi)
    (hCertified : AllTolerances.{u,v} c C m0 m1 q CD bA hA bW hW) :
    OriginalWorldAlgorithms.{u,v} c C m0 m1 q CD bA hA bW hW := by
  intro Seed mSeed packet query out hq ho Npaid zeta hz hDimA hDimW seeds pSeeds
  let nu := (frameLaw bA hA).prod (frameLaw bW hW)
  let laws := fun _ : Fin (outer+1) => nu
  haveI : IsProbabilityMeasure (frameLaw bA hA) :=
    Measure.isProbabilityMeasure_map (FangqingAdaptiveHaarProduct.measurable_frame _).aemeasurable
  haveI : IsProbabilityMeasure (frameLaw bW hW) :=
    Measure.isProbabilityMeasure_map (FangqingAdaptiveHaarProduct.measurable_frame _).aemeasurable
  haveI : IsProbabilityMeasure nu := inferInstanceAs (IsProbabilityMeasure ((frameLaw bA hA).prod (frameLaw bW hW)))
  haveI : ∀ t, IsProbabilityMeasure (laws t) := fun _ => inferInstanceAs (IsProbabilityMeasure nu)
  let sigma := sideLaw seeds laws packet
  haveI : IsProbabilityMeasure sigma := original_side_probability seeds laws packet
  have hDecode : Measurable (decodePublic (A:=A) (B:=B) (W:=W) (outer:=outer) (nt:=nt)) := by unfold decodePublic; fun_prop
  have hView : Measurable (oracleView (A:=A) (B:=B) (W:=W) (outer:=outer) (nt:=nt)) := measurable_fst
  have hqpad := paddedQuery_measurable query hq decodePublic hDecode oracleView hView (0 : Point A B W outer)
  have hopad := paddedOutput_measurable out ho decodePublic hDecode oracleView hView
  have hBoth := (hCertified Seed packet (paddedQuery query decodePublic oracleView (0 : Point A B W outer))
    (paddedOutput out decodePublic oracleView) hqpad hopad Npaid zeta hz hDimA hDimW sigma)
  have hBad := paperBad_measurable c C m0 m1 packet hd hdw hp
    (paddedQuery query decodePublic oracleView (0 : Point A B W outer)) hqpad
    (paddedOutput out decodePublic oracleView) hopad (Npaid+1) q
  have hSource := original_world_conditional_event_bound seeds laws packet _ hBad zeta hBoth.2
  rw [original_side_sigma_is_exact] at hSource
  exact ⟨fun rawSide => hBoth.1 (sideEncoder packet rawSide),hSource⟩

end Algorithms
end
end FangqingOriginalWorldFirstHit
end

section
-- Source component: PrivateHandleFirstHitOriginalWorld.lean

open MeasureTheory
open scoped NNReal

namespace FangqingPrivateHandleFirstHitOriginalWorld

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingActualPaddedRelayReplies FangqingActualRelayHaarEvent FangqingActualUniformFirstHit
  FangqingActualFirstHitOriginalDimension FangqingActualRelayPublicNormalizers
  FangqingHierarchyFirstHitPacketGeometry FangqingHierarchyLateGateWorldFactory FangqingHierarchyAlignment
  FangqingOriginalWorldFirstHit FangqingFirstHitAllTolerances FangqingPrivateHandleFirstHit FangqingPrivateHandleFirstHitVariableC FangqingActualRelayScaling FangqingThirdGroupScaling FangqingAdaptiveHaarOriginal FangqingPaperFirstHitEvents OriginalTwoGroupPrefixExecution
  OriginalTwoGroupHaarExecution OriginalPacketOrientationNormalization OriginalPacketDistanceGapBounds

noncomputable section
set_option maxHeartbeats 7000000

universe u v

theorem original_private_handle_first_hit
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw : ℝ)
    (hCm : 1 ≤ Cm) (hCw : 4*(Cm+2) ≤ Cw)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left)
    (hr : ∀ t, Bp < t → phi t = right) (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ Ce : ℝ≥0, 1 ≤ Ce ∧ ∃ K Ks KD csigma Cdelta cL cq cg cT CD : ℝ,
      0 ≤ K ∧ 0 ≤ Ks ∧ 1 ≤ KD ∧ 0 < csigma ∧ 0 ≤ Cdelta ∧
      0 < cL ∧ cL ≤ 1/256 ∧ 0 < cq ∧ cq ≤ 1 ∧ 0 < cg ∧ cg ≤ 1 ∧ 0 < cT ∧ 1 ≤ CD ∧
      AlignmentAvailable cq cL Cw cg KD ∧
      ∀ (A B W : Type u)
        [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
        [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
        [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
        [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
        [MeasurableSpace W] [BorelSpace W] [Nontrivial W]
        [SecondCountableTopology A] [SecondCountableTopology W]
        [MeasurableSpace (PhysicalSpace A B W)] [BorelSpace (PhysicalSpace A B W)]
        [SecondCountableTopology (PhysicalSpace A B W)],
      ∀ (nt : ℕ) (L mu eps r rhop omega : ℝ) (q : ℕ),
      0 < L → 0 < mu → 0 < eps → 1 ≤ r → 0 < rhop → rhop ≤ rho L mu eps r →
      8 ≤ q → q ≤ nt+2 → (q:ℝ)^2 ≤ cq^2*(L/mu) → 0 < omega → ((nt+2:ℕ):ℝ) ≤ Cm*(q:ℝ) →
      omega = Cw*((8*(2*mu))/(cg*rhop))*(q:ℝ)^2 →
      distanceScale q omega = packetD (2*cL*L) (2*mu) KD eps →
      let c := originalConfig2 P phi nt Ce K Ks Cm Cw KD csigma Cdelta cL cg L mu eps r rhop q ((1/8)*omega) omega
      ∀ (dA dW : ℕ) (bA : OrthonormalBasis (Fin dA) ℝ A) (hA : 1 ≤ dA)
        (bW : OrthonormalBasis (Fin dW) ℝ W) (hW : nt+2 ≤ dW),
      let hRef := referenceHandle bA hA
      let tailRef := referenceTail bW hW
      ∀ (outer : ℕ)
        [MeasurableSpace (Point A B W outer)] [BorelSpace (Point A B W outer)]
        [MeasurableSpace (Point A B W outer →L[ℝ] Point A B W outer)] [BorelSpace (Point A B W outer →L[ℝ] Point A B W outer)]
        (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B),
      let mZero := fun t => publicZeroNormalizer c (C t) hRef tailRef
      let mOne := fun t => publicOneNormalizer c (C t) hRef tailRef
      (∀ t (h : A) (tail : Fin (nt+2) → W), ‖h‖=1 → Orthonormal ℝ tail →
        FangqingCanonicalLateGateFamily.H0 c (C t) h tail 0 = mZero t ∧
        FangqingCanonicalLateGateFamily.H1 c (C t) h tail (Z c (C t) h tail) = mOne t) ∧
        OriginalWorldAlgorithms.{u,v} (outer:=outer) c C mZero mOne q CD bA hA bW hW := by
  obtain ⟨Ce,hCe,K,Ks,KD,csigma,Cdelta,cL,cq,cg,cT,CD,hK,hKs,hKD,hcs,hCD,hcL,hcL256,hcq,hcq1,hcg,hcg1,hcT,hCD1,hAlign,hModel⟩ :=
    original_uniform_conditional_first_hit_all_tolerances.{u,v} P phi Bp left right Cm Cw hCm hCw hp hl hr hcore
  refine ⟨Ce,hCe,K,Ks,KD,csigma,Cdelta,cL,cq,cg,cT,CD,hK,hKs,hKD,hcs,hCD,hcL,hcL256,hcq,hcq1,hcg,hcg1,hcT,hCD1,hAlign,?_⟩
  intro A B W iA iA' iA'' iB iB' iB'' iW iW' iW'' mA bAinst nA mW bWinst nW scA scW mPhys bPhys scPhys
    nt L mu eps r rhop omega q hL hmu heps hr hrhop hrho hq hfit hqcap hw hn homega hScale c
    dA dW bA hA bW hW hRef tailRef outer mPoint bPoint mHess bHess C mZero mOne
  have hthis := hModel A B W nt L mu eps r rhop omega q hL hmu heps hr hrhop hrho hq hfit hqcap hw hn homega hScale
    dA dW bA hA bW hW outer C
  exact ⟨hthis.1,all_tolerances_give_literal_original_product_world c C mZero mOne q CD bA hA bW hW
    (by change 0 < (1/8:ℝ)*omega; positivity)
    (by change (1/8:ℝ)*omega ≤ omega; linarith only [hw]) hp hthis.2⟩

end
end FangqingPrivateHandleFirstHitOriginalWorld
end

section
-- Source component: OriginalWorldExecutionCoordinates.lean

namespace FangqingOriginalWorldExecutionCoordinates

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingCanonicalSuppressedRelay FangqingActualPaddedRelayReplies FangqingActualPaddedProgramEmbedding
  FangqingPaddedPublicInputProgram FangqingOriginalPacketWorld FangqingOriginalWorldFirstHit
  FangqingActualUniformFirstHit FangqingStoppedUniformFirstHit FangqingPreHitRelayLocality
  OriginalTwoGroupPrefixExecution

noncomputable section
set_option maxHeartbeats 5000000

universe u v

variable {A B W : Type u} {Seed : Type v}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace A] [BorelSpace A] [MeasurableSpace W] [BorelSpace W]
  [Nontrivial A] [Nontrivial W] [SecondCountableTopology A] [SecondCountableTopology W]
  [MeasurableSpace (PhysicalSpace A B W)] [BorelSpace (PhysicalSpace A B W)]
  [SecondCountableTopology (PhysicalSpace A B W)]
  [MeasurableSpace Seed] {outer nt : ℕ}
  [MeasurableSpace (Point A B W outer)] [BorelSpace (Point A B W outer)]
  [MeasurableSpace (Point A B W outer →L[ℝ] Point A B W outer)] [BorelSpace (Point A B W outer →L[ℝ] Point A B W outer)]

abbrev OriginalQuery (Seed A B W : Type*)
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] (outer : ℕ) :=
  PublicQuery Seed (Point A B W outer) (Response A B W outer) (Point A B W outer)

abbrev OriginalOutput (Seed A B W : Type*)
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] (outer : ℕ) :=
  Seed → Point A B W outer → (ℕ → Response A B W outer) → Point A B W outer

def globalPublicInput (c : Config nt) (z : World Seed A W outer nt) : Point A B W outer :=
  publicInitialPoint c ((globalParameters z 0).1)

def globalOracle (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (z : World Seed A W outer nt) : Point A B W outer → Response A B W outer :=
  fullReply (FangqingCanonicalRelayParameterFamily.family c C m0 m1 (globalParameters z))

def globalHistory (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (query : OriginalQuery Seed A B W outer) (N : ℕ) (z : World Seed A W outer nt) : ℕ → Response A B W outer :=
  ordinaryRun query (globalOracle c C m0 m1 z) z.1 (globalPublicInput c z) N

def globalQuery (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (query : OriginalQuery Seed A B W outer) (N : ℕ) (z : World Seed A W outer nt) : Point A B W outer :=
  query N z.1 (globalPublicInput c z) (globalHistory c C m0 m1 query N z)

def globalOutput (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (query : OriginalQuery Seed A B W outer) (out : OriginalOutput Seed A B W outer)
    (N : ℕ) (z : World Seed A W outer nt) : Point A B W outer :=
  out z.1 (globalPublicInput c z) (globalHistory c C m0 m1 query N z)

def packetState (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (packet : Fin (outer+1)) (query : OriginalQuery Seed A B W outer) (n : ℕ)
    (z : World Seed A W outer nt) : State (AugResponse A B W outer nt) :=
  let e := worldToPacket packet z
  fullRun (paddedQuery query decodePublic oracleView (0 : Point A B W outer)) (activation c C packet)
    (realReply c C m0 m1 packet) n z.1 e.1.2 e.2.1 e.2.2

theorem packet_paid_history_is_same_global_history
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (packet : Fin (outer+1)) (query : OriginalQuery Seed A B W outer) (n : ℕ) (z : World Seed A W outer nt) :
    decodePublic ((packetState c C m0 m1 packet query (n+1) z).2.2 0) = globalPublicInput c z ∧
    paidHistory oracleView (packetState c C m0 m1 packet query (n+1) z).2.2 = globalHistory c C m0 m1 query n z := by
  have h := original_full_instance_paid_history_and_unqueried_output c C m0 m1 packet query (fun _ _ _ => 0) z n
  exact ⟨h.1,h.2.1⟩

theorem packet_paid_query_is_same_global_query
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (packet : Fin (outer+1)) (query : OriginalQuery Seed A B W outer) (n : ℕ) (z : World Seed A W outer nt) :
    paddedQuery query decodePublic oracleView (0 : Point A B W outer) (n+1) z.1
      (packetState c C m0 m1 packet query (n+1) z).2.2 = globalQuery c C m0 m1 query n z := by
  have h := packet_paid_history_is_same_global_history c C m0 m1 packet query n z
  simp only [paddedQuery,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false,Nat.add_sub_cancel]
  rw [h.1,h.2]
  rfl

theorem packet_terminal_output_is_same_global_output
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (packet : Fin (outer+1)) (query : OriginalQuery Seed A B W outer) (out : OriginalOutput Seed A B W outer)
    (N : ℕ) (z : World Seed A W outer nt) :
    paddedOutput out decodePublic oracleView z.1 (packetState c C m0 m1 packet query (N+1) z).2.2 =
      globalOutput c C m0 m1 query out N z :=
  (original_full_instance_paid_history_and_unqueried_output c C m0 m1 packet query out z N).2.2

def globalDecision (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (packet : Fin (outer+1)) (query : OriginalQuery Seed A B W outer) (n : ℕ) (z : World Seed A W outer nt) : Bool :=
  if n=0 then decide (packet=0) else Fin.cases true
    (fun j => decide (‖globalQuery c C m0 m1 query (n-1) z (2,j.castSucc) -
      c.a • center c (C j.castSucc) (globalParameters z j.castSucc)‖ < 2*(c.a*c.ell))) packet

def globalTau (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (packet : Fin (outer+1)) (query : OriginalQuery Seed A B W outer) (M : ℕ) (z : World Seed A W outer nt) : ℕ :=
  OriginalPrefixOracleReplay.firstHitUntil M (fun n => globalDecision c C m0 m1 packet query n z)

theorem packet_actual_decision_is_same_global_decision
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (packet : Fin (outer+1)) (query : OriginalQuery Seed A B W outer) (n : ℕ) (z : World Seed A W outer nt) :
    activation c C packet n (worldToPacket packet z).1.2 (packetState c C m0 m1 packet query n z)
      (paddedQuery query decodePublic oracleView (0 : Point A B W outer) n z.1 (packetState c C m0 m1 packet query n z).2.2) =
      globalDecision c C m0 m1 packet query n z := by
  cases n with
  | zero => simp [activation,globalDecision]
  | succ n =>
      rw [packet_paid_query_is_same_global_query]
      revert packet
      intro packet
      refine Fin.cases ?_ (fun j => ?_) packet
      · simp [activation,globalDecision]
      · have hne : j.castSucc ≠ j.succ := by intro h; have hv := congrArg Fin.val h; simp only [Fin.val_castSucc,Fin.val_succ] at hv; omega
        have hs := congrArg Prod.snd (side_is_zero_filled_actual_parameters (Seed:=Seed) j.succ z)
        have hp := congrArg (fun side : Parameters A W outer nt => side j.castSucc) hs
        simp only [Function.update_of_ne hne] at hp
        simp only [activation,globalDecision,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false,
          Fin.cases_succ,Nat.add_sub_cancel,hp,globalParameters]

theorem packet_actual_activation_time_is_same_global_time
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (packet : Fin (outer+1)) (query : OriginalQuery Seed A B W outer) (M : ℕ) (z : World Seed A W outer nt) :
    realTau c C m0 m1 packet (paddedQuery query decodePublic oracleView (0 : Point A B W outer)) M
      (worldToPacket packet z) = globalTau c C m0 m1 packet query M z := by
  unfold realTau realActivationUntil globalTau
  apply congrArg (OriginalPrefixOracleReplay.firstHitUntil M)
  funext n
  exact packet_actual_decision_is_same_global_decision c C m0 m1 packet query n z


def globalOwnRelayHit (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (packet : Fin (outer+1))
    (z : World Seed A W outer nt) (point : Point A B W outer) : Bool :=
  ownRelayHit c C packet (z.2 packet).1 (z.2 packet).2 point

def globalPrimalHit (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (packet : Fin (outer+1))
    (z : World Seed A W outer nt) (point : Point A B W outer) : Bool :=
  packetOutputHit c C packet (z.2 packet).1 (z.2 packet).2 point

theorem next_global_activation_is_own_relay_hit
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (j : Fin outer) (query : OriginalQuery Seed A B W outer) (n : ℕ) (z : World Seed A W outer nt) (hn : 0 < n) :
    globalDecision c C m0 m1 j.succ query n z =
      globalOwnRelayHit c C j.castSucc z (globalQuery c C m0 m1 query (n-1) z) := by
  simp only [globalDecision,Nat.ne_of_gt hn,if_false,Fin.cases_succ,globalOwnRelayHit,ownRelayHit,globalParameters]
  congr 1

theorem packet_actual_paid_candidate_is_same_global_query
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (packet : Fin (outer+1)) (query : OriginalQuery Seed A B W outer) (out : OriginalOutput Seed A B W outer)
    (M n : ℕ) (hn : 0 < n) (hnM : n < M) (z : World Seed A W outer nt) :
    FangqingActualUniformFirstHit.actualCandidate c C m0 m1 packet
      (paddedQuery query decodePublic oracleView (0 : Point A B W outer)) (paddedOutput out decodePublic oracleView)
      M ⟨n,by omega⟩ (worldToPacket packet z) = globalQuery c C m0 m1 query (n-1) z := by
  simp only [FangqingActualUniformFirstHit.actualCandidate,OriginalTwoGroupHaarExecution.queryOrOutput,if_pos hnM]
  have he : n-1+1=n := by omega
  simpa only [he,packetState,seed_coordinate] using!
    packet_paid_query_is_same_global_query c C m0 m1 packet query (n-1) z

theorem packet_actual_terminal_candidate_is_same_global_output
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (packet : Fin (outer+1)) (query : OriginalQuery Seed A B W outer) (out : OriginalOutput Seed A B W outer)
    (N : ℕ) (z : World Seed A W outer nt) :
    FangqingActualUniformFirstHit.actualCandidate c C m0 m1 packet
      (paddedQuery query decodePublic oracleView (0 : Point A B W outer)) (paddedOutput out decodePublic oracleView)
      (N+1) (Fin.last (N+1)) (worldToPacket packet z) = globalOutput c C m0 m1 query out N z := by
  simp only [FangqingActualUniformFirstHit.actualCandidate,OriginalTwoGroupHaarExecution.queryOrOutput,
    Fin.val_last,lt_self_iff_false,if_false]
  simpa only [packetState,seed_coordinate] using!
    packet_terminal_output_is_same_global_output c C m0 m1 packet query out N z

end
end FangqingOriginalWorldExecutionCoordinates
end

section
-- Source component: ActualSerialFirstHitGeometry.lean

namespace FangqingActualSerialFirstHitGeometry

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingCanonicalSuppressedRelay FangqingActualPaddedRelayReplies FangqingActualPaddedProgramEmbedding
  FangqingPaddedPublicInputProgram FangqingOriginalPacketWorld FangqingOriginalWorldFirstHit
  FangqingActualUniformFirstHit FangqingStoppedUniformFirstHit FangqingPreHitRelayLocality
  FangqingPaperFirstHitEvents FangqingOriginalWorldExecutionCoordinates
  FangqingStoppedTwoGroupReplay OriginalTwoGroupPrefixExecution

noncomputable section
set_option maxHeartbeats 5000000

universe u v
variable {A B W : Type u} {Seed : Type v}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace A] [BorelSpace A] [MeasurableSpace W] [BorelSpace W]
  [Nontrivial A] [Nontrivial W] [SecondCountableTopology A] [SecondCountableTopology W]
  [MeasurableSpace (PhysicalSpace A B W)] [BorelSpace (PhysicalSpace A B W)]
  [SecondCountableTopology (PhysicalSpace A B W)]
  [MeasurableSpace Seed] {outer nt : ℕ}
  [MeasurableSpace (Point A B W outer)] [BorelSpace (Point A B W outer)]
  [MeasurableSpace (Point A B W outer →L[ℝ] Point A B W outer)] [BorelSpace (Point A B W outer →L[ℝ] Point A B W outer)]

def worldPacketBad (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (packet : Fin (outer+1)) (query : OriginalQuery Seed A B W outer) (out : OriginalOutput Seed A B W outer)
    (N q : ℕ) : Set (World Seed A W outer nt) :=
  worldToPacket packet ⁻¹' paperBad c C m0 m1 packet
    (paddedQuery query decodePublic oracleView (0 : Point A B W outer))
    (paddedOutput out decodePublic oracleView) (N+1) q

theorem global_activation_time_le_horizon
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (packet : Fin (outer+1)) (query : OriginalQuery Seed A B W outer) (M : ℕ) (z : World Seed A W outer nt) :
    globalTau c C m0 m1 packet query M z ≤ M := OriginalPrefixOracleReplay.firstHitUntil_le M _

theorem first_global_packet_activation_is_zero
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (query : OriginalQuery Seed A B W outer) (N : ℕ) (z : World Seed A W outer nt) :
    globalTau c C m0 m1 0 query (N+1) z = 0 := by
  simp [globalTau,OriginalPrefixOracleReplay.firstHitUntil,globalDecision]

theorem good_packet_excludes_early_global_terminal_hit
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (packet : Fin (outer+1)) (query : OriginalQuery Seed A B W outer) (out : OriginalOutput Seed A B W outer)
    (N q : ℕ) (z : World Seed A W outer nt) (hg : z ∉ worldPacketBad c C m0 m1 packet query out N q)
    (hearly : paperEarly (globalTau c C m0 m1 packet query (N+1) z) (N+1) q (N+1)) :
    globalPrimalHit c C packet z (globalOutput c C m0 m1 query out N z) = false := by
  by_contra hn
  have hh : globalPrimalHit c C packet z (globalOutput c C m0 m1 query out N z) = true := by simpa using hn
  apply hg
  change worldToPacket packet z ∈ paperBad c C m0 m1 packet _ _ (N+1) q
  apply Or.inr
  constructor
  · rw [packet_actual_activation_time_is_same_global_time]
    exact hearly
  · rw [packet_actual_terminal_candidate_is_same_global_output]
    simpa only [own_coordinate,globalPrimalHit] using hh

theorem terminal_hit_on_good_packet_implies_genuine_query_activation
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (packet : Fin (outer+1)) (query : OriginalQuery Seed A B W outer) (out : OriginalOutput Seed A B W outer)
    (N q : ℕ) (z : World Seed A W outer nt) (hg : z ∉ worldPacketBad c C m0 m1 packet query out N q)
    (hHit : globalPrimalHit c C packet z (globalOutput c C m0 m1 query out N z) = true) :
    globalTau c C m0 m1 packet query (N+1) z < N+1 := by
  have hle := global_activation_time_le_horizon c C m0 m1 packet query (N+1) z
  by_contra hnot
  have he : globalTau c C m0 m1 packet query (N+1) z = N+1 := by omega
  have hf := good_packet_excludes_early_global_terminal_hit c C m0 m1 packet query out N q z hg (Or.inl he)
  rw [hf] at hHit
  contradiction

theorem good_packet_excludes_early_global_paid_query_hit
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (packet : Fin (outer+1)) (query : OriginalQuery Seed A B W outer) (out : OriginalOutput Seed A B W outer)
    (N q n : ℕ) (hn : 0 < n) (hnM : n < N+1) (z : World Seed A W outer nt)
    (hg : z ∉ worldPacketBad c C m0 m1 packet query out N q)
    (hearly : paperEarly (globalTau c C m0 m1 packet query (N+1) z) (N+1) q n) :
    globalOwnRelayHit c C packet z (globalQuery c C m0 m1 query (n-1) z) = false := by
  by_contra hnot
  have hh : globalOwnRelayHit c C packet z (globalQuery c C m0 m1 query (n-1) z) = true := by simpa using hnot
  apply hg
  change worldToPacket packet z ∈ paperBad c C m0 m1 packet _ _ (N+1) q
  apply Or.inl
  apply Or.inr
  apply Set.mem_iUnion.mpr
  refine ⟨⟨n,hnM⟩,?_,?_⟩
  · rw [packet_actual_activation_time_is_same_global_time]
    exact hearly
  · have he := packet_actual_paid_candidate_is_same_global_query c C m0 m1 packet query out (N+1) n hn hnM z
    have he' : FangqingActualUniformFirstHit.actualCandidate c C m0 m1 packet
        (paddedQuery query decodePublic oracleView (0 : Point A B W outer)) (paddedOutput out decodePublic oracleView)
        (N+1) (⟨n,hnM⟩ : Fin (N+1)).castSucc (worldToPacket packet z) = globalQuery c C m0 m1 query (n-1) z := by
      convert! he using 1
    rw [he']
    simpa only [own_coordinate,globalOwnRelayHit] using hh

theorem next_packet_activation_after_true_increment
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (j : Fin outer) (query : OriginalQuery Seed A B W outer) (out : OriginalOutput Seed A B W outer)
    (N q : ℕ) (z : World Seed A W outer nt) (hg : z ∉ worldPacketBad c C m0 m1 j.castSucc query out N q)
    (hNext : globalTau c C m0 m1 j.succ query (N+1) z < N+1) :
    (globalTau c C m0 m1 j.castSucc query (N+1) z : ℝ)+(q:ℝ)/16-2 ≤
      (globalTau c C m0 m1 j.succ query (N+1) z : ℝ) := by
  let n := globalTau c C m0 m1 j.succ query (N+1) z
  have ht : globalDecision c C m0 m1 j.succ query n z = true :=
    firstHit_is_hit_when_lt (N+1) (fun n => globalDecision c C m0 m1 j.succ query n z) hNext
  have hn : 0 < n := by
    by_contra hn
    have hz : n=0 := by omega
    have hj : j.succ ≠ 0 := by intro he; have hv := congrArg Fin.val he; simp only [Fin.val_succ,Fin.val_zero] at hv; omega
    simp only [hz,globalDecision,if_true,decide_eq_true_eq] at ht
    exact hj ht
  rw [next_global_activation_is_own_relay_hit c C m0 m1 j query n z hn] at ht
  by_contra hlt
  have hearly : paperEarly (globalTau c C m0 m1 j.castSucc query (N+1) z) (N+1) q n := Or.inr (lt_of_not_ge hlt)
  have hf := good_packet_excludes_early_global_paid_query_hit c C m0 m1 j.castSucc query out N q n hn hNext z hg hearly
  rw [hf] at ht
  contradiction

theorem terminal_time_after_true_increment
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (packet : Fin (outer+1)) (query : OriginalQuery Seed A B W outer) (out : OriginalOutput Seed A B W outer)
    (N q : ℕ) (z : World Seed A W outer nt) (hg : z ∉ worldPacketBad c C m0 m1 packet query out N q)
    (hHit : globalPrimalHit c C packet z (globalOutput c C m0 m1 query out N z) = true) :
    (globalTau c C m0 m1 packet query (N+1) z : ℝ)+(q:ℝ)/16-2 ≤ ((N+1:ℕ):ℝ) := by
  by_contra hlt
  have hf := good_packet_excludes_early_global_terminal_hit c C m0 m1 packet query out N q z hg (Or.inr (lt_of_not_ge hlt))
  rw [hf] at hHit
  contradiction


def terminalChamberSuccess (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (query : OriginalQuery Seed A B W outer) (out : OriginalOutput Seed A B W outer) (N : ℕ) :
    Set (World Seed A W outer nt) :=
  {z | ∀ packet, globalPrimalHit c C packet z (globalOutput c C m0 m1 query out N z) = true}

def serialClock (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (query : OriginalQuery Seed A B W outer) (N n : ℕ) (z : World Seed A W outer nt) : ℝ :=
  if h : n < outer+1 then (globalTau c C m0 m1 ⟨n,h⟩ query (N+1) z : ℝ) else ((N+1:ℕ):ℝ)

theorem actual_success_conditional_serial_clock_starts_and_ends
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (query : OriginalQuery Seed A B W outer) (N : ℕ) (z : World Seed A W outer nt) :
    serialClock c C m0 m1 query N 0 z = 0 ∧
    serialClock c C m0 m1 query N (outer+1) z = ((N+1:ℕ):ℝ) := by
  constructor
  · simp only [serialClock,Nat.zero_lt_succ,dif_pos,Fin.mk_zero,first_global_packet_activation_is_zero,Nat.cast_zero]
  · simp only [serialClock,lt_self_iff_false,dif_neg,not_false_eq_true]

theorem actual_success_conditional_serial_increments
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (query : OriginalQuery Seed A B W outer) (out : OriginalOutput Seed A B W outer) (N q : ℕ)
    (z : World Seed A W outer nt) (hs : z ∈ terminalChamberSuccess c C m0 m1 query out N)
    (hg : z ∉ ⋃ packet, worldPacketBad c C m0 m1 packet query out N q) :
    ∀ n < outer+1,
      serialClock c C m0 m1 query N n z + ((q:ℝ)/16-2) ≤ serialClock c C m0 m1 query N (n+1) z := by
  have good (p : Fin (outer+1)) : z ∉ worldPacketBad c C m0 m1 p query out N q :=
    fun hp => hg (Set.mem_iUnion.mpr ⟨p,hp⟩)
  intro n hn
  by_cases hlast : n=outer
  · subst n
    have he0 : serialClock c C m0 m1 query N outer z =
        (globalTau c C m0 m1 (Fin.last outer) query (N+1) z : ℝ) := by
      simp only [serialClock,Nat.lt_succ_self,dif_pos,Fin.last]
    rw [he0,(actual_success_conditional_serial_clock_starts_and_ends c C m0 m1 query N z).2]
    have h := terminal_time_after_true_increment c C m0 m1 (Fin.last outer) query out N q z (good _) (hs _)
    linarith only [h]
  · let j : Fin outer := ⟨n,by omega⟩
    have hn1 : n+1 < outer+1 := by omega
    have he0 : serialClock c C m0 m1 query N n z =
        (globalTau c C m0 m1 j.castSucc query (N+1) z : ℝ) := by
      simp only [serialClock,dif_pos hn,j,Fin.castSucc_mk]
    have he1 : serialClock c C m0 m1 query N (n+1) z =
        (globalTau c C m0 m1 j.succ query (N+1) z : ℝ) := by
      simp only [serialClock,dif_pos hn1,j,Fin.succ_mk]
    rw [he0,he1]
    have hNext := terminal_hit_on_good_packet_implies_genuine_query_activation c C m0 m1 j.succ query out N q z (good _) (hs _)
    have h := next_packet_activation_after_true_increment c C m0 m1 j query out N q z (good _) hNext
    linarith only [h]

theorem original_serial_small_budget_absorbs_terminal_plus_one (T N q : ℕ)
    (hT : 1 ≤ T) (hq : 128 ≤ q) (hN : (N:ℝ) < (T:ℝ)*(q:ℝ)/128) :
    ((N+1:ℕ):ℝ) < (T:ℝ)*((q:ℝ)/16-2) := by
  have hTr : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hqr : (128:ℝ) ≤ q := by exact_mod_cast hq
  have hT0 : (0:ℝ) ≤ T := Nat.cast_nonneg _
  have hTq : (128:ℝ) ≤ (T:ℝ)*(q:ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hqr hT0
    nlinarith only [hmul,hTr]
  have hhalf : (q:ℝ)/32 ≤ (q:ℝ)/16-2 := by linarith only [hqr]
  have hmul := mul_le_mul_of_nonneg_left hhalf hT0
  push_cast
  nlinarith only [hN,hTq,hmul]

end
end FangqingActualSerialFirstHitGeometry
end

section
-- Source component: ActualProductMeasurability.lean

open MeasureTheory

namespace FangqingActualProductMeasurability

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingCanonicalSuppressedRelay FangqingActualPaddedRelayReplies FangqingActualPaddedProgramEmbedding
  FangqingPaddedPublicInputProgram FangqingOriginalPacketWorld FangqingOriginalWorldFirstHit
  FangqingActualUniformFirstHit FangqingStoppedUniformFirstHit FangqingPreHitRelayLocality
  FangqingPaperFirstHitEvents FangqingOriginalWorldExecutionCoordinates FangqingActualSerialFirstHitGeometry
  FangqingActualFirstHitMeasurability FangqingHaarFrameLawSupport FangqingAdaptiveHaarOriginal

noncomputable section
set_option maxHeartbeats 5000000

universe u v
variable {A B W : Type u} {Seed : Type v}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace A] [BorelSpace A] [MeasurableSpace W] [BorelSpace W]
  [Nontrivial A] [Nontrivial W] [SecondCountableTopology A] [SecondCountableTopology W]
  [MeasurableSpace (PhysicalSpace A B W)] [BorelSpace (PhysicalSpace A B W)]
  [SecondCountableTopology (PhysicalSpace A B W)]
  [MeasurableSpace Seed] {outer nt : ℕ}
  [MeasurableSpace (Point A B W outer)] [BorelSpace (Point A B W outer)]
  [MeasurableSpace (Point A B W outer →L[ℝ] Point A B W outer)] [BorelSpace (Point A B W outer →L[ℝ] Point A B W outer)]

variable (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hp : ContDiff ℝ 3 c.phi)
    (query : OriginalQuery Seed A B W outer) (out : OriginalOutput Seed A B W outer)
    (hq : ∀ n, Measurable (fun x : Seed × Point A B W outer × (ℕ → Response A B W outer) => query n x.1 x.2.1 x.2.2))
    (ho : Measurable (fun x : Seed × Point A B W outer × (ℕ → Response A B W outer) => out x.1 x.2.1 x.2.2))

include hd hdw hp hq ho

theorem global_output_measurable (N : ℕ) : Measurable (globalOutput c C m0 m1 query out N) := by
  have hDecode : Measurable (decodePublic (A:=A) (B:=B) (W:=W) (outer:=outer) (nt:=nt)) := by unfold decodePublic; fun_prop
  have hView : Measurable (oracleView (A:=A) (B:=B) (W:=W) (outer:=outer) (nt:=nt)) := measurable_fst
  have hqp := paddedQuery_measurable query hq decodePublic hDecode oracleView hView (0 : Point A B W outer)
  have hop := paddedOutput_measurable out ho decodePublic hDecode oracleView hView
  have hTarget := actualCandidate_measurable c C m0 m1 0 hd hdw hp
    (paddedQuery query decodePublic oracleView (0 : Point A B W outer)) hqp
    (paddedOutput out decodePublic oracleView) hop (N+1) (Fin.last (N+1))
  have hWorld := hTarget.comp (worldToPacket_measurableEmbedding (Seed:=Seed) (A:=A) (W:=W) (nt:=nt) (0 : Fin (outer+1))).measurable
  simpa only [Function.comp_def,packet_actual_terminal_candidate_is_same_global_output] using hWorld

theorem world_packet_bad_measurable (packet : Fin (outer+1)) (N q : ℕ) :
    MeasurableSet (worldPacketBad c C m0 m1 packet query out N q) := by
  have hDecode : Measurable (decodePublic (A:=A) (B:=B) (W:=W) (outer:=outer) (nt:=nt)) := by unfold decodePublic; fun_prop
  have hView : Measurable (oracleView (A:=A) (B:=B) (W:=W) (outer:=outer) (nt:=nt)) := measurable_fst
  have hqp := paddedQuery_measurable query hq decodePublic hDecode oracleView hView (0 : Point A B W outer)
  have hop := paddedOutput_measurable out ho decodePublic hDecode oracleView hView
  exact (paperBad_measurable c C m0 m1 packet hd hdw hp
    (paddedQuery query decodePublic oracleView (0 : Point A B W outer)) hqp
    (paddedOutput out decodePublic oracleView) hop (N+1) q).preimage
      (worldToPacket_measurableEmbedding packet).measurable

theorem terminal_chamber_success_measurable (N : ℕ) :
    MeasurableSet (terminalChamberSuccess c C m0 m1 query out N) := by
  have he : terminalChamberSuccess c C m0 m1 query out N =
      ⋂ packet, {z : World Seed A W outer nt | globalPrimalHit c C packet z (globalOutput c C m0 m1 query out N z) = true} := by
    ext z
    simp only [terminalChamberSuccess,Set.mem_setOf_eq,Set.mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro packet
  have hHandle : Measurable (fun z : World Seed A W outer nt => (z.2 packet).1) := by fun_prop
  have hTail : Measurable (fun z : World Seed A W outer nt => (z.2 packet).2) := by fun_prop
  have hh := (packetOutputHit_measurable c C packet).comp
    (hHandle.prodMk (hTail.prodMk (global_output_measurable c C m0 m1 hd hdw hp query out hq ho N)))
  exact hh (measurableSet_singleton true)

omit hd hdw hp hq ho in
 theorem original_side_sigma_le (packet : Fin (outer+1)) :
    originalSideSigma (Seed:=Seed) (A:=A) (W:=W) (nt:=nt) packet ≤
      (inferInstance : MeasurableSpace (World Seed A W outer nt)) := by
  have h : Measurable (fun z : World Seed A W outer nt => (z.1,fun j : Fin outer => z.2 (packet.succAbove j))) := by fun_prop
  exact h.comap_le

end
end FangqingActualProductMeasurability
end

section
-- Source component: ActualProductFrameSupport.lean

open MeasureTheory

namespace FangqingActualProductFrameSupport

open FangqingOriginalPacketWorld FangqingHaarFrameLawSupport FangqingAdaptiveHaarOriginal

noncomputable section
set_option maxHeartbeats 3000000

variable {A W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
  [MeasurableSpace W] [BorelSpace W] [Nontrivial W]
  {outer nt : ℕ}

abbrev Frames (A W : Type*) (outer nt : ℕ) := Fin (outer+1) → OwnFrame A W nt

def validFrames : Set (Frames A W outer nt) :=
  ⋂ packet, {frames | Orthonormal ℝ (frames packet).1 ∧ Orthonormal ℝ (frames packet).2}

theorem valid_frames_measurable : MeasurableSet (validFrames (A:=A) (W:=W) (outer:=outer) (nt:=nt)) := by
  apply MeasurableSet.iInter
  intro packet
  exact ((measurableSet_orthonormal_frames (E:=A) 1).preimage (by fun_prop)).inter
    ((measurableSet_orthonormal_frames (E:=W) (nt+2)).preimage (by fun_prop))

theorem true_haar_product_ae_valid_frames
    {dA dW : ℕ} (bA : OrthonormalBasis (Fin dA) ℝ A) (hA : 1 ≤ dA)
    (bW : OrthonormalBasis (Fin dW) ℝ W) (hW : nt+2 ≤ dW) :
    ∀ᵐ frames ∂Measure.pi (fun _ : Fin (outer+1) => (frameLaw bA hA).prod (frameLaw bW hW)),
      frames ∈ validFrames := by
  haveI : IsProbabilityMeasure (frameLaw bA hA) :=
    Measure.isProbabilityMeasure_map (FangqingAdaptiveHaarProduct.measurable_frame _).aemeasurable
  haveI : IsProbabilityMeasure (frameLaw bW hW) :=
    Measure.isProbabilityMeasure_map (FangqingAdaptiveHaarProduct.measurable_frame _).aemeasurable
  have hOwn := independent_product_ae_frame_support 1 (nt+2) (frameLaw bA hA) (frameLaw bW hW)
    (actual_frameLaw_ae_orthonormal bA hA) (actual_frameLaw_ae_orthonormal bW hW)
  have hEach (packet : Fin (outer+1)) :
      ∀ᵐ frames ∂Measure.pi (fun _ : Fin (outer+1) => (frameLaw bA hA).prod (frameLaw bW hW)),
        Orthonormal ℝ (frames packet).1 ∧ Orthonormal ℝ (frames packet).2 :=
    (measurePreserving_eval (fun _ : Fin (outer+1) => (frameLaw bA hA).prod (frameLaw bW hW)) packet).quasiMeasurePreserving.ae hOwn
  simpa only [validFrames,Set.mem_iInter,Set.mem_setOf_eq] using (ae_all_iff.mpr hEach)

theorem finite_horizon_dimension_budget_monotone (N N0 : ℕ) (hN : N ≤ N0)
    (CD q zeta : ℝ) (hCD : 0 < CD) (hq : 0 < q) (hz : 0 < zeta) :
    CD*q^3*Real.log (CD*((N:ℝ)+2)*q/zeta) ≤
      CD*q^3*Real.log (CD*((N0:ℝ)+2)*q/zeta) := by
  apply mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) (by positivity)
  gcongr

end
end FangqingActualProductFrameSupport
end

section
-- Source component: FirstHitModelFromGeometry.lean

open MeasureTheory
open scoped NNReal

namespace FangqingFirstHitModelFromGeometry

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingActualPaddedRelayReplies FangqingActualRelayHaarEvent FangqingActualUniformFirstHit
  FangqingActualFirstHitOriginalDimension FangqingActualRelayPublicNormalizers
  FangqingHierarchyFirstHitPacketGeometry FangqingHierarchyLateGateWorldFactory FangqingHierarchyAlignment
  FangqingOriginalWorldFirstHit FangqingFirstHitAllTolerances FangqingPrivateHandleFirstHit FangqingActualRelayScaling FangqingThirdGroupScaling FangqingAdaptiveHaarOriginal FangqingPaperFirstHitEvents OriginalTwoGroupPrefixExecution
  OriginalTwoGroupHaarExecution OriginalPacketOrientationNormalization OriginalPacketDistanceGapBounds

noncomputable section
set_option maxHeartbeats 7000000

universe u v

variable {A B W : Type u}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
  [MeasurableSpace W] [BorelSpace W] [Nontrivial W]
  [SecondCountableTopology A] [SecondCountableTopology W]
  [MeasurableSpace (PhysicalSpace A B W)] [BorelSpace (PhysicalSpace A B W)]
  [SecondCountableTopology (PhysicalSpace A B W)]
  {outer nt dA dW : ℕ}
  [MeasurableSpace (Point A B W outer)] [BorelSpace (Point A B W outer)]
  [MeasurableSpace (Point A B W outer →L[ℝ] Point A B W outer)] [BorelSpace (Point A B W outer →L[ℝ] Point A B W outer)]

theorem literal_first_hit_model_from_actual_canonical_packet_geometry
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (hp : ContDiff ℝ 3 c.phi) (hR : 0 < c.R) (hb : 0 < c.beta) (hl : 0 < c.lam) (ha : 0 < c.a)
    (q : ℕ) (hq : 8 ≤ q) (hfit : q ≤ nt+2) (hw : 0 < c.omega)
    (hell : c.ell = c.lam/c.beta * distanceScale q c.omega)
    (Cmin CR Cm : ℝ) (hCR : 0 < CR) (hCm : 1 ≤ Cm)
    (hcDelta : c.delta = (1/8)*c.omega) (hclip : Cmin+3 ≤ CR)
    (hRshell : 2*c.R ≤ CR*distanceScale q c.omega) (hm : ((nt+2:ℕ):ℝ) ≤ Cm*(q:ℝ))
    (hPacket : ∀ (packet : Fin (outer+1)) (h : A) (tail : Fin (nt+2) → W), ‖h‖=1 → Orthonormal ℝ tail →
      ‖Z c (C packet) h tail‖ ≤ Cmin*distanceScale q c.omega ∧
      ∀ j : Fin (nt+3), (j.val : ℝ) ≤ q → 3*(q:ℝ)*c.omega ≤
        inner ℝ (physicalFrame (C packet) h nt tail j) (Z c (C packet) h tail))
    (bA : OrthonormalBasis (Fin dA) ℝ A) (hA : 1 ≤ dA)
    (bW : OrthonormalBasis (Fin dW) ℝ W) (hW : nt+2 ≤ dW) :
    OriginalWorldAlgorithms.{u,v} c C m0 m1 q (dimensionConstant CR (1/8) Cm) bA hA bW hW := by
  have hd : 0 < c.delta := by rw [hcDelta]; positivity
  have hdw : c.delta ≤ c.omega := by rw [hcDelta]; linarith only [hw]
  apply all_tolerances_give_literal_original_product_world c C m0 m1 q (dimensionConstant CR (1/8) Cm) bA hA bW hW hd hdw hp
  apply all_tolerances_from_small_tolerances c C m0 m1 q (dimensionConstant CR (1/8) Cm) bA hA bW hW hd hdw hp
  intro Seed mSeed packet query out hqMeas hout Npaid zeta hz hz1 hDimA hDimW sigma pSigma
  have hActual := actual_conditional_first_hit_from_original_cubic_dimension c C m0 m1 packet hp hR hb hl ha q hq hfit hw hell
    Cmin CR (1/8) Cm hCR (by norm_num) (by norm_num) hCm hcDelta hclip hRshell hm (hPacket packet)
    bA hA bW hW query hqMeas out hout Npaid zeta hz hz1 hDimA hDimW sigma
  let nu := (frameLaw bA hA).prod (frameLaw bW hW)
  haveI : IsProbabilityMeasure (frameLaw bA hA) :=
    Measure.isProbabilityMeasure_map (FangqingAdaptiveHaarProduct.measurable_frame _).aemeasurable
  haveI : IsProbabilityMeasure (frameLaw bW hW) :=
    Measure.isProbabilityMeasure_map (FangqingAdaptiveHaarProduct.measurable_frame _).aemeasurable
  haveI : IsProbabilityMeasure nu := inferInstanceAs (IsProbabilityMeasure ((frameLaw bA hA).prod (frameLaw bW hW)))
  have hFiber : ∀ s : Seed × Parameters A W outer nt,
      nu.real (Prod.mk s ⁻¹' paperBad c C m0 m1 packet query out (Npaid+1) q) ≤ zeta := by
    intro s
    have hSub := Set.preimage_mono (f:=Prod.mk s) (paper_bad_subset_actual_stronger_bad c C m0 m1 packet query out (Npaid+1) q)
    exact (measureReal_mono hSub (by finiteness)).trans (hActual.1 s)
  exact ⟨hFiber,every_fiber_probability_bound_gives_actual_event_conditional_bound sigma nu _
    (paperBad_measurable c C m0 m1 packet hd hdw hp query hqMeas out hout (Npaid+1) q) zeta hFiber⟩

end
end FangqingFirstHitModelFromGeometry
end

section
-- Source component: SerialProductProbability-typed-infinity.lean

namespace OriginalSerialProductProbability

open MeasureTheory
open scoped ENNReal BigOperators

theorem serial_time_growth (T : ℕ) (delta : ℝ) (tau : ℕ → ℝ)
    (hzero : tau 0 = 0) (hstep : ∀ n < T, tau n + delta ≤ tau (n + 1)) :
    (T : ℝ) * delta ≤ tau T := by
  have hall : ∀ n ≤ T, (n : ℝ) * delta ≤ tau n := by
    intro n hn
    induction n with
    | zero => simp only [Nat.cast_zero, zero_mul, hzero]; exact le_rfl
    | succ n ih =>
      have hp := ih (by omega)
      have hs := hstep n (by omega)
      push_cast
      nlinarith only [hp, hs]
  exact hall T le_rfl

theorem probability_of_union_complement
    {Omega I : Type*} [MeasurableSpace Omega] [Fintype I]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (bad : I → Set Omega) (hbad : ∀ i, MeasurableSet (bad i))
    (zeta : ℝ≥0∞) (hprob : ∀ i, mu (bad i) ≤ zeta) :
    1 - (Fintype.card I : ℝ≥0∞) * zeta ≤ mu (⋃ i, bad i)ᶜ := by
  have hsum : mu (⋃ i, bad i) ≤ (Fintype.card I : ℝ≥0∞) * zeta := by
    calc
      _ ≤ ∑ i, mu (bad i) := measure_iUnion_fintype_le mu bad
      _ ≤ ∑ _ : I, zeta := Finset.sum_le_sum (fun i _ => hprob i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [measure_compl (MeasurableSet.iUnion hbad) (measure_ne_top mu _), measure_univ]
  exact tsub_le_tsub_left hsum 1

theorem probability_failure_from_serial_increments
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (T N : ℕ) (delta : ℝ) (tau : Omega → ℕ → ℝ)
    (bad : Fin T → Set Omega) (hbad : ∀ i, MeasurableSet (bad i))
    (zeta : ℝ≥0∞) (hprob : ∀ i, mu (bad i) ≤ zeta)
    (success : Set Omega)
    (hzero : ∀ omega ∉ ⋃ i, bad i, tau omega 0 = 0)
    (hstep : ∀ omega ∉ ⋃ i, bad i, ∀ n < T, tau omega n + delta ≤ tau omega (n + 1))
    (hterminal : ∀ omega ∉ ⋃ i, bad i, omega ∈ success → tau omega T ≤ (N : ℝ) + 1)
    (hbudget : (N : ℝ) + 1 < (T : ℝ) * delta) :
    1 - (T : ℝ≥0∞) * zeta ≤ mu successᶜ := by
  have hsubset : (⋃ i, bad i)ᶜ ⊆ successᶜ := by
    intro omega hg hs
    have hn : omega ∉ ⋃ i, bad i := hg
    have htime := serial_time_growth T delta (tau omega) (hzero omega hn) (hstep omega hn)
    have hlast := hterminal omega hn hs
    linarith only [htime, hlast, hbudget]
  have hp := probability_of_union_complement mu bad hbad zeta hprob
  simpa only [Fintype.card_fin] using hp.trans (measure_mono hsubset)

theorem exists_fixed_frame_failure
    {Frame Seed : Type*} [MeasurableSpace Frame] [MeasurableSpace Seed]
    (frames : Measure Frame) (seeds : Measure Seed)
    [IsProbabilityMeasure frames] [IsProbabilityMeasure seeds]
    (failure : Set (Frame × Seed)) (hfailure : MeasurableSet failure)
    (a : ℝ≥0∞) (haverage : a ≤ (frames.prod seeds) failure) :
    ∃ frame : Frame, a ≤ seeds {seed | (frame, seed) ∈ failure} := by
  have hfinite : (∫⁻ frame, seeds (Prod.mk frame ⁻¹' failure) ∂frames) ≠ (⊤ : ℝ≥0∞) := by
    rw [← Measure.prod_apply hfailure]
    exact measure_ne_top _ _
  obtain ⟨frame, hf⟩ := exists_lintegral_le hfinite
  refine ⟨frame, haverage.trans ?_⟩
  rw [Measure.prod_apply hfailure]
  exact hf

theorem third_budget_allocation (T : ℕ) (hT : 0 < T) :
    (T : ℝ≥0∞) * ENNReal.ofReal (1 / (3 * (T : ℝ))) = (1 / 3 : ℝ≥0∞) := by
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (T : ℝ))]
  have hid : (T : ℝ) * (1 / (3 * (T : ℝ))) = 1 / 3 := by field_simp
  rw [hid]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
  norm_num

theorem fixed_frame_from_serial_increments
    {Frame Seed : Type*} [MeasurableSpace Frame] [MeasurableSpace Seed]
    (frames : Measure Frame) (seeds : Measure Seed)
    [IsProbabilityMeasure frames] [IsProbabilityMeasure seeds]
    (T N : ℕ) (hT : 0 < T) (delta : ℝ) (tau : Frame × Seed → ℕ → ℝ)
    (bad : Fin T → Set (Frame × Seed)) (hbad : ∀ i, MeasurableSet (bad i))
    (hprob : ∀ i, (frames.prod seeds) (bad i) ≤ ENNReal.ofReal (1 / (3 * (T : ℝ))))
    (success : Set (Frame × Seed)) (hsuccess : MeasurableSet success)
    (hzero : ∀ omega ∉ ⋃ i, bad i, tau omega 0 = 0)
    (hstep : ∀ omega ∉ ⋃ i, bad i, ∀ n < T, tau omega n + delta ≤ tau omega (n + 1))
    (hterminal : ∀ omega ∉ ⋃ i, bad i, omega ∈ success → tau omega T ≤ (N : ℝ) + 1)
    (hbudget : (N : ℝ) + 1 < (T : ℝ) * delta) :
    ∃ frame : Frame, (2 / 3 : ℝ≥0∞) ≤ seeds {seed | (frame, seed) ∉ success} := by
  have hp := probability_failure_from_serial_increments (frames.prod seeds) T N delta tau bad hbad
    (ENNReal.ofReal (1 / (3 * (T : ℝ)))) hprob success hzero hstep hterminal hbudget
  rw [third_budget_allocation T hT] at hp
  have harith : (1 : ℝ≥0∞) - 1 / 3 = 2 / 3 := by
    have hthird : ENNReal.ofReal (1 / 3 : ℝ) = (1 / 3 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
      norm_num
    calc
      _ = ENNReal.ofReal 1 - ENNReal.ofReal (1 / 3 : ℝ) := by rw [hthird]; norm_num
      _ = ENNReal.ofReal (1 - (1 / 3 : ℝ)) := (ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 1 / 3)).symm
      _ = ENNReal.ofReal (2 / 3 : ℝ) := by norm_num
      _ = _ := by rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]; norm_num
  rw [harith] at hp
  exact exists_fixed_frame_failure frames seeds successᶜ hsuccess.compl (2 / 3) hp

end OriginalSerialProductProbability
end

section
-- Source component: SerialProductSuccessProbability.lean

namespace FangqingSerialProductSuccessProbability

open MeasureTheory
open scoped ENNReal BigOperators
open OriginalSerialProductProbability

theorem probability_failure_from_success_conditional_serial_steps
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (T N : ℕ) (delta : ℝ) (tau : Omega → ℕ → ℝ)
    (bad : Fin T → Set Omega) (hbad : ∀ i, MeasurableSet (bad i))
    (zeta : ℝ≥0∞) (hprob : ∀ i, mu (bad i) ≤ zeta)
    (success : Set Omega)
    (hzero : ∀ sample ∈ success, sample ∉ ⋃ i, bad i → tau sample 0 = 0)
    (hstep : ∀ sample ∈ success, sample ∉ ⋃ i, bad i →
      ∀ n < T, tau sample n + delta ≤ tau sample (n + 1))
    (hterminal : ∀ sample ∈ success, sample ∉ ⋃ i, bad i → tau sample T ≤ (N : ℝ) + 1)
    (hbudget : (N : ℝ) + 1 < (T : ℝ) * delta) :
    1 - (T : ℝ≥0∞) * zeta ≤ mu successᶜ := by
  have hsubset : (⋃ i, bad i)ᶜ ⊆ successᶜ := by
    intro sample hg hs
    have htime := serial_time_growth T delta (tau sample) (hzero sample hs hg) (hstep sample hs hg)
    have hlast := hterminal sample hs hg
    linarith only [htime, hlast, hbudget]
  have hp := probability_of_union_complement mu bad hbad zeta hprob
  simpa only [Fintype.card_fin] using hp.trans (measure_mono hsubset)

/-- A selected raw frame is also in the actual analytic-validity support. -/
theorem exists_fixed_valid_frame_failure
    {Frame Seed : Type*} [MeasurableSpace Frame] [MeasurableSpace Seed]
    (frames : Measure Frame) (seeds : Measure Seed)
    [IsProbabilityMeasure frames] [IsProbabilityMeasure seeds]
    (valid : Set Frame) (hvalid : MeasurableSet valid) (hae : ∀ᵐ frame ∂frames, frame ∈ valid)
    (failure : Set (Frame × Seed)) (hfailure : MeasurableSet failure)
    (a : ℝ≥0∞) (ha : 0 < a) (haverage : a ≤ (frames.prod seeds) failure) :
    ∃ frame : Frame, frame ∈ valid ∧ a ≤ seeds {seed | (frame, seed) ∈ failure} := by
  let restricted := failure ∩ {p : Frame × Seed | p.1 ∈ valid}
  have hpre : MeasurableSet {p : Frame × Seed | p.1 ∈ valid} :=
    hvalid.preimage measurable_fst
  have hprod : ∀ᵐ p ∂frames.prod seeds, p.1 ∈ valid := by
    apply (Measure.ae_prod_iff_ae_ae hpre).mpr
    filter_upwards [hae] with frame hf
    exact Filter.Eventually.of_forall (fun _ => hf)
  have heq : (frames.prod seeds) restricted = (frames.prod seeds) failure := by
    apply measure_congr
    filter_upwards [hprod] with p hp
    change (p ∈ failure ∧ p.1 ∈ valid) = (p ∈ failure)
    simp only [hp, and_true]
  obtain ⟨frame, hf⟩ := exists_fixed_frame_failure frames seeds restricted (hfailure.inter hpre) a
    (by rw [heq]; exact haverage)
  have hv : frame ∈ valid := by
    by_contra hn
    have hempty : {seed | (frame, seed) ∈ restricted} = ∅ := by
      ext seed
      simp only [restricted, Set.mem_inter_iff, Set.mem_setOf_eq, hn, and_false, Set.mem_empty_iff_false]
    rw [hempty, measure_empty] at hf
    exact (not_le_of_gt ha) hf
  refine ⟨frame, hv, hf.trans (measure_mono ?_)⟩
  intro seed h
  exact h.1

theorem fixed_valid_frame_from_success_conditional_serial_steps
    {Frame Seed : Type*} [MeasurableSpace Frame] [MeasurableSpace Seed]
    (frames : Measure Frame) (seeds : Measure Seed)
    [IsProbabilityMeasure frames] [IsProbabilityMeasure seeds]
    (valid : Set Frame) (hvalid : MeasurableSet valid) (hae : ∀ᵐ frame ∂frames, frame ∈ valid)
    (T N : ℕ) (hT : 0 < T) (delta : ℝ) (tau : Frame × Seed → ℕ → ℝ)
    (bad : Fin T → Set (Frame × Seed)) (hbad : ∀ i, MeasurableSet (bad i))
    (hprob : ∀ i, (frames.prod seeds) (bad i) ≤ ENNReal.ofReal (1 / (3 * (T : ℝ))))
    (success : Set (Frame × Seed)) (hsuccess : MeasurableSet success)
    (hzero : ∀ sample ∈ success, sample ∉ ⋃ i, bad i → tau sample 0 = 0)
    (hstep : ∀ sample ∈ success, sample ∉ ⋃ i, bad i →
      ∀ n < T, tau sample n + delta ≤ tau sample (n + 1))
    (hterminal : ∀ sample ∈ success, sample ∉ ⋃ i, bad i → tau sample T ≤ (N : ℝ) + 1)
    (hbudget : (N : ℝ) + 1 < (T : ℝ) * delta) :
    ∃ frame : Frame, frame ∈ valid ∧
      (2 / 3 : ℝ≥0∞) ≤ seeds {seed | (frame, seed) ∉ success} := by
  have hp := probability_failure_from_success_conditional_serial_steps (frames.prod seeds)
    T N delta tau bad hbad (ENNReal.ofReal (1 / (3 * (T : ℝ)))) hprob success hzero hstep hterminal hbudget
  rw [third_budget_allocation T hT] at hp
  have htwo : (1 : ℝ≥0∞) - 1 / 3 = 2 / 3 := by
    have hthird : ENNReal.ofReal (1 / 3 : ℝ) = (1 / 3 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
      norm_num
    calc
      _ = ENNReal.ofReal 1 - ENNReal.ofReal (1 / 3 : ℝ) := by rw [hthird]; norm_num
      _ = ENNReal.ofReal (1 - (1 / 3 : ℝ)) :=
        (ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 1 / 3)).symm
      _ = _ := by norm_num [ENNReal.ofReal_div_of_pos]
  rw [htwo] at hp
  exact exists_fixed_valid_frame_failure frames seeds valid hvalid hae successᶜ hsuccess.compl
    (2 / 3) (by norm_num) hp

end FangqingSerialProductSuccessProbability
end

section
-- Source component: ActualProductProbability.lean

open MeasureTheory
open scoped ENNReal

namespace FangqingActualProductProbability

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingActualPaddedRelayReplies FangqingOriginalPacketWorld FangqingOriginalWorldFirstHit
  FangqingOriginalWorldExecutionCoordinates FangqingActualSerialFirstHitGeometry
  FangqingActualProductMeasurability FangqingActualProductFrameSupport FangqingAdaptiveHaarOriginal
  FangqingSerialProductSuccessProbability

noncomputable section
set_option maxHeartbeats 6000000

universe u v
variable {A B W : Type u} {Seed : Type v}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace A] [BorelSpace A] [MeasurableSpace W] [BorelSpace W]
  [Nontrivial A] [Nontrivial W] [SecondCountableTopology A] [SecondCountableTopology W]
  [MeasurableSpace (PhysicalSpace A B W)] [BorelSpace (PhysicalSpace A B W)]
  [SecondCountableTopology (PhysicalSpace A B W)]
  [MeasurableSpace Seed] {outer nt : ℕ}
  [MeasurableSpace (Point A B W outer)] [BorelSpace (Point A B W outer)]
  [MeasurableSpace (Point A B W outer →L[ℝ] Point A B W outer)] [BorelSpace (Point A B W outer →L[ℝ] Point A B W outer)]

theorem actual_fixed_valid_frame_with_chamber_failure
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hp : ContDiff ℝ 3 c.phi)
    (q : ℕ) (hq : 128 ≤ q) (CD : ℝ) (hCD : 1 ≤ CD)
    {dA dW : ℕ} (bA : OrthonormalBasis (Fin dA) ℝ A) (hA : 1 ≤ dA)
    (bW : OrthonormalBasis (Fin dW) ℝ W) (hW : nt+2 ≤ dW)
    (hCertified : OriginalWorldAlgorithms.{u,v} c C m0 m1 q CD bA hA bW hW)
    (query : OriginalQuery Seed A B W outer) (out : OriginalOutput Seed A B W outer)
    (hqMeas : ∀ n, Measurable (fun x : Seed × Point A B W outer × (ℕ → Response A B W outer) => query n x.1 x.2.1 x.2.2))
    (hout : Measurable (fun x : Seed × Point A B W outer × (ℕ → Response A B W outer) => out x.1 x.2.1 x.2.2))
    (N0 N : ℕ) (hNN : N ≤ N0)
    (hDimA : CD*(q:ℝ)^3*Real.log (CD*((N0:ℝ)+2)*(q:ℝ)/(1/(3*((outer+1:ℕ):ℝ)))) ≤ ((dA-1:ℕ):ℝ))
    (hDimW : CD*(q:ℝ)^3*Real.log (CD*((N0:ℝ)+2)*(q:ℝ)/(1/(3*((outer+1:ℕ):ℝ)))) ≤ ((dW-(nt+2):ℕ):ℝ))
    (seeds : Measure Seed) [IsProbabilityMeasure seeds]
    (hBudget : (N:ℝ) < ((outer+1:ℕ):ℝ)*(q:ℝ)/128) :
    ∃ frames : Frames A W outer nt, frames ∈ validFrames ∧
      (2/3:ℝ≥0∞) ≤ seeds {seed | (seed,frames) ∉ terminalChamberSuccess c C m0 m1 query out N} := by
  let nu := (frameLaw bA hA).prod (frameLaw bW hW)
  let laws := fun _ : Fin (outer+1) => nu
  let frames : Measure (Frames A W outer nt) := Measure.pi laws
  let mu : Measure (World Seed A W outer nt) := seeds.prod frames
  let zeta : ℝ := 1/(3*((outer+1:ℕ):ℝ))
  haveI : IsProbabilityMeasure (frameLaw bA hA) :=
    Measure.isProbabilityMeasure_map (FangqingAdaptiveHaarProduct.measurable_frame _).aemeasurable
  haveI : IsProbabilityMeasure (frameLaw bW hW) :=
    Measure.isProbabilityMeasure_map (FangqingAdaptiveHaarProduct.measurable_frame _).aemeasurable
  haveI : IsProbabilityMeasure nu := inferInstanceAs (IsProbabilityMeasure ((frameLaw bA hA).prod (frameLaw bW hW)))
  haveI : ∀ t, IsProbabilityMeasure (laws t) := fun _ => inferInstanceAs (IsProbabilityMeasure nu)
  haveI : IsProbabilityMeasure frames := inferInstanceAs (IsProbabilityMeasure (Measure.pi laws))
  haveI : IsProbabilityMeasure mu := inferInstanceAs (IsProbabilityMeasure (seeds.prod frames))
  have hz : 0 < zeta := by dsimp [zeta]; positivity
  have hqr : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hCD0 : 0 < CD := lt_of_lt_of_le zero_lt_one hCD
  have hDimAN : CD*(q:ℝ)^3*Real.log (CD*((N:ℝ)+2)*(q:ℝ)/zeta) ≤ ((dA-1:ℕ):ℝ) :=
    (finite_horizon_dimension_budget_monotone N N0 hNN CD q zeta hCD0 hqr hz).trans hDimA
  have hDimWN : CD*(q:ℝ)^3*Real.log (CD*((N:ℝ)+2)*(q:ℝ)/zeta) ≤ ((dW-(nt+2):ℕ):ℝ) :=
    (finite_horizon_dimension_budget_monotone N N0 hNN CD q zeta hCD0 hqr hz).trans hDimW
  have hbad (packet : Fin (outer+1)) :=
    world_packet_bad_measurable c C m0 m1 hd hdw hp query out hqMeas hout packet N q
  have hprob (packet : Fin (outer+1)) : mu (worldPacketBad c C m0 m1 packet query out N q) ≤ ENNReal.ofReal zeta := by
    have hCE := (hCertified Seed packet query out hqMeas hout N zeta hz hDimAN hDimWN seeds).2
    have hr : mu.real (worldPacketBad c C m0 m1 packet query out N q) ≤ zeta :=
      FangqingAdaptiveHaar.event_bound_of_conditional_indicator mu (originalSideSigma packet)
        (original_side_sigma_le (Seed:=Seed) (A:=A) (W:=W) (nt:=nt) packet) _ (hbad packet) zeta hCE
    rw [← ENNReal.ofReal_toReal (by finiteness : mu (worldPacketBad c C m0 m1 packet query out N q) ≠ (⊤ : ℝ≥0∞))]
    exact ENNReal.ofReal_le_ofReal hr
  have hsuccess := terminal_chamber_success_measurable c C m0 m1 hd hdw hp query out hqMeas hout N
  let bad : Fin (outer+1) → Set ((Frames A W outer nt) × Seed) :=
    fun packet => Prod.swap ⁻¹' worldPacketBad c C m0 m1 packet query out N q
  let success : Set ((Frames A W outer nt) × Seed) :=
    Prod.swap ⁻¹' terminalChamberSuccess c C m0 m1 query out N
  have hswap : MeasurePreserving (Prod.swap : (Frames A W outer nt) × Seed → World Seed A W outer nt)
      (frames.prod seeds) mu := Measure.measurePreserving_swap
  have hbadSwap (packet : Fin (outer+1)) : MeasurableSet (bad packet) := (hbad packet).preimage measurable_swap
  have hprobSwap (packet : Fin (outer+1)) : (frames.prod seeds) (bad packet) ≤ ENNReal.ofReal zeta := by
    rw [show (frames.prod seeds) (bad packet) = mu (worldPacketBad c C m0 m1 packet query out N q) from
      hswap.measure_preimage (hbad packet).nullMeasurableSet]
    exact hprob packet
  have hsuccessSwap : MeasurableSet success := hsuccess.preimage measurable_swap
  have goodSwap (w : (Frames A W outer nt) × Seed) (hg : w ∉ ⋃ packet, bad packet) :
      w.swap ∉ ⋃ packet, worldPacketBad c C m0 m1 packet query out N q := by
    intro h
    obtain ⟨packet,hp⟩ := Set.mem_iUnion.mp h
    exact hg (Set.mem_iUnion.mpr ⟨packet,hp⟩)
  apply fixed_valid_frame_from_success_conditional_serial_steps frames seeds validFrames valid_frames_measurable
    (true_haar_product_ae_valid_frames bA hA bW hW) (outer+1) N (by omega) ((q:ℝ)/16-2)
    (fun w n => serialClock c C m0 m1 query N n w.swap) bad hbadSwap hprobSwap success hsuccessSwap
  · intro w hs hg
    exact (actual_success_conditional_serial_clock_starts_and_ends c C m0 m1 query N w.swap).1
  · intro w hs hg n hn
    exact actual_success_conditional_serial_increments c C m0 m1 query out N q w.swap hs (goodSwap w hg) n hn
  · intro w hs hg
    simpa only [Nat.cast_add,Nat.cast_one] using le_of_eq (actual_success_conditional_serial_clock_starts_and_ends c C m0 m1 query N w.swap).2
  · simpa only [Nat.cast_add,Nat.cast_one] using original_serial_small_budget_absorbs_terminal_plus_one (outer+1) N q (by omega) hq hBudget

end
end FangqingActualProductProbability
end

section
-- Source component: CanonicalRelayStationarity.lean

open scoped ContDiff Topology

namespace FangqingCanonicalRelayStationarity
open FangqingAmplifier FangqingActualInactivePacket FangqingCanonicalLateGateFamily
  FangqingCanonicalRelayParameterFamily FangqingHierarchyBudgetTable FangqingRelayStationarity
  FangqingRelayFenchelInterfaces FangqingPublicShellProfiles FangqingRadialGateBounds
  OriginalPacketOrientationNormalization FangqingRelayAnalyticAssembly
noncomputable section
set_option maxHeartbeats 7000000

variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

def actualPhi {outer nt : ℕ} (c : Config nt)
    (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (p : Parameters A W outer nt) (X : Blocks outer (PhysicalSpace A B W)) : ℝ :=
  sSup (Set.range (FangqingRelayValueBridge.curryF outer c.beta c.lam c.a c.sigma c.reward
    (hZero c C p) (hOne c C p) m0 m1 (gates c C p) X))

/-- A parameter adapter for the SAME Config2/canonical packet family and its
already constructed true maxima. No choice of a new constants tuple, no old
Li/mu factory, and no desired stationary-to-chamber conclusion is assumed. -/
theorem actual_canonical_final_family_stationarity
    {outer nt : ℕ} (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B)
    (p : Parameters A W outer nt) (m0 m1 : Fin (outer+1) → ℝ)
    (L muTarget rho M Ctheta Gap LF RF KD eps : ℝ)
    (X0 : Blocks outer (PhysicalSpace A B W))
    (hbeta : 0 < c.beta) (hmu : 0 < c.mu) (ha : 0 < c.a)
    (hsigma : 0 < c.sigma) (hell : 0 < c.ell)
    (hrel : c.lam^2 = c.beta*c.mu) (hM : 0 ≤ M) (hCt : 0 ≤ Ctheta)
    (hreward : M ≤ c.reward) (hDeriv : ∀ u, |deriv theta u| ≤ Ctheta)
    (hKD : 10 ≤ KD) (heps : 0 ≤ eps) (hscale : c.beta*c.ell = KD*eps)
    (hH1 : ∀ t, AnalyticClass (H1 c (C t) (p t).1 (p t).2) (4*c.mu) LF RF)
    (hMin : ∀ t y, H1 c (C t) (p t).1 (p t).2 (Z c (C t) (p t).1 (p t).2) ≤
      H1 c (C t) (p t).1 (p t).2 y)
    (hFinal : FinalFamily outer c.beta c.lam c.a c.sigma c.reward L muTarget rho M Ctheta
      c.ell Gap (hZero c C p) (hOne c C p) m0 m1 (gates c C p) X0) :
    ∃ Y S : Blocks outer (PhysicalSpace A B W) → (Fin (outer+1) → PhysicalSpace A B W),
      (∀ (X : Blocks outer (PhysicalSpace A B W)) yy ss,
        FangqingRelayStationarity.family outer c.beta c.lam c.a c.sigma c.reward
          (hZero c C p) (hOne c C p) m0 m1 (gates c C p) X.ofLp yy ss ≤
        exactValue outer c.beta c.lam c.a c.sigma c.reward
          (hZero c C p) (hOne c C p) m0 m1 (gates c C p) Y S X) ∧
      Differentiable ℝ (exactValue outer c.beta c.lam c.a c.sigma c.reward
        (hZero c C p) (hOne c C p) m0 m1 (gates c C p) Y S) ∧
      (∀ X, exactValue outer c.beta c.lam c.a c.sigma c.reward
        (hZero c C p) (hOne c C p) m0 m1 (gates c C p) Y S X = actualPhi c C m0 m1 p X) ∧
      actualPhi c C m0 m1 p X0 - sInf (Set.range (actualPhi c C m0 m1 p)) ≤ Gap/2 ∧
      ∀ X : Blocks outer (PhysicalSpace A B W), ‖gradient (actualPhi c C m0 m1 p) X‖ ≤ eps →
        (∀ j : Fin outer, gates c C p j (S X j.castSucc) = 1) ∧
        (∀ t, ‖X t-center c (C t) (p t)‖ ≤ c.ell/8) ∧
        (∀ t, ‖X t-center c (C t) (p t)‖ < 2*c.ell) := by
  obtain ⟨hDelta,hRange,hSmall,hJ,hGrad,hHess,hSC,Y,S,hMax,hDiff,hSup,hGap⟩ := hFinal
  have hPhi : actualPhi c C m0 m1 p =
      exactValue outer c.beta c.lam c.a c.sigma c.reward
        (hZero c C p) (hOne c C p) m0 m1 (gates c C p) Y S := by
    funext X
    exact (hSup X).symm
  refine ⟨Y,S,hMax,hDiff,hSup,?_,?_⟩
  · simpa only [hPhi] using hGap
  · intro X hStationary
    have hwidth : 2*eps ≤ c.beta*c.ell*(3/2) := by nlinarith [hKD]
    have hclose : eps ≤ c.beta*(1/8)*c.ell := by nlinarith [hKD]
    have hscH : ∀ t, StrongConvexOn (Set.univ : Set (PhysicalSpace A B W))
        (3*c.mu+c.mu) (H1 c (C t) (p t).1 (p t).2) := by
      intro t
      convert! (hH1 t).2.1 using 1 <;> ring
    have hdiffH : ∀ t, Differentiable ℝ (H1 c (C t) (p t).1 (p t).2) :=
      fun t => (hH1 t).1.differentiable (by norm_num)
    have hDeltaH : ∀ t z,
        |H0 c (C t) (p t).1 (p t).2 z - H1 c (C t) (p t).1 (p t).2 z +m1 t-m0 t| ≤ M := by
      intro t z
      simpa only [hZero,hOne,reducedZero,reducedOne,
        FangqingRelayFenchelInterfaces.delta_from_H] using hDelta t z
    have hGateEq : ∀ j z, gates c C p j z =
        radialGate theta c.a c.ell (center c (C j.castSucc) (p j.castSucc)) z := by
      intro j z
      exact congrFun (FangqingInitialGateGeometry.scaled_gate_is_original_radial_gate
        c.a c.ell (center c (C j.castSucc) (p j.castSucc))) z
    have hGateFun : gates c C p = fun j =>
        radialGate theta c.a c.ell ((-c.lam/c.beta) • Z c (C j.castSucc) (p j.castSucc).1 (p j.castSucc).2) := by
      funext j z
      exact hGateEq j z
    have hMax' : ∀ (U : Blocks outer (PhysicalSpace A B W)) yy ss,
        FangqingRelayStationarity.family outer c.beta c.lam c.a c.sigma c.reward
          (fun t => fenchelPotential (H0 c (C t) (p t).1 (p t).2) c.mu)
          (fun t => fenchelPotential (H1 c (C t) (p t).1 (p t).2) c.mu) m0 m1
          (fun j => radialGate theta c.a c.ell
            ((-c.lam/c.beta) • Z c (C j.castSucc) (p j.castSucc).1 (p j.castSucc).2)) U.ofLp yy ss ≤
        exactValue outer c.beta c.lam c.a c.sigma c.reward
          (fun t => fenchelPotential (H0 c (C t) (p t).1 (p t).2) c.mu)
          (fun t => fenchelPotential (H1 c (C t) (p t).1 (p t).2) c.mu) m0 m1
          (fun j => radialGate theta c.a c.ell
            ((-c.lam/c.beta) • Z c (C j.castSucc) (p j.castSucc).1 (p j.castSucc).2)) Y S U := by
      simpa only [hGateFun,hZero,hOne,reducedZero,reducedOne,reduced,fenchelPotential] using! hMax
    have hDiff' : Differentiable ℝ (exactValue outer c.beta c.lam c.a c.sigma c.reward
        (fun t => fenchelPotential (H0 c (C t) (p t).1 (p t).2) c.mu)
        (fun t => fenchelPotential (H1 c (C t) (p t).1 (p t).2) c.mu) m0 m1
        (fun j => radialGate theta c.a c.ell
          ((-c.lam/c.beta) • Z c (C j.castSucc) (p j.castSucc).1 (p j.castSucc).2)) Y S) := by
      simpa only [hGateFun,hZero,hOne,reducedZero,reducedOne,reduced,fenchelPotential] using! hDiff
    have hStationary' : ‖gradient (exactValue outer c.beta c.lam c.a c.sigma c.reward
        (fun t => fenchelPotential (H0 c (C t) (p t).1 (p t).2) c.mu)
        (fun t => fenchelPotential (H1 c (C t) (p t).1 (p t).2) c.mu) m0 m1
        (fun j => radialGate theta c.a c.ell
          ((-c.lam/c.beta) • Z c (C j.castSucc) (p j.castSucc).1 (p j.castSucc).2)) Y S) X‖ ≤ eps := by
      rw [hPhi] at hStationary
      simpa only [hGateFun,hZero,hOne,reducedZero,reducedOne,reduced,fenchelPotential] using! hStationary
    have hout := original_packet_relay_stationarity outer c.beta c.mu c.lam (3*c.mu)
      c.a c.sigma c.reward M Ctheta c.ell (3/2) (1/8) eps
      (fun t => H0 c (C t) (p t).1 (p t).2) (fun t => H1 c (C t) (p t).1 (p t).2)
      m0 m1 (fun t => Z c (C t) (p t).1 (p t).2) theta
      hbeta hrel ha hsigma hell (by positivity) hM hCt (by norm_num) hscH hdiffH hMin
      ((theta_smooth.of_le (by decide) : ContDiff ℝ 3 theta).differentiable (by norm_num))
      theta_antitone hDeriv (fun u _ hu => theta_one u (by nlinarith only [hu]))
      hreward hDeltaH hSmall hwidth hclose Y S hMax' X (hDiff' X) hStationary'
    refine ⟨?_,?_,?_⟩
    · intro j
      rw [hGateEq]
      exact hout.1 j
    · intro t
      simpa only [center,div_eq_mul_inv,mul_comm,one_mul] using hout.2 t
    · intro t
      have ht := hout.2 t
      change ‖X t-center c (C t) (p t)‖ ≤ (1/8)*c.ell at ht
      linarith

end
end FangqingCanonicalRelayStationarity
end

section
-- Source component: CanonicalHierarchyGlobalWorld.lean

open scoped ContDiff Topology NNReal

namespace FangqingCanonicalHierarchyGlobalWorld

open FangqingAmplifier FangqingPathEdgeRegularity FangqingActualInactivePacket
  FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
  OriginalPacketOrientationNormalization OriginalPhysicalPacketMinimizer OriginalPacketDistanceGapBounds
  FangqingActualRelayScaling FangqingThirdGroupScaling FangqingRelayAnalyticAssembly FangqingRelayFenchelInterfaces
  FangqingRadialGateBounds FangqingRelayStationarity FangqingHierarchyExternalReserves FangqingHierarchyBudgetTable
  FangqingHierarchyPairedRates FangqingHierarchyInactivePacket FangqingHierarchyAlignment
  FangqingPrivateConstantHierarchy FangqingCanonicalLateGateFamily FangqingHierarchyLateGateWorldFactory
  FangqingCanonicalRelayParameterFamily FangqingActualRelayPublicNormalizers
  FangqingHierarchyCanonicalPacketGeometry FangqingCanonicalRelayStationarity
  FangqingPhysicalRelayExactInitialPoint

noncomputable section
set_option maxHeartbeats 9500000

universe u

/-- The original global builder, retained with its constants rather than independently re-chosen. -/
def RawBuilder (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Cm Cw : ℝ) (Ce : ℝ≥0)
    (K Kc Ks KD csigma Cdelta Ctheta cL cq cg cT : ℝ) : Prop :=
  let Cs := 2*Cw
  let CA := 3+8*Ks*Cs+2*Cw*(Cm+2)
  let CL := 7/2+4*(Ce:ℝ)*Cw*(16*K+(64*K+1)*Kc)
  let Crho := 8*K*(Ce:ℝ)+4*(Ce:ℝ)*(21*K+(64*K+1)*Kc)+Ks*Cs
  ∀ (A0 B0 W : Type u)
    [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [FiniteDimensional ℝ A0]
    [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [FiniteDimensional ℝ B0]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W],
  ∀ (outer nt : ℕ) (C : A0 ≃ₗᵢ[ℝ] B0) (h : Fin (outer + 1) → A0)
    (tail : Fin (outer + 1) → Fin (nt + 2) → W)
    (L mu eps r rhop q delta omega Delta : ℝ),
    (∀ t, ‖h t‖ = 1) → (∀ t, Orthonormal ℝ (tail t)) →
    0 < L → 0 < mu → 0 < eps → 1 ≤ r → 0 < rhop → rhop ≤ rho L mu eps r →
    1 ≤ q → q ^ 2 ≤ cq ^ 2 * (L / mu) → 0 < delta → delta ≤ omega →
    ((nt + 2 : ℕ) : ℝ) ≤ Cm * q → 0 ≤ Delta →
    ((outer + 1 : ℕ) : ℝ) ≤ cT * Delta / energy L eps →
    let Li := 2 * cL * L
    let mui := 2 * mu
    let ri := r / (4 * Real.sqrt cL)
    let scale := cg * rhop
    let barlam := (8 * mui) / scale
    omega = Cw * barlam * q ^ 2 → distanceScale q omega = packetD Li mui KD eps →
    let nu := scale * barlam
    let D := distanceScale q omega
    let A := CA * D
    let R := 2 * A
    let seed := Cs * nu * D
    let Mpath : ℝ := (4 * Ce : ℝ) * scale * omega
    let gain := (64 * K + 1) * Mpath
    let H0 := fun t => inactiveShell (QPhysical q nu C)
      (fun z => scale * pathEdge P delta omega (nt + 2) (physicalFrame C (h t) nt (tail t)) z) R gain
    let H1 := fun t z => H0 t z - localizedSeed theta phi R A (seed * A) (mkPhysical (h t) 0 0) z
    ∃ Z : Fin (outer + 1) → PhysicalSpace A0 B0 W,
      (∀ t, AnalyticClass (H0 t) (4 * mui) (CL * nu * q ^ 2) (Crho * scale)) ∧
      (∀ t, AnalyticClass (H1 t) (4 * mui) (CL * nu * q ^ 2) (Crho * scale)) ∧
      (∀ t y, H0 t 0 ≤ H0 t y) ∧ (∀ t y, H1 t (Z t) ≤ H1 t y) ∧
      (∀ t, ‖Z t‖ ≤ (2 * Cw * (Cm + 2)) * D) ∧
      (∀ t, H1 t 0 - H1 t (Z t) ≤ 4 * Cw ^ 2 * nu * D ^ 2) ∧
      (∀ t (j : Fin (nt + 3)), (j.val : ℝ) ≤ q →
        3 * q * omega ≤ inner ℝ (physicalFrame C (h t) nt (tail t) j) (Z t)) ∧
      (∀ t Y, rawPacket C (h t) nt (tail t) (FlatCubic.edge P delta omega) q nu scale
        (scale * (2 * omega ^ 2 / Real.sqrt q)) (Z t) ≤
        rawPacket C (h t) nt (tail t) (FlatCubic.edge P delta omega) q nu scale
        (scale * (2 * omega ^ 2 / Real.sqrt q)) Y) ∧
      (∀ t Y, ‖Y - Z t‖ ≤ 2 * D → ‖Y‖ < A ∧ ‖Y‖ < R) ∧
      (∀ t, ShellReserves (QPhysical q nu C)
        (pathEdge P delta omega (nt + 2) (physicalFrame C (h t) nt (tail t)))
        (localizedSeed theta phi R A (seed * A) (mkPhysical (h t) (0 : B0) (0 : W)))
        scale R nu K Mpath gain (Ks * (seed * A) / A ^ 2) (nu * (q + 2) + Mpath) ((8 * Ce : ℝ) * scale)) ∧
      (∀ t, PacketTable (QPhysical q nu C)
        (pathEdge P delta omega (nt + 2) (physicalFrame C (h t) nt (tail t)))
        (H0 t) (H1 t) scale L (rho L mu eps r)) ∧
      ∀ center : Fin outer → PhysicalSpace A0 B0 W,
      let a := relayAmplitude 1 (Li / mui) ri
      let ell := width Li mui KD eps
      let rw := reward Cdelta 8 Li KD eps
      let h0 := fun t => reduced (H0 t) mui
      let h1 := fun t => reduced (H1 t) mui
      let m0 := fun t => H0 t 0
      let m1 := fun t => H1 t (Z t)
      let gate := fun j => scaledGate theta (a * ell) (center j)
      let X0 : Blocks outer (PhysicalSpace A0 B0 W) :=
        WithLp.toLp 2 (Fin.cons ((-(seed / lam Li mui)) • mkPhysical (h 0) (0 : B0) (0 : W)) (fun _ => 0))
      RelayTable outer Li (lam Li mui) a (sigma Li a csigma) rw L (rho L mu eps r) h0 h1 m0 m1 gate ∧
      FinalFamily outer Li (lam Li mui) a (sigma Li a csigma) rw L mu (rho L mu eps r)
        (rawBudget Cdelta 8 Li mui KD eps) Ctheta ell Delta h0 h1 m0 m1 gate X0

/-- One constants tuple, chosen before every dimension, frame, horizon and algorithm. -/
structure HierarchyConstants (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Cm Cw : ℝ) where
  Ce : ℝ≥0
  K : ℝ
  Kc : ℝ
  Ks : ℝ
  KD : ℝ
  csigma : ℝ
  Cglobal : ℝ
  Cdelta : ℝ
  Ctheta : ℝ
  Clink : ℝ
  Cgap : ℝ
  cL : ℝ
  cq : ℝ
  cg : ℝ
  cT : ℝ
  hCe : 1 ≤ Ce
  hK : 0 ≤ K
  hKc : 0 ≤ Kc
  hKs : 0 ≤ Ks
  hKD : 1 ≤ KD
  hKD10 : 10 ≤ KD
  hcs : 0 < csigma
  hCG : 0 ≤ Cglobal
  hCD : 0 ≤ Cdelta
  hCt : 0 ≤ Ctheta
  hClink : 0 ≤ Clink
  hGap : 0 ≤ Cgap
  hDeriv : ∀ x : ℝ, |deriv theta x| ≤ Ctheta
  hcL : 0 < cL
  hcL256 : cL ≤ 1/256
  hcq : 0 < cq
  hcq1 : cq ≤ 1
  hcg : 0 < cg
  hcg1 : cg ≤ 1
  hcT : 0 < cT
  alignment : AlignmentAvailable cq cL Cw cg KD
  builder : RawBuilder.{u} P phi Cm Cw Ce K Kc Ks KD csigma Cdelta Ctheta cL cq cg cT

theorem exists_same_actual_hierarchy
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw : ℝ)
    (hCm : 0 ≤ Cm) (hCw : 4*(Cm+2) ≤ Cw)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left)
    (hr : ∀ t, Bp < t → phi t = right) (hcore : ∀ t, |t| < 1 → phi t = t) :
    Nonempty (HierarchyConstants.{u} P phi Cm Cw) := by
  obtain ⟨Ce,hCe,K,Kc,Ks,KD,csigma,Cglobal,Cdelta,Ctheta,Clink,Cgap,
    hK,hKc,hKs,hKD,hKDl,hcs,hCG,hCD,hCt,hClink,hGap,hDeriv,
    cL,cq,cg,cT,hcL,hcL256,hcq,hcq1,hcg,hcg1,hcT,hAlignment,hBuilder⟩ :=
    actual_private_constant_hierarchy.{u} P phi Bp left right Cm Cw 10 hCm hCw (by norm_num) hp hl hr hcore
  exact ⟨⟨Ce,K,Kc,Ks,KD,csigma,Cglobal,Cdelta,Ctheta,Clink,Cgap,cL,cq,cg,cT,
    hCe,hK,hKc,hKs,hKD,hKDl,hcs,hCG,hCD,hCt,hClink,hGap,hDeriv,
    hcL,hcL256,hcq,hcq1,hcg,hcg1,hcT,hAlignment,hBuilder⟩⟩

end
end FangqingCanonicalHierarchyGlobalWorld

namespace FangqingCanonicalHierarchyGlobalWorld
open FangqingAmplifier FangqingActualInactivePacket FangqingCanonicalLateGateFamily FangqingHierarchyLateGateWorldFactory
  FangqingCanonicalRelayParameterFamily FangqingActualRelayPublicNormalizers
  FangqingRelayStationarity FangqingHierarchyBudgetTable FangqingPathEdgeRegularity
  FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
  OriginalPacketOrientationNormalization OriginalPhysicalPacketMinimizer OriginalPacketDistanceGapBounds
  OriginalCanonicalPacketTailSupport FangqingActualRelayScaling FangqingThirdGroupScaling
  FangqingRelayFenchelInterfaces FangqingCanonicalRelayStationarity
  FangqingPhysicalRelayExactInitialPoint
noncomputable section
set_option maxHeartbeats 9500000
universe u

variable {A B W : Type u}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

def actualInitial {outer nt : ℕ} (c : Config nt) (p : Parameters A W outer nt) :
    Blocks outer (PhysicalSpace A B W) :=
  WithLp.toLp 2 (Fin.cons ((-(c.seed/c.lam)) • mkPhysical (p 0).1 (0:B) (0:W)) (fun _ => 0))

/-- Actual global family with public frame-independent normalizers and the exact displayed dual start. -/
structure CanonicalWorld {outer nt : ℕ} (c : Config nt) (C : A ≃ₗᵢ[ℝ] B)
    (p : Parameters A W outer nt) (hRef : A) (tailRef : Fin (nt+2) → W)
    (L muTarget rho M Ctheta Gap Cmin eps LF RF : ℝ) : Prop where
  analyticZero : ∀ t, AnalyticClass (H0 c C (p t).1 (p t).2) (4*c.mu) LF RF
  analyticOne : ∀ t, AnalyticClass (H1 c C (p t).1 (p t).2) (4*c.mu) LF RF
  minZero : ∀ t y, H0 c C (p t).1 (p t).2 0 ≤ H0 c C (p t).1 (p t).2 y
  minOne : ∀ t y, H1 c C (p t).1 (p t).2 (Z c C (p t).1 (p t).2) ≤ H1 c C (p t).1 (p t).2 y
  publicNormalizers : ∀ t,
    H0 c C (p t).1 (p t).2 0 = publicZeroNormalizer c C hRef tailRef ∧
    H1 c C (p t).1 (p t).2 (Z c C (p t).1 (p t).2) = publicOneNormalizer c C hRef tailRef
  canonicalNorm : ∀ t, ‖Z c C (p t).1 (p t).2‖ ≤ Cmin*distanceScale c.q c.omega
  canonicalBulk : ∀ t (j : Fin (nt+3)), (j.val:ℝ) ≤ c.q →
    3*c.q*c.omega ≤ inner ℝ (physicalFrame C (p t).1 nt (p t).2 j) (Z c C (p t).1 (p t).2)
  finalFamily : FinalFamily outer c.beta c.lam c.a c.sigma c.reward L muTarget rho M Ctheta c.ell Gap
    (hZero c (fun _ => C) p) (hOne c (fun _ => C) p)
    (fun _ => publicZeroNormalizer c C hRef tailRef) (fun _ => publicOneNormalizer c C hRef tailRef)
    (gates c (fun _ => C) p) (actualInitial c p)
  exactInitial : ∀ yy ss : Fin (outer+1) → PhysicalSpace A B W,
    FangqingRelayStationarity.family outer c.beta c.lam c.a c.sigma c.reward
      (hZero c (fun _ => C) p) (hOne c (fun _ => C) p)
      (fun _ => publicZeroNormalizer c C hRef tailRef) (fun _ => publicOneNormalizer c C hRef tailRef)
      (gates c (fun _ => C) p) (actualInitial c p).ofLp yy ss ≤
    FangqingRelayStationarity.family outer c.beta c.lam c.a c.sigma c.reward
      (hZero c (fun _ => C) p) (hOne c (fun _ => C) p)
      (fun _ => publicZeroNormalizer c C hRef tailRef) (fun _ => publicOneNormalizer c C hRef tailRef)
      (gates c (fun _ => C) p) (actualInitial c p).ofLp 0 (fun t => c.a • actualInitial c p t)
  differentiablePhi : Differentiable ℝ (actualPhi c (fun _ => C)
    (fun _ => publicZeroNormalizer c C hRef tailRef) (fun _ => publicOneNormalizer c C hRef tailRef) p)
  gapPhi :
    (actualPhi c (fun _ => C)
      (fun _ => publicZeroNormalizer c C hRef tailRef) (fun _ => publicOneNormalizer c C hRef tailRef) p) (actualInitial c p) -
      sInf (Set.range (actualPhi c (fun _ => C)
        (fun _ => publicZeroNormalizer c C hRef tailRef) (fun _ => publicOneNormalizer c C hRef tailRef) p)) ≤ Gap/2
  stationaryChambers : ∀ X : Blocks outer (PhysicalSpace A B W),
    ‖gradient (actualPhi c (fun _ => C)
      (fun _ => publicZeroNormalizer c C hRef tailRef) (fun _ => publicOneNormalizer c C hRef tailRef) p) X‖ ≤ eps →
    ∀ t, ‖X t-center c C (p t)‖ < 2*c.ell

theorem same_constants_canonical_global_world
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Cm Cw : ℝ)
    (H : HierarchyConstants.{u} P phi Cm Cw)
    (hCm : 0 ≤ Cm) (hCw : 4*(Cm+2) ≤ Cw) (hcore : ∀ t, |t| < 1 → phi t = t)
    (outer nt q : ℕ) (C : A ≃ₗᵢ[ℝ] B) (p : Parameters A W outer nt)
    (hRef : A) (hhRef : ‖hRef‖=1) (tailRef : Fin (nt+2) → W) (htRef : Orthonormal ℝ tailRef)
    (L mu eps r rhop delta omega Delta : ℝ)
    (hh : ∀ t, ‖(p t).1‖=1) (ht : ∀ t, Orthonormal ℝ (p t).2)
    (hL : 0 < L) (hmu : 0 < mu) (heps : 0 < eps) (hr : 1 ≤ r)
    (hrhop : 0 < rhop) (hrho : rhop ≤ rho L mu eps r)
    (hq : 1 ≤ q) (hfit : q ≤ nt+2) (hqcap : (q:ℝ)^2 ≤ H.cq^2*(L/mu))
    (hd : 0 < delta) (hdw : delta ≤ omega) (hn : ((nt+2:ℕ):ℝ) ≤ Cm*(q:ℝ))
    (hDelta : 0 ≤ Delta) (hCount : ((outer+1:ℕ):ℝ) ≤ H.cT*Delta/energy L eps)
    (homega : omega = Cw*((8*(2*mu))/(H.cg*rhop))*(q:ℝ)^2)
    (hD : distanceScale q omega = packetD (2*H.cL*L) (2*mu) H.KD eps) :
    let c := originalConfig2 P phi nt H.Ce H.K H.Ks Cm Cw H.KD H.csigma H.Cdelta H.cL H.cg
      L mu eps r rhop q delta omega
    let CL := 7/2+4*(H.Ce:ℝ)*Cw*(16*H.K+(64*H.K+1)*H.Kc)
    let Crho := 8*H.K*(H.Ce:ℝ)+4*(H.Ce:ℝ)*(21*H.K+(64*H.K+1)*H.Kc)+H.Ks*(2*Cw)
    CanonicalWorld c C p hRef tailRef L mu (rho L mu eps r)
      (rawBudget H.Cdelta 8 c.beta c.mu H.KD eps) H.Ctheta Delta (2*Cw*(Cm+2)) eps
      (CL*(c.scale*c.barlam)*(q:ℝ)^2) (Crho*c.scale) := by
  intro c CL Crho
  have hcL := H.hcL
  have hcg := H.hcg
  have hKs := H.hKs
  have hKD := H.hKD
  have hcs := H.hcs
  have hCD := H.hCD
  let Li := 2*H.cL*L
  let mui := 2*mu
  let scale := H.cg*rhop
  let barlam := 8*mui/scale
  have hLi : 0 < Li := by dsimp [Li]; positivity
  have hmui : 0 < mui := by dsimp [mui]; positivity
  have hs : 0 < scale := by dsimp [scale]; positivity
  have hb : 0 < barlam := by dsimp [barlam]; positivity
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hw : 0 < omega := hd.trans_le hdw
  have hCw0 : 0 < Cw := by linarith only [hCm,hCw]
  obtain ⟨Zraw,hH0,hH1,hMin0,hMin1,hNorm,hLocalGap,hBulk,hRawMin,hChamber,hReserve,hTable,hCenters⟩ :=
    H.builder A B W outer nt C (fun t => (p t).1) (fun t => (p t).2)
      L mu eps r rhop q delta omega Delta hh ht hL hmu heps hr hrhop hrho hqR hqcap
      hd hdw hn hDelta hCount homega hD
  have hCanon : ∀ t, Zraw t = Z c C (p t).1 (p t).2 := by
    intro t
    exact actual_raw_minimizer_uses_public_coefficients P C (p t).1 (hh t) nt (p t).2 (ht t)
      delta omega q scale barlam hd hdw (by positivity) hs hb (Zraw t) (hRawMin t)
  have hZfun : Zraw = fun t => Z c C (p t).1 (p t).2 := funext hCanon
  rw [hZfun] at hMin1 hNorm hBulk hCenters
  have hH0' : ∀ t, AnalyticClass (H0 c C (p t).1 (p t).2) (4*c.mu)
      (CL*(c.scale*c.barlam)*(q:ℝ)^2) (Crho*c.scale) := hH0
  have hH1' : ∀ t, AnalyticClass (H1 c C (p t).1 (p t).2) (4*c.mu)
      (CL*(c.scale*c.barlam)*(q:ℝ)^2) (Crho*c.scale) := hH1
  have hMin0' : ∀ t y, H0 c C (p t).1 (p t).2 0 ≤ H0 c C (p t).1 (p t).2 y := hMin0
  have hMin1' : ∀ t y, H1 c C (p t).1 (p t).2 (Z c C (p t).1 (p t).2) ≤ H1 c C (p t).1 (p t).2 y := hMin1
  have hPublic : ∀ t,
      H0 c C (p t).1 (p t).2 0 = publicZeroNormalizer c C hRef tailRef ∧
      H1 c C (p t).1 (p t).2 (Z c C (p t).1 (p t).2) = publicOneNormalizer c C hRef tailRef := by
    intro t
    exact actual_public_normalizers_are_actual_endpoint_minima c C hRef hhRef tailRef htRef
      (p t).1 (hh t) (p t).2 (ht t) (hMin0' t) (hMin1' t)
  have hm0 : (fun t => H0 c C (p t).1 (p t).2 0) =
      (fun _ : Fin (outer+1) => publicZeroNormalizer c C hRef tailRef) := funext (fun t => (hPublic t).1)
  have hm1 : (fun t => H1 c C (p t).1 (p t).2 (Z c C (p t).1 (p t).2)) =
      (fun _ : Fin (outer+1) => publicOneNormalizer c C hRef tailRef) := funext (fun t => (hPublic t).2)
  obtain ⟨hRelay,hFinal⟩ := hCenters (fun j => c.a • center c C (p j.castSucc))
  change FinalFamily outer c.beta c.lam c.a c.sigma c.reward L mu (rho L mu eps r)
    (rawBudget H.Cdelta 8 c.beta c.mu H.KD eps) H.Ctheta c.ell Delta
    (hZero c (fun _ => C) p) (hOne c (fun _ => C) p)
    (fun t => H0 c C (p t).1 (p t).2 0)
    (fun t => H1 c C (p t).1 (p t).2 (Z c C (p t).1 (p t).2))
    (gates c (fun _ => C) p) (actualInitial c p) at hFinal
  rw [hm0,hm1] at hFinal
  have hA : 0 < c.A := by change 0 < (3+8*H.Ks*(2*Cw)+2*Cw*(Cm+2))*distanceScale q omega; unfold distanceScale; positivity
  have hR : 0 < c.R := by change 0 < 2*c.A; positivity
  have hbeta : 0 < c.beta := hLi
  have hlam : 0 < c.lam := by change 0 < lam Li mui; unfold lam; positivity
  have ha : 0 < c.a := by
    change 0 < relayAmplitude 1 (Li/mui) (r/(4*Real.sqrt H.cL))
    unfold relayAmplitude
    simpa only [one_mul] using lt_of_lt_of_le zero_lt_one (le_max_left 1 (((Li/mui)^(3/2:ℝ)/(r/(4*Real.sqrt H.cL)))^(1/3:ℝ)))
  have hell : 0 < c.ell := by
    change 0 < width Li mui H.KD eps
    rw [width_eq_actual Li mui H.KD eps hLi hmui]
    positivity
  have hsigma : 0 < c.sigma := by change 0 < sigma Li c.a H.csigma; unfold sigma; positivity
  have hM : 0 ≤ rawBudget H.Cdelta 8 c.beta c.mu H.KD eps := by unfold rawBudget packetD; positivity
  have hReward : rawBudget H.Cdelta 8 c.beta c.mu H.KD eps ≤ c.reward := by
    change rawBudget H.Cdelta 8 Li mui H.KD eps ≤ reward H.Cdelta 8 Li H.KD eps
    rw [reward_eq_two_raw_plus_energy H.Cdelta 8 Li mui H.KD eps hLi hmui]
    have hE : 0 ≤ energy Li eps := by unfold energy; positivity
    have hMraw : 0 ≤ rawBudget H.Cdelta 8 Li mui H.KD eps := hM
    linarith only [hMraw,hE]
  have hEllScale : c.ell = c.lam/c.beta*distanceScale q omega := by
    change width Li mui H.KD eps = lam Li mui/Li*distanceScale q omega
    rw [hD]
    unfold width
    ring
  have hLamRel : c.lam^2 = c.beta*c.mu := by
    change (lam Li mui)^2 = Li*mui
    unfold lam
    rw [Real.sq_sqrt (by positivity)]
  have hScale : c.beta*c.ell = H.KD*eps := by
    change Li*width Li mui H.KD eps = H.KD*eps
    rw [width_eq_actual Li mui H.KD eps hLi hmui]
    field_simp
  obtain ⟨Y,S,hMax,hDiff,hSup,hGap,hStat⟩ := actual_canonical_final_family_stationarity
    c (fun _ => C) p (fun _ => publicZeroNormalizer c C hRef tailRef)
      (fun _ => publicOneNormalizer c C hRef tailRef) L mu (rho L mu eps r)
      (rawBudget H.Cdelta 8 c.beta c.mu H.KD eps) H.Ctheta Delta
      (CL*(c.scale*c.barlam)*(q:ℝ)^2) (Crho*c.scale) H.KD eps (actualInitial c p)
      hbeta hmui ha hsigma hell hLamRel hM H.hCt hReward H.hDeriv H.hKD10 heps.le hScale
      hH1' hMin1' hFinal
  have hPhi : actualPhi c (fun _ => C)
      (fun _ => publicZeroNormalizer c C hRef tailRef) (fun _ => publicOneNormalizer c C hRef tailRef) p =
      exactValue outer c.beta c.lam c.a c.sigma c.reward
        (hZero c (fun _ => C) p) (hOne c (fun _ => C) p)
        (fun _ => publicZeroNormalizer c C hRef tailRef) (fun _ => publicOneNormalizer c C hRef tailRef)
        (gates c (fun _ => C) p) Y S := funext (fun X => (hSup X).symm)
  have hExact := displayed_physical_initial_point_exact P phi hcore outer nt q C
    (fun t => (p t).1) (fun t => (p t).2) (fun t => Z c C (p t).1 (p t).2) hh ht hq hfit
    delta omega (scale*barlam) scale c.R c.A c.seed c.gain c.mu (4*c.mu)
    (CL*(c.scale*c.barlam)*(q:ℝ)^2) (Crho*c.scale) c.beta c.lam c.a c.ell c.sigma c.reward
    (rawBudget H.Cdelta 8 c.beta c.mu H.KD eps) hR hA hw.le hbeta hlam ha hell hEllScale
    (by change 0 ≤ 4*mui-mui; linarith only [hmui]) hsigma.le hM hReward hH0' hH1' hMin0' hBulk
    (by
      intro t z
      change |FangqingRelayStationarity.delta
        (reduced (H0 c C (p t).1 (p t).2) c.mu)
        (reduced (H1 c C (p t).1 (p t).2) c.mu)
        (H0 c C (p t).1 (p t).2 0) (H1 c C (p t).1 (p t).2 (Z c C (p t).1 (p t).2)) z| ≤ _
      rw [(hPublic t).1,(hPublic t).2]
      exact hFinal.1 t z)
  refine ⟨hH0',hH1',hMin0',hMin1',hPublic,hNorm,hBulk,hFinal,?_,?_,hGap,?_⟩
  · have he := hExact.2
    change (∀ yy ss : Fin (outer+1) → PhysicalSpace A B W,
      FangqingRelayStationarity.family outer c.beta c.lam c.a c.sigma c.reward
        (hZero c (fun _ => C) p) (hOne c (fun _ => C) p)
        (fun t => H0 c C (p t).1 (p t).2 0)
        (fun t => H1 c C (p t).1 (p t).2 (Z c C (p t).1 (p t).2))
        (gates c (fun _ => C) p) (actualInitial c p).ofLp yy ss ≤
      FangqingRelayStationarity.family outer c.beta c.lam c.a c.sigma c.reward
        (hZero c (fun _ => C) p) (hOne c (fun _ => C) p)
        (fun t => H0 c C (p t).1 (p t).2 0)
        (fun t => H1 c C (p t).1 (p t).2 (Z c C (p t).1 (p t).2))
        (gates c (fun _ => C) p) (actualInitial c p).ofLp 0 (fun t => c.a • actualInitial c p t)) at he
    simpa only [hm0,hm1] using he
  · rw [hPhi]
    exact hDiff
  · intro X hX
    exact (hStat X hX).2.2

end
end FangqingCanonicalHierarchyGlobalWorld

namespace FangqingCanonicalHierarchyGlobalWorld
open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingHierarchyLateGateWorldFactory
  FangqingCanonicalRelayParameterFamily FangqingActualRelayScaling FangqingThirdGroupScaling
  FangqingRelayStationarity FangqingHierarchyAlignment OriginalPacketDistanceGapBounds
  OriginalPacketOrientationNormalization
noncomputable section
set_option maxHeartbeats 9500000
universe u

/-- Each first-hit packet geometry is obtained from the retained global builder. -/
theorem same_constants_all_packet_geometry
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Cm Cw : ℝ)
    (H : HierarchyConstants.{u} P phi Cm Cw)
    (hCm : 0 ≤ Cm) (hCw : 4*(Cm+2) ≤ Cw) (hcore : ∀ t, |t| < 1 → phi t = t)
    (A B W : Type u)
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (nt q : ℕ) (C : A ≃ₗᵢ[ℝ] B) (L mu eps r rhop delta omega : ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (heps : 0 < eps) (hr : 1 ≤ r)
    (hrhop : 0 < rhop) (hrho : rhop ≤ rho L mu eps r)
    (hq : 1 ≤ q) (hfit : q ≤ nt+2) (hqcap : (q:ℝ)^2 ≤ H.cq^2*(L/mu))
    (hd : 0 < delta) (hdw : delta ≤ omega) (hn : ((nt+2:ℕ):ℝ) ≤ Cm*(q:ℝ))
    (homega : omega = Cw*((8*(2*mu))/(H.cg*rhop))*(q:ℝ)^2)
    (hD : distanceScale q omega = packetD (2*H.cL*L) (2*mu) H.KD eps) :
    let c := originalConfig2 P phi nt H.Ce H.K H.Ks Cm Cw H.KD H.csigma H.Cdelta H.cL H.cg
      L mu eps r rhop q delta omega
    let Cmin := 2*Cw*(Cm+2)
    let CA := 3+8*H.Ks*(2*Cw)+Cmin
    let CR := 4*CA+Cmin+3
    0 < c.R ∧ 0 < c.beta ∧ 0 < c.lam ∧ 0 < c.a ∧
    c.ell = c.lam/c.beta*distanceScale q omega ∧ 0 < CR ∧ Cmin+3 ≤ CR ∧
    2*c.R ≤ CR*distanceScale q omega ∧
    ∀ (h : A) (tail : Fin (nt+2) → W), ‖h‖=1 → Orthonormal ℝ tail →
      (∀ y, H0 c C h tail 0 ≤ H0 c C h tail y) ∧
      (∀ y, H1 c C h tail (Z c C h tail) ≤ H1 c C h tail y) ∧
      ‖Z c C h tail‖ ≤ Cmin*distanceScale q omega ∧
      ∀ j : Fin (nt+3), (j.val:ℝ) ≤ q →
        3*(q:ℝ)*omega ≤ inner ℝ (physicalFrame C h nt tail j) (Z c C h tail) := by
  intro c Cmin CA CR
  have hcL := H.hcL
  have hKs := H.hKs
  have hCw0 : 0 < Cw := by linarith only [hCm,hCw]
  have hw : 0 < omega := hd.trans_le hdw
  have hDpos : 0 < distanceScale q omega := by unfold distanceScale; positivity
  have hLi : 0 < 2*H.cL*L := by positivity
  have hmui : 0 < 2*mu := by positivity
  have hCA : 0 < CA := by dsimp [CA,Cmin]; positivity
  have hCmin : 0 < Cmin := by dsimp [Cmin]; positivity
  have hCR : 0 < CR := by dsimp [CR]; positivity
  have hBeta : 0 < c.beta := hLi
  have hLam : 0 < c.lam := by change 0 < lam (2*H.cL*L) (2*mu); unfold lam; positivity
  have hRadius : 0 < c.R := by change 0 < 2*(CA*distanceScale q omega); positivity
  have hAmp : 0 < c.a := by
    change 0 < relayAmplitude 1 ((2*H.cL*L)/(2*mu)) (r/(4*Real.sqrt H.cL))
    unfold relayAmplitude
    simpa only [one_mul] using lt_of_lt_of_le zero_lt_one
      (le_max_left 1 ((((2*H.cL*L)/(2*mu))^(3/2:ℝ)/(r/(4*Real.sqrt H.cL)))^(1/3:ℝ)))
  have hEll : c.ell = c.lam/c.beta*distanceScale q omega := by
    change width (2*H.cL*L) (2*mu) H.KD eps = lam (2*H.cL*L) (2*mu)/(2*H.cL*L)*distanceScale q omega
    rw [hD]
    unfold width
    ring
  refine ⟨hRadius,hBeta,hLam,hAmp,hEll,hCR,?_,?_,?_⟩
  · dsimp [CR]
    linarith only [hCA]
  · change 2*(2*(CA*distanceScale q omega)) ≤ CR*distanceScale q omega
    dsimp [CR]
    nlinarith only [hCmin,hDpos]
  · intro h tail hh ht
    let Delta := energy L eps/H.cT
    have hE : 0 < energy L eps := by unfold energy; positivity
    have hcT := H.hcT
    have hDelta : 0 ≤ Delta := by dsimp [Delta]; positivity
    have hCount : ((0+1:ℕ):ℝ) ≤ H.cT*Delta/energy L eps := by
      dsimp [Delta]
      norm_num
      field_simp [hcT.ne',hE.ne']
      <;> norm_num
    have hWorld := same_constants_canonical_global_world P phi Cm Cw H hCm hCw hcore
      0 nt q C (fun _ => (h,tail)) h hh tail ht L mu eps r rhop delta omega Delta
      (fun _ => hh) (fun _ => ht) hL hmu heps hr hrhop hrho hq hfit hqcap
      hd hdw hn hDelta hCount homega hD
    exact ⟨hWorld.minZero 0,hWorld.minOne 0,hWorld.canonicalNorm 0,hWorld.canonicalBulk 0⟩

end
end FangqingCanonicalHierarchyGlobalWorld
end

section
-- Source component: CanonicalProductGradientFailure.lean

open MeasureTheory
open scoped ENNReal

namespace FangqingCanonicalProductGradientFailure

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingOriginalPacketWorld FangqingOriginalWorldFirstHit FangqingOriginalWorldExecutionCoordinates
  FangqingActualSerialFirstHitGeometry FangqingActualProductFrameSupport FangqingActualProductProbability
  FangqingCanonicalRelayStationarity FangqingCanonicalHierarchyGlobalWorld FangqingActualRelayPublicNormalizers
  FangqingActualPaddedRelayReplies FangqingRelayStationarity FangqingAdaptiveHaarOriginal

noncomputable section
set_option maxHeartbeats 6000000

universe u v
variable {A B W : Type u} {Seed : Type v}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace A] [BorelSpace A] [MeasurableSpace W] [BorelSpace W]
  [Nontrivial A] [Nontrivial W] [SecondCountableTopology A] [SecondCountableTopology W]
  [MeasurableSpace (PhysicalSpace A B W)] [BorelSpace (PhysicalSpace A B W)]
  [SecondCountableTopology (PhysicalSpace A B W)]
  [MeasurableSpace Seed] {outer nt : ℕ}
  [MeasurableSpace (Point A B W outer)] [BorelSpace (Point A B W outer)]
  [MeasurableSpace (Point A B W outer →L[ℝ] Point A B W outer)] [BorelSpace (Point A B W outer →L[ℝ] Point A B W outer)]

def frameParameters (frames : Frames A W outer nt) : Parameters A W outer nt :=
  fun t => ((frames t).1 0,(frames t).2)

def primalBlocks (point : Point A B W outer) : Blocks outer (PhysicalSpace A B W) :=
  WithLp.toLp 2 (fun t => point (0,t))

theorem global_public_input_has_actual_displayed_primal_initial
    (c : Config nt) (seed : Seed) (frames : Frames A W outer nt) :
    primalBlocks (B:=B) (globalPublicInput c (seed,frames)) = actualInitial (B:=B) c (frameParameters frames) := by
  apply PiLp.ext
  intro t
  refine Fin.cases ?_ (fun j => ?_) t
  · simp only [primalBlocks,globalPublicInput,actualInitial,FangqingActualPaddedRelayReplies.public_initial_x,
      if_true,frameParameters,globalParameters,Fin.cons_zero]
  · have hj : j.succ ≠ (0 : Fin (outer+1)) := by intro h; have hv := congrArg Fin.val h; simp only [Fin.val_succ,Fin.val_zero] at hv; omega
    simp only [primalBlocks,globalPublicInput,actualInitial,FangqingActualPaddedRelayReplies.public_initial_x,
      if_neg hj,Fin.cons_succ]

theorem actual_phi_stationarity_forces_terminal_chamber_success
    (c : Config nt) (C : A ≃ₗᵢ[ℝ] B) (hRef : A) (tailRef : Fin (nt+2) → W)
    (L mu rho M Ctheta Gap Cmin eps LF RF : ℝ) (frames : Frames A W outer nt)
    (hWorld : CanonicalWorld c C (frameParameters frames) hRef tailRef L mu rho M Ctheta Gap Cmin eps LF RF)
    (query : OriginalQuery Seed A B W outer) (out : OriginalOutput Seed A B W outer) (N : ℕ) (seed : Seed)
    (hStationary : ‖gradient (actualPhi c (fun _ => C)
      (fun _ => publicZeroNormalizer c C hRef tailRef) (fun _ => publicOneNormalizer c C hRef tailRef) (frameParameters frames))
      (primalBlocks (globalOutput c (fun _ => C) (fun _ => publicZeroNormalizer c C hRef tailRef)
        (fun _ => publicOneNormalizer c C hRef tailRef) query out N (seed,frames)))‖ ≤ eps) :
    (seed,frames) ∈ terminalChamberSuccess c (fun _ => C) (fun _ => publicZeroNormalizer c C hRef tailRef)
      (fun _ => publicOneNormalizer c C hRef tailRef) query out N := by
  intro packet
  apply decide_eq_true
  have h := hWorld.stationaryChambers _ hStationary packet
  simpa only [primalBlocks,PiLp.toLp_apply,globalPrimalHit,packetOutputHit,frameParameters] using h

theorem actual_fixed_valid_world_with_gradient_failure
    (c : Config nt) (C : A ≃ₗᵢ[ℝ] B) (hRef : A) (tailRef : Fin (nt+2) → W)
    (L mu rho M Ctheta Gap Cmin eps LF RF : ℝ)
    (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hp : ContDiff ℝ 3 c.phi)
    (q : ℕ) (hq : 128 ≤ q) (CD : ℝ) (hCD : 1 ≤ CD)
    {dA dW : ℕ} (bA : OrthonormalBasis (Fin dA) ℝ A) (hA : 1 ≤ dA)
    (bW : OrthonormalBasis (Fin dW) ℝ W) (hW : nt+2 ≤ dW)
    (hCertified : OriginalWorldAlgorithms.{u,v} c (fun _ : Fin (outer+1) => C)
      (fun _ => publicZeroNormalizer c C hRef tailRef) (fun _ => publicOneNormalizer c C hRef tailRef) q CD bA hA bW hW)
    (hWorlds : ∀ frames : Frames A W outer nt, frames ∈ validFrames →
      CanonicalWorld c C (frameParameters frames) hRef tailRef L mu rho M Ctheta Gap Cmin eps LF RF)
    (query : OriginalQuery Seed A B W outer) (out : OriginalOutput Seed A B W outer)
    (hqMeas : ∀ n, Measurable (fun x : Seed × Point A B W outer × (ℕ → Response A B W outer) => query n x.1 x.2.1 x.2.2))
    (hout : Measurable (fun x : Seed × Point A B W outer × (ℕ → Response A B W outer) => out x.1 x.2.1 x.2.2))
    (N0 N : ℕ) (hNN : N ≤ N0)
    (hDimA : CD*(q:ℝ)^3*Real.log (CD*((N0:ℝ)+2)*(q:ℝ)/(1/(3*((outer+1:ℕ):ℝ)))) ≤ ((dA-1:ℕ):ℝ))
    (hDimW : CD*(q:ℝ)^3*Real.log (CD*((N0:ℝ)+2)*(q:ℝ)/(1/(3*((outer+1:ℕ):ℝ)))) ≤ ((dW-(nt+2):ℕ):ℝ))
    (seeds : Measure Seed) [IsProbabilityMeasure seeds]
    (hBudget : (N:ℝ) < ((outer+1:ℕ):ℝ)*(q:ℝ)/128) :
    ∃ frames : Frames A W outer nt, frames ∈ validFrames ∧
      CanonicalWorld c C (frameParameters frames) hRef tailRef L mu rho M Ctheta Gap Cmin eps LF RF ∧
      (2/3:ℝ≥0∞) ≤ seeds {seed | eps < ‖gradient (actualPhi c (fun _ => C)
        (fun _ => publicZeroNormalizer c C hRef tailRef) (fun _ => publicOneNormalizer c C hRef tailRef) (frameParameters frames))
        (primalBlocks (globalOutput c (fun _ => C) (fun _ => publicZeroNormalizer c C hRef tailRef)
          (fun _ => publicOneNormalizer c C hRef tailRef) query out N (seed,frames)))‖} := by
  obtain ⟨frames,hvalid,hFailure⟩ := actual_fixed_valid_frame_with_chamber_failure c (fun _ => C)
    (fun _ => publicZeroNormalizer c C hRef tailRef) (fun _ => publicOneNormalizer c C hRef tailRef)
    hd hdw hp q hq CD hCD bA hA bW hW hCertified query out hqMeas hout N0 N hNN hDimA hDimW seeds hBudget
  have hWorld := hWorlds frames hvalid
  refine ⟨frames,hvalid,hWorld,hFailure.trans (measure_mono ?_)⟩
  intro seed hnot
  change eps < _
  apply lt_of_not_ge
  intro hStationary
  exact hnot (actual_phi_stationarity_forces_terminal_chamber_success c C hRef tailRef
    L mu rho M Ctheta Gap Cmin eps LF RF frames hWorld query out N seed hStationary)

end
end FangqingCanonicalProductGradientFailure
end

section
-- Source component: CanonicalHierarchyProduct.lean

open MeasureTheory
open scoped ENNReal

namespace FangqingCanonicalHierarchyProduct

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingHierarchyLateGateWorldFactory FangqingActualRelayScaling FangqingThirdGroupScaling
  FangqingCanonicalHierarchyGlobalWorld FangqingCanonicalRelayStationarity
  FangqingCanonicalProductGradientFailure FangqingActualProductFrameSupport
  FangqingOriginalWorldExecutionCoordinates FangqingActualRelayPublicNormalizers
  FangqingFirstHitModelFromGeometry FangqingActualFirstHitOriginalDimension
  FangqingRelayStationarity FangqingAdaptiveHaarOriginal FangqingActualPaddedRelayReplies OriginalPacketDistanceGapBounds FangqingOriginalWorldFirstHit

noncomputable section
set_option maxHeartbeats 9500000
universe u v

def productDimensionConstant (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Cm Cw : ℝ)
    (H : HierarchyConstants.{u} P phi Cm Cw) : ℝ :=
  dimensionConstant (4*(3+8*H.Ks*(2*Cw)+2*Cw*(Cm+2))+2*Cw*(Cm+2)+3) (1/8) Cm

def productConfig (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Cm Cw : ℝ)
    (H : HierarchyConstants.{u} P phi Cm Cw) (nt q : ℕ) (L mu eps r rhop omega : ℝ) : Config nt :=
  originalConfig2 P phi nt H.Ce H.K H.Ks Cm Cw H.KD H.csigma H.Cdelta H.cL H.cg
    L mu eps r rhop q ((1/8)*omega) omega

/-- The full original serial-product assertion for one constants tuple.
Every oracle below is the literal full F_T jet oracle, and the private seed is independent.
The reference frames specify only public normalizers and are not the selected hard frames. -/
def ProductGuarantee (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Cm Cw : ℝ)
    (H : HierarchyConstants.{u} P phi Cm Cw) : Prop :=
  ∀ (A B W : Type u) (Seed : Type v)
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace W] [BorelSpace W]
    [Nontrivial A] [Nontrivial W] [SecondCountableTopology A] [SecondCountableTopology W]
    [MeasurableSpace (PhysicalSpace A B W)] [BorelSpace (PhysicalSpace A B W)]
    [SecondCountableTopology (PhysicalSpace A B W)] [MeasurableSpace Seed],
  ∀ (outer nt q : ℕ)
    [MeasurableSpace (Point A B W outer)] [BorelSpace (Point A B W outer)]
    [MeasurableSpace (Point A B W outer →L[ℝ] Point A B W outer)]
    [BorelSpace (Point A B W outer →L[ℝ] Point A B W outer)]
    (C : A ≃ₗᵢ[ℝ] B) (hRef : A) (tailRef : Fin (nt+2) → W)
    (hhRef : ‖hRef‖=1) (htRef : Orthonormal ℝ tailRef)
    (L mu eps r rhop omega Delta : ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (heps : 0 < eps) (hr : 1 ≤ r)
    (hrhop : 0 < rhop) (hrho : rhop ≤ rho L mu eps r)
    (hq : 128 ≤ q) (hfit : q ≤ nt+2) (hqcap : (q:ℝ)^2 ≤ H.cq^2*(L/mu))
    (hw : 0 < omega) (hn : ((nt+2:ℕ):ℝ) ≤ Cm*(q:ℝ))
    (hDelta : 0 ≤ Delta) (hCount : ((outer+1:ℕ):ℝ) ≤ H.cT*Delta/energy L eps)
    (homega : omega = Cw*((8*(2*mu))/(H.cg*rhop))*(q:ℝ)^2)
    (hD : distanceScale q omega = packetD (2*H.cL*L) (2*mu) H.KD eps)
    {dA dW : ℕ} (bA : OrthonormalBasis (Fin dA) ℝ A) (hA : 1 ≤ dA)
    (bW : OrthonormalBasis (Fin dW) ℝ W) (hW : nt+2 ≤ dW)
    (N0 N : ℕ) (hNN : N ≤ N0)
    (hDimA : productDimensionConstant P phi Cm Cw H*(q:ℝ)^3*
      Real.log (productDimensionConstant P phi Cm Cw H*((N0:ℝ)+2)*(q:ℝ)/(1/(3*((outer+1:ℕ):ℝ)))) ≤ ((dA-1:ℕ):ℝ))
    (hDimW : productDimensionConstant P phi Cm Cw H*(q:ℝ)^3*
      Real.log (productDimensionConstant P phi Cm Cw H*((N0:ℝ)+2)*(q:ℝ)/(1/(3*((outer+1:ℕ):ℝ)))) ≤ ((dW-(nt+2):ℕ):ℝ))
    (query : OriginalQuery Seed A B W outer) (out : OriginalOutput Seed A B W outer)
    (hqMeas : ∀ n, Measurable (fun x : Seed × Point A B W outer × (ℕ → Response A B W outer) => query n x.1 x.2.1 x.2.2))
    (hout : Measurable (fun x : Seed × Point A B W outer × (ℕ → Response A B W outer) => out x.1 x.2.1 x.2.2))
    (seeds : Measure Seed) [IsProbabilityMeasure seeds],
  let c := productConfig P phi Cm Cw H nt q L mu eps r rhop omega
  let CL := 7/2+4*(H.Ce:ℝ)*Cw*(16*H.K+(64*H.K+1)*H.Kc)
  let Crho := 8*H.K*(H.Ce:ℝ)+4*(H.Ce:ℝ)*(21*H.K+(64*H.K+1)*H.Kc)+H.Ks*(2*Cw)
  ∃ frames : Frames A W outer nt, frames ∈ validFrames ∧
    CanonicalWorld c C (frameParameters frames) hRef tailRef L mu (rho L mu eps r)
      (rawBudget H.Cdelta 8 c.beta c.mu H.KD eps) H.Ctheta Delta (2*Cw*(Cm+2)) eps
      (CL*(c.scale*c.barlam)*(q:ℝ)^2) (Crho*c.scale) ∧
    ((N:ℝ) < ((outer+1:ℕ):ℝ)*(q:ℝ)/128 →
      (2/3:ℝ≥0∞) ≤ seeds {seed | eps < ‖gradient (actualPhi c (fun _ => C)
        (fun _ => publicZeroNormalizer c C hRef tailRef) (fun _ => publicOneNormalizer c C hRef tailRef) (frameParameters frames))
        (primalBlocks (globalOutput c (fun _ => C) (fun _ => publicZeroNormalizer c C hRef tailRef)
          (fun _ => publicOneNormalizer c C hRef tailRef) query out N (seed,frames)))‖})

theorem same_hierarchy_actual_serial_product
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Cm Cw : ℝ)
    (H : HierarchyConstants.{u} P phi Cm Cw)
    (hCm : 1 ≤ Cm) (hCw : 4*(Cm+2) ≤ Cw) (hp : ContDiff ℝ 3 phi)
    (hcore : ∀ t, |t| < 1 → phi t = t) : ProductGuarantee.{u,v} P phi Cm Cw H := by
  intro A B W Seed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  intro outer nt q _ _ _ _ C hRef tailRef hhRef htRef L mu eps r rhop omega Delta
    hL hmu heps hr hrhop hrho hq hfit hqcap hw hn hDelta hCount homega hD
    dA dW bA hA bW hW N0 N hNN hDimA hDimW query out hqMeas hout seeds _
  intro c CL Crho
  have hd : 0 < (1/8:ℝ)*omega := by positivity
  have hdw : (1/8:ℝ)*omega ≤ omega := by linarith only [hw]
  have hCm0 : 0 ≤ Cm := by linarith only [hCm]
  have hq1 : 1 ≤ q := by omega
  have hWorlds : ∀ frames : Frames A W outer nt, frames ∈ validFrames →
      CanonicalWorld c C (frameParameters frames) hRef tailRef L mu (rho L mu eps r)
        (rawBudget H.Cdelta 8 c.beta c.mu H.KD eps) H.Ctheta Delta (2*Cw*(Cm+2)) eps
        (CL*(c.scale*c.barlam)*(q:ℝ)^2) (Crho*c.scale) := by
    intro frames hf
    have hf' : ∀ t, Orthonormal ℝ (frames t).1 ∧ Orthonormal ℝ (frames t).2 := by
      simpa only [validFrames,Set.mem_iInter,Set.mem_setOf_eq] using hf
    exact same_constants_canonical_global_world P phi Cm Cw H hCm0 hCw hcore
      outer nt q C (frameParameters frames) hRef hhRef tailRef htRef L mu eps r rhop ((1/8)*omega) omega Delta
      (fun t => (hf' t).1.norm_eq_one 0) (fun t => (hf' t).2)
      hL hmu heps hr hrhop hrho hq1 hfit hqcap hd hdw hn hDelta hCount homega hD
  by_cases hBudget : (N:ℝ) < ((outer+1:ℕ):ℝ)*(q:ℝ)/128
  · have hGeo := same_constants_all_packet_geometry P phi Cm Cw H hCm0 hCw hcore A B W
      nt q C L mu eps r rhop ((1/8)*omega) omega hL hmu heps hr hrhop hrho hq1 hfit hqcap hd hdw hn homega hD
    obtain ⟨hR,hb,hl,ha,hell,hCR,hclip,hRshell,hPacket⟩ := hGeo
    let CR := 4*(3+8*H.Ks*(2*Cw)+2*Cw*(Cm+2))+2*Cw*(Cm+2)+3
    have hCertified : OriginalWorldAlgorithms.{u,v} c (fun _ : Fin (outer+1) => C)
        (fun _ => publicZeroNormalizer c C hRef tailRef) (fun _ => publicOneNormalizer c C hRef tailRef)
        q (productDimensionConstant P phi Cm Cw H) bA hA bW hW :=
      literal_first_hit_model_from_actual_canonical_packet_geometry c (fun _ : Fin (outer+1) => C)
      (fun _ => publicZeroNormalizer c C hRef tailRef) (fun _ => publicOneNormalizer c C hRef tailRef)
      hp hR hb hl ha q (by omega) hfit hw hell (2*Cw*(Cm+2)) CR Cm hCR hCm rfl hclip hRshell hn
      (fun _ h tail hh ht => ⟨(hPacket h tail hh ht).2.2.1,(hPacket h tail hh ht).2.2.2⟩) bA hA bW hW
    have hCD : 1 ≤ productDimensionConstant P phi Cm Cw H := le_max_left _ _
    obtain ⟨frames,hvalid,hWorld,hfail⟩ := actual_fixed_valid_world_with_gradient_failure c C hRef tailRef
      L mu (rho L mu eps r) (rawBudget H.Cdelta 8 c.beta c.mu H.KD eps) H.Ctheta Delta (2*Cw*(Cm+2)) eps
      (CL*(c.scale*c.barlam)*(q:ℝ)^2) (Crho*c.scale) hd hdw hp q hq (productDimensionConstant P phi Cm Cw H) hCD
      bA hA bW hW hCertified hWorlds query out hqMeas hout N0 N hNN hDimA hDimW seeds hBudget
    exact ⟨frames,hvalid,hWorld,fun _ => hfail⟩
  · let frames : Frames A W outer nt := fun _ => ((fun _ => hRef),tailRef)
    have hvalid : frames ∈ validFrames := by
      simp only [validFrames,Set.mem_iInter,Set.mem_setOf_eq]
      intro t
      exact ⟨orthonormal_subsingleton_iff.mpr (fun _ => hhRef),htRef⟩
    exact ⟨frames,hvalid,hWorlds frames hvalid,fun h => (hBudget h).elim⟩

/-- Universal constants precede all ambient dimensions, budgets, algorithms and realized seeds. -/
theorem original_private_handle_product
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw : ℝ)
    (hCm : 1 ≤ Cm) (hCw : 4*(Cm+2) ≤ Cw)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left)
    (hr : ∀ t, Bp < t → phi t = right) (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ H : HierarchyConstants.{u} P phi Cm Cw, ProductGuarantee.{u,v} P phi Cm Cw H := by
  obtain ⟨H⟩ := exists_same_actual_hierarchy P phi Bp left right Cm Cw (by linarith only [hCm]) hCw hp hl hr hcore
  exact ⟨H,same_hierarchy_actual_serial_product P phi Cm Cw H hCm hCw hp hcore⟩

end
end FangqingCanonicalHierarchyProduct
end

section
-- Source component: CompositionParameterSelection.lean

open scoped ENNReal

namespace FangqingCompositionParameterSelection

open FangqingCanonicalHierarchyGlobalWorld FangqingCanonicalHierarchyProduct
  FangqingActualRelayScaling FangqingThirdGroupScaling FangqingHierarchyAlignment
  HandleAlignment OriginalPacketDistanceGapBounds FangqingUnboundedOriginalPacketLength

noncomputable section
set_option maxHeartbeats 5000000
universe u

def rateFactor (r kappa : ℝ) : ℝ := min (r^(2/7:ℝ)) (Real.sqrt kappa)
def compositionRateConstant (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Cm Cw : ℝ)
    (H : HierarchyConstants.{u} P phi Cm Cw) : ℝ := H.cT*H.cq/512

theorem external_regime_identity (L mu eps r : ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (heps : 0 < eps) :
    regime L (rho L mu eps r) eps (L/mu) = r := by
  have hk : 0 < L/mu := div_pos hL hmu
  have hs : 0 < Real.sqrt (L/mu) := Real.sqrt_pos.mpr hk
  unfold regime rho
  rw [HandleAlignment.rpow_three_halves (L/mu) hk]
  field_simp

structure SelectedParameters (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Cm Cw : ℝ)
    (H : HierarchyConstants.{u} P phi Cm Cw) (L mu eps r Delta : ℝ) where
  outer : ℕ
  nt : ℕ
  q : ℕ
  N0 : ℕ
  d : ℕ
  rhop : ℝ
  omega : ℝ
  qOriginal : q = packetLength H.cq r (L/mu)
  timeOriginal : outer+1 = Nat.floor (H.cT*Delta/energy L eps)
  budgetOriginal : N0 = Nat.floor (((outer+1:ℕ):ℝ)*(q:ℝ)/128)
  pathOriginal : Nat.ceil (Cm*(q:ℝ)) = nt+3
  qLarge : 128 ≤ q
  qFit : q ≤ nt+2
  qCap : (q:ℝ)^2 ≤ H.cq^2*(L/mu)
  widthPositive : 0 < omega
  packetCurvaturePositive : 0 < rhop
  packetCurvatureBound : rhop ≤ rho L mu eps r
  pathSize : ((nt+2:ℕ):ℝ) ≤ Cm*(q:ℝ)
  timeBudget : ((outer+1:ℕ):ℝ) ≤ H.cT*Delta/energy L eps
  widthOriginal : omega = Cw*((8*(2*mu))/(H.cg*rhop))*(q:ℝ)^2
  alignmentOriginal : distanceScale q omega = packetD (2*H.cL*L) (2*mu) H.KD eps
  dimensionEnough : nt+3 ≤ d
  dimensionReserve : productDimensionConstant P phi Cm Cw H*(q:ℝ)^3*
    Real.log (productDimensionConstant P phi Cm Cw H*((N0:ℝ)+2)*(q:ℝ)/(1/(3*((outer+1:ℕ):ℝ)))) ≤ ((d-(nt+3):ℕ):ℝ)
  rateBudget : compositionRateConstant P phi Cm Cw H*(Delta/energy L eps)*rateFactor r (L/mu) ≤
    ((outer+1:ℕ):ℝ)*(q:ℝ)/128

/-- Exact original floors and physical alignment, with a single same-H universal rate constant.
The Euclidean dimension reserve is chosen before an algorithm or its random seed. -/
theorem select_original_composition_parameters
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Cm Cw : ℝ)
    (H : HierarchyConstants.{u} P phi Cm Cw)
    (hCm : 4 ≤ Cm) (hCw : 0 < Cw)
    (L mu eps r Delta : ℝ) (hL : 0 < L) (hmu : 0 < mu) (heps : 0 < eps) (hr : 1 ≤ r)
    (hA : 2/H.cT ≤ Delta/energy L eps)
    (hLarge : 128 ≤ H.cq*rateFactor r (L/mu)) :
    Nonempty (SelectedParameters P phi Cm Cw H L mu eps r Delta) := by
  have hcT := H.hcT
  have hcq := H.hcq
  have hk : 0 < L/mu := div_pos hL hmu
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hrho : 0 < rho L mu eps r := by unfold rho; positivity
  have hReg := external_regime_identity L mu eps r hL hmu heps
  have hAligned := H.alignment L (rho L mu eps r) eps mu 128 hL hrho heps hmu (by norm_num)
    (by simpa only [hReg,rateFactor,Nat.cast_ofNat] using hLarge)
  dsimp only at hAligned
  rw [hReg] at hAligned
  let q := packetLength H.cq r (L/mu)
  let nu := curvature 16 L (L/mu)
  let D := distance (H.KD/(2*Real.sqrt H.cL)) L eps (L/mu)
  let rhop := packetBudget Cw H.cg nu D q
  let omega := edgeWidth Cw H.cg nu rhop q
  change 128 ≤ q ∧ H.cq*rateFactor r (L/mu)/2 ≤ (q:ℝ) ∧
    (q:ℝ) ≤ H.cq*rateFactor r (L/mu) ∧ 0 < H.cg*rhop ∧
    0 < nu/(H.cg*rhop) ∧ 0 < omega ∧ 0 < rhop ∧ rhop ≤ rho L mu eps r/8 ∧
    (H.cg*rhop)*(nu/(H.cg*rhop)) = 8*(2*mu) ∧
    omega = Cw*(nu/(H.cg*rhop))*(q:ℝ)^2 ∧
    distanceScale q omega = packetD (2*H.cL*L) (2*mu) H.KD eps at hAligned
  obtain ⟨hq,hqHalf,hqUpper,hscale,hbarlam,hw,hR,hRB,hmass,homega,hD⟩ := hAligned
  have hnu : nu = 8*(2*mu) := by dsimp [nu,curvature]; field_simp; ring
  rw [hnu] at homega
  have hqSqrt : (q:ℝ) ≤ H.cq*Real.sqrt (L/mu) :=
    hqUpper.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hcq.le)
  have hqCap : (q:ℝ)^2 ≤ H.cq^2*(L/mu) := by
    have hh := (sq_le_sq₀ (Nat.cast_nonneg q) (mul_nonneg hcq.le (Real.sqrt_nonneg (L/mu)))).mpr hqSqrt
    simpa only [mul_pow,Real.sq_sqrt hk.le] using hh
  let nt := OriginalPacketBulkIndexing.packetIndex Cm q
  have hpath := OriginalPacketBulkIndexing.original_ceil_path_conditions Cm hCm q (by omega)
  let T := Nat.floor (H.cT*Delta/energy L eps)
  have harg : 2 ≤ H.cT*Delta/energy L eps := by
    have hm := mul_le_mul_of_nonneg_left hA hcT.le
    have heq : H.cT*(2/H.cT) = 2 := by field_simp
    rw [heq] at hm
    simpa only [mul_div_assoc] using hm
  have hT2 : 2 ≤ T := Nat.le_floor harg
  have hTupper : (T:ℝ) ≤ H.cT*Delta/energy L eps := Nat.floor_le (by linarith only [harg])
  have hTnear : H.cT*Delta/energy L eps < (T:ℝ)+1 := Nat.lt_floor_add_one _
  have hTcast : (2:ℝ) ≤ T := by exact_mod_cast hT2
  have hThalf : H.cT*(Delta/energy L eps)/2 ≤ (T:ℝ) := by
    rw [← mul_div_assoc]
    nlinarith only [hTnear,hTcast]
  let outer := T-1
  have hT : outer+1=T := by dsimp [outer]; omega
  let N0 := Nat.floor (((outer+1:ℕ):ℝ)*(q:ℝ)/128)
  let bound := productDimensionConstant P phi Cm Cw H*(q:ℝ)^3*
    Real.log (productDimensionConstant P phi Cm Cw H*((N0:ℝ)+2)*(q:ℝ)/(1/(3*((outer+1:ℕ):ℝ))))
  obtain ⟨d,hd,hreserve⟩ := arbitrary_original_dimension_reserve_is_available (nt+3) bound
  have hRate : compositionRateConstant P phi Cm Cw H*(Delta/energy L eps)*rateFactor r (L/mu) ≤
      ((outer+1:ℕ):ℝ)*(q:ℝ)/128 := by
    have htime0 : 0 ≤ H.cT*(Delta/energy L eps)/2 := by
      have ha0 : 0 < Delta/energy L eps := (div_pos (by norm_num : (0:ℝ)<2) hcT).trans_le hA
      positivity
    have hq0 : 0 ≤ H.cq*rateFactor r (L/mu)/2 := by dsimp [rateFactor]; positivity
    have hm := mul_le_mul hThalf hqHalf hq0 (Nat.cast_nonneg T)
    rw [← hT] at hm
    dsimp [compositionRateConstant]
    nlinarith only [hm]
  exact ⟨⟨outer,nt,q,N0,d,rhop,omega,rfl,hT,rfl,hpath.2.1,hq,hpath.2.2.2,hqCap,hw,hR,
    by linarith only [hRB,hrho],hpath.2.2.1,by rw [hT]; exact hTupper,homega,hD,hd,hreserve,hRate⟩⟩

/-- The original small-budget hypothesis implies the target-budget bound as well. -/
theorem selected_parameters_support_every_subrate_budget
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Cm Cw : ℝ)
    (H : HierarchyConstants.{u} P phi Cm Cw) (L mu eps r Delta : ℝ)
    (s : SelectedParameters P phi Cm Cw H L mu eps r Delta) (N : ℕ)
    (hN : (N:ℝ) < compositionRateConstant P phi Cm Cw H*(Delta/energy L eps)*rateFactor r (L/mu)) :
    N ≤ s.N0 ∧ (N:ℝ) < ((s.outer+1:ℕ):ℝ)*(s.q:ℝ)/128 := by
  have hb := hN.trans_le s.rateBudget
  exact ⟨by rw [s.budgetOriginal]; exact Nat.le_floor hb.le,hb⟩

end
end FangqingCompositionParameterSelection
end

section
-- Source component: CompositionEuclideanHardFamily.lean

open MeasureTheory
open scoped ENNReal

namespace FangqingCompositionEuclideanHardFamily

open FangqingCompositionParameterSelection FangqingCanonicalHierarchyProduct
  FangqingCanonicalHierarchyGlobalWorld FangqingCanonicalRelayStationarity
  FangqingCanonicalProductGradientFailure FangqingActualProductFrameSupport
  FangqingOriginalWorldExecutionCoordinates FangqingActualRelayPublicNormalizers
  FangqingHierarchyLateGateWorldFactory FangqingActualRelayScaling FangqingThirdGroupScaling
  FangqingActualPaddedRelayReplies FangqingRelayStationarity

noncomputable section
set_option maxHeartbeats 6000000
universe v

abbrev EuclideanBlock (d : ℕ) := EuclideanSpace ℝ (Fin d)

def referenceHandle (d : ℕ) (hd : 1 ≤ d) : EuclideanBlock d :=
  EuclideanSpace.basisFun (Fin d) ℝ ⟨0,hd⟩

def referenceTail (nt d : ℕ) (hd : nt+2 ≤ d) : Fin (nt+2) → EuclideanBlock d :=
  fun j => EuclideanSpace.basisFun (Fin d) ℝ (Fin.castLE hd j)

theorem reference_handle_unit (d : ℕ) (hd : 1 ≤ d) : ‖referenceHandle d hd‖=1 :=
  (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.norm_eq_one _

theorem reference_tail_orthonormal (nt d : ℕ) (hd : nt+2 ≤ d) :
    Orthonormal ℝ (referenceTail nt d hd) :=
  (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.comp (Fin.castLE hd) (Fin.castLE_injective hd)

/-- An actual finite-dimensional Euclidean saddle instance, not an abstract bad event. -/
def SelectedWorldOutcome (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Cm Cw : ℝ)
    (H : HierarchyConstants.{0} P phi Cm Cw) (L mu eps r Delta : ℝ)
    (s : SelectedParameters P phi Cm Cw H L mu eps r Delta)
    {Seed : Type v} [MeasurableSpace Seed]
    (query : OriginalQuery Seed (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer)
    (out : OriginalOutput Seed (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer)
    (N : ℕ) (seeds : Measure Seed) : Prop :=
  let c := productConfig P phi Cm Cw H s.nt s.q L mu eps r s.rhop s.omega
  let C := LinearIsometryEquiv.refl ℝ (EuclideanBlock s.d)
  let hRef := referenceHandle s.d (by have h:=s.dimensionEnough; omega)
  let tailRef := referenceTail s.nt s.d (by have h:=s.dimensionEnough; omega)
  let CL := 7/2+4*(H.Ce:ℝ)*Cw*(16*H.K+(64*H.K+1)*H.Kc)
  let Crho := 8*H.K*(H.Ce:ℝ)+4*(H.Ce:ℝ)*(21*H.K+(64*H.K+1)*H.Kc)+H.Ks*(2*Cw)
  ∃ frames : Frames (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer s.nt,
    frames ∈ validFrames ∧
    CanonicalWorld c C (frameParameters frames) hRef tailRef L mu (rho L mu eps r)
      (rawBudget H.Cdelta 8 c.beta c.mu H.KD eps) H.Ctheta Delta (2*Cw*(Cm+2)) eps
      (CL*(c.scale*c.barlam)*(s.q:ℝ)^2) (Crho*c.scale) ∧
    (2/3:ℝ≥0∞) ≤ seeds {seed | eps < ‖gradient (actualPhi c (fun _ => C)
      (fun _ => publicZeroNormalizer c C hRef tailRef) (fun _ => publicOneNormalizer c C hRef tailRef) (frameParameters frames))
      (primalBlocks (globalOutput c (fun _ => C) (fun _ => publicZeroNormalizer c C hRef tailRef)
        (fun _ => publicOneNormalizer c C hRef tailRef) query out N (seed,frames)))‖}

theorem actual_selected_euclidean_instance_lower
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Cm Cw : ℝ)
    (H : HierarchyConstants.{0} P phi Cm Cw)
    (hCm : 1 ≤ Cm) (hCw : 4*(Cm+2) ≤ Cw) (hp : ContDiff ℝ 3 phi)
    (hcore : ∀ t, |t| < 1 → phi t = t)
    (L mu eps r Delta : ℝ) (hL : 0 < L) (hmu : 0 < mu) (heps : 0 < eps) (hr : 1 ≤ r) (hDelta : 0 ≤ Delta)
    (s : SelectedParameters P phi Cm Cw H L mu eps r Delta)
    {Seed : Type v} [MeasurableSpace Seed] (seeds : Measure Seed) [IsProbabilityMeasure seeds]
    (query : OriginalQuery Seed (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer)
    (out : OriginalOutput Seed (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer)
    (hqMeas : ∀ n, Measurable (fun x : Seed × Point (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer ×
      (ℕ → Response (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer) => query n x.1 x.2.1 x.2.2))
    (hout : Measurable (fun x : Seed × Point (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer ×
      (ℕ → Response (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer) => out x.1 x.2.1 x.2.2))
    (N : ℕ)
    (hN : (N:ℝ) < compositionRateConstant P phi Cm Cw H*(Delta/energy L eps)*rateFactor r (L/mu)) :
    SelectedWorldOutcome P phi Cm Cw H L mu eps r Delta s query out N seeds := by
  have hdA : 1 ≤ s.d := by have h:=s.dimensionEnough; omega
  have hdW : s.nt+2 ≤ s.d := by have h:=s.dimensionEnough; omega
  letI : Nonempty (Fin s.d) := ⟨⟨0,hdA⟩⟩
  have hBudget := selected_parameters_support_every_subrate_budget P phi Cm Cw H L mu eps r Delta s N hN
  have hDimA : productDimensionConstant P phi Cm Cw H*(s.q:ℝ)^3*
      Real.log (productDimensionConstant P phi Cm Cw H*((s.N0:ℝ)+2)*(s.q:ℝ)/(1/(3*((s.outer+1:ℕ):ℝ)))) ≤ ((s.d-1:ℕ):ℝ) :=
    s.dimensionReserve.trans (by exact_mod_cast (show s.d-(s.nt+3) ≤ s.d-1 by omega))
  have hDimW : productDimensionConstant P phi Cm Cw H*(s.q:ℝ)^3*
      Real.log (productDimensionConstant P phi Cm Cw H*((s.N0:ℝ)+2)*(s.q:ℝ)/(1/(3*((s.outer+1:ℕ):ℝ)))) ≤ ((s.d-(s.nt+2):ℕ):ℝ) :=
    s.dimensionReserve.trans (by exact_mod_cast (show s.d-(s.nt+3) ≤ s.d-(s.nt+2) by omega))
  have hProduct := same_hierarchy_actual_serial_product P phi Cm Cw H hCm hCw hp hcore
  obtain ⟨frames,hvalid,hWorld,hfailure⟩ := hProduct (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) Seed
    s.outer s.nt s.q (LinearIsometryEquiv.refl ℝ _) (referenceHandle s.d hdA) (referenceTail s.nt s.d hdW)
    (reference_handle_unit s.d hdA) (reference_tail_orthonormal s.nt s.d hdW)
    L mu eps r s.rhop s.omega Delta hL hmu heps hr s.packetCurvaturePositive s.packetCurvatureBound
    s.qLarge s.qFit s.qCap s.widthPositive s.pathSize hDelta s.timeBudget s.widthOriginal s.alignmentOriginal
    (EuclideanSpace.basisFun (Fin s.d) ℝ) hdA (EuclideanSpace.basisFun (Fin s.d) ℝ) hdW
    s.N0 N hBudget.1 hDimA hDimW query out hqMeas hout seeds
  exact ⟨frames,hvalid,hWorld,hfailure hBudget.2⟩

/-- Before choosing any algorithm or seed realization, one finite Euclidean dimension
and the literal original physical scale realize the large-m branch of the composition bound. -/
theorem select_actual_euclidean_composition_family
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Cm Cw : ℝ)
    (H : HierarchyConstants.{0} P phi Cm Cw)
    (hCm : 4 ≤ Cm) (hCw : 4*(Cm+2) ≤ Cw) (hp : ContDiff ℝ 3 phi)
    (hcore : ∀ t, |t| < 1 → phi t = t)
    (L mu eps r Delta : ℝ) (hL : 0 < L) (hmu : 0 < mu) (heps : 0 < eps) (hr : 1 ≤ r) (hDelta : 0 ≤ Delta)
    (hA : 2/H.cT ≤ Delta/energy L eps) (hLarge : 128 ≤ H.cq*rateFactor r (L/mu)) :
    ∃ s : SelectedParameters P phi Cm Cw H L mu eps r Delta,
    ∀ (Seed : Type v) [MeasurableSpace Seed] (seeds : Measure Seed) [IsProbabilityMeasure seeds]
      (query : OriginalQuery Seed (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer)
      (out : OriginalOutput Seed (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer)
      (hqMeas : ∀ n, Measurable (fun x : Seed × Point (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer ×
        (ℕ → Response (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer) => query n x.1 x.2.1 x.2.2))
      (hout : Measurable (fun x : Seed × Point (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer ×
        (ℕ → Response (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer) => out x.1 x.2.1 x.2.2))
      (N : ℕ) (hN : (N:ℝ) < compositionRateConstant P phi Cm Cw H*(Delta/energy L eps)*rateFactor r (L/mu)),
      SelectedWorldOutcome P phi Cm Cw H L mu eps r Delta s query out N seeds := by
  have hCw0 : 0 < Cw := by linarith only [hCm,hCw]
  obtain ⟨s⟩ := select_original_composition_parameters P phi Cm Cw H hCm hCw0 L mu eps r Delta hL hmu heps hr hA hLarge
  exact ⟨s,fun Seed _ seeds _ query out hq ho N hN =>
    actual_selected_euclidean_instance_lower P phi Cm Cw H (by linarith only [hCm]) hCw hp hcore
      L mu eps r Delta hL hmu heps hr hDelta s seeds query out hq ho N hN⟩

end
end FangqingCompositionEuclideanHardFamily
end

section
-- Source component: ActualFixedRelaySuccessProbability.lean

open MeasureTheory
open scoped ENNReal

namespace FangqingActualFixedRelaySuccessProbability

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingCanonicalProductGradientFailure FangqingActualProductFrameSupport
  FangqingOriginalWorldExecutionCoordinates FangqingActualProductMeasurability
  FangqingCanonicalRelayStationarity FangqingActualPaddedRelayReplies FangqingRelayStationarity

noncomputable section
set_option maxHeartbeats 4000000
universe u v
variable {A B W : Type u} {Seed : Type v}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace A] [BorelSpace A] [MeasurableSpace W] [BorelSpace W]
  [Nontrivial A] [Nontrivial W] [SecondCountableTopology A] [SecondCountableTopology W]
  [MeasurableSpace (PhysicalSpace A B W)] [BorelSpace (PhysicalSpace A B W)]
  [SecondCountableTopology (PhysicalSpace A B W)]
  [MeasurableSpace Seed] {outer nt : ℕ}
  [MeasurableSpace (Point A B W outer)] [BorelSpace (Point A B W outer)]
  [MeasurableSpace (Point A B W outer →L[ℝ] Point A B W outer)] [BorelSpace (Point A B W outer →L[ℝ] Point A B W outer)]

theorem measurable_gradient_for_every_real_function
    (f : Blocks outer (PhysicalSpace A B W) → ℝ) : Measurable (gradient f) := by
  exact (InnerProductSpace.toDual ℝ (Blocks outer (PhysicalSpace A B W))).symm.continuous.measurable.comp
    (measurable_fderiv ℝ f)

theorem actual_fixed_frame_terminal_stationarity_event_measurable
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hp : ContDiff ℝ 3 c.phi)
    (frames : Frames A W outer nt) (f : Blocks outer (PhysicalSpace A B W) → ℝ)
    (query : OriginalQuery Seed A B W outer) (out : OriginalOutput Seed A B W outer)
    (hqMeas : ∀ n, Measurable (fun x : Seed × Point A B W outer × (ℕ → Response A B W outer) => query n x.1 x.2.1 x.2.2))
    (hout : Measurable (fun x : Seed × Point A B W outer × (ℕ → Response A B W outer) => out x.1 x.2.1 x.2.2))
    (N : ℕ) (eps : ℝ) :
    MeasurableSet {seed | ‖gradient f (primalBlocks (globalOutput c C m0 m1 query out N (seed,frames)))‖ ≤ eps} := by
  have hOut := (global_output_measurable c C m0 m1 hd hdw hp query out hqMeas hout N).comp
    (measurable_id.prodMk measurable_const : Measurable (fun seed : Seed => (seed,frames)))
  have hPrimal : Continuous (primalBlocks (A:=A) (B:=B) (W:=W) (outer:=outer)) := by
    unfold primalBlocks
    fun_prop
  exact measurableSet_le ((measurable_gradient_for_every_real_function f).norm.comp (hPrimal.measurable.comp hOut)) measurable_const

theorem actual_fixed_frame_failure_bound_implies_success_bound
    (c : Config nt) (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ)
    (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hp : ContDiff ℝ 3 c.phi)
    (frames : Frames A W outer nt) (f : Blocks outer (PhysicalSpace A B W) → ℝ)
    (query : OriginalQuery Seed A B W outer) (out : OriginalOutput Seed A B W outer)
    (hqMeas : ∀ n, Measurable (fun x : Seed × Point A B W outer × (ℕ → Response A B W outer) => query n x.1 x.2.1 x.2.2))
    (hout : Measurable (fun x : Seed × Point A B W outer × (ℕ → Response A B W outer) => out x.1 x.2.1 x.2.2))
    (N : ℕ) (eps : ℝ) (seeds : Measure Seed) [IsProbabilityMeasure seeds]
    (hFailure : (2/3:ℝ≥0∞) ≤ seeds {seed | eps < ‖gradient f (primalBlocks (globalOutput c C m0 m1 query out N (seed,frames)))‖}) :
    seeds {seed | ‖gradient f (primalBlocks (globalOutput c C m0 m1 query out N (seed,frames)))‖ ≤ eps} ≤ (1/3:ℝ≥0∞) := by
  let success := {seed | ‖gradient f (primalBlocks (globalOutput c C m0 m1 query out N (seed,frames)))‖ ≤ eps}
  have hs : MeasurableSet success := actual_fixed_frame_terminal_stationarity_event_measurable c C m0 m1 hd hdw hp frames f query out hqMeas hout N eps
  have hf : successᶜ = {seed | eps < ‖gradient f (primalBlocks (globalOutput c C m0 m1 query out N (seed,frames)))‖} := by
    ext seed
    simp only [success,Set.mem_compl_iff,Set.mem_setOf_eq,not_le]
  have hsum : seeds success + seeds successᶜ = 1 := by
    rw [measure_add_measure_compl hs,measure_univ]
  have hDirect : seeds success ≤ 1-(2/3:ℝ≥0∞) := by
    apply ENNReal.le_sub_of_add_le_right (by finiteness)
    have hm : seeds success+(2/3:ℝ≥0∞) ≤ seeds success+seeds {seed | eps < ‖gradient f (primalBlocks (globalOutput c C m0 m1 query out N (seed,frames)))‖} := add_le_add le_rfl hFailure
    rw [← hf,hsum] at hm
    exact hm
  have harith : (1:ℝ≥0∞)-(2/3:ℝ≥0∞) = 1/3 := by
    have htwo : ENNReal.ofReal (2/3:ℝ) = (2/3:ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<3)]
      norm_num
    calc
      _ = ENNReal.ofReal 1-ENNReal.ofReal (2/3:ℝ) := by rw [htwo]; norm_num
      _ = ENNReal.ofReal (1-(2/3:ℝ)) := (ENNReal.ofReal_sub 1 (by norm_num)).symm
      _ = _ := by norm_num [ENNReal.ofReal_div_of_pos]
  rw [harith] at hDirect
  exact hDirect

end
end FangqingActualFixedRelaySuccessProbability
end

section
-- Source component: CanonicalWorldFiniteInf.lean

namespace FangqingCanonicalWorldFiniteInf
open FangqingCanonicalHierarchyGlobalWorld FangqingCanonicalLateGateFamily
  FangqingCanonicalRelayParameterFamily FangqingCanonicalRelayStationarity
  FangqingActualRelayPublicNormalizers FangqingRelayStationarity FangqingRelayFenchelInterfaces
  FangqingRelayGap FangqingAmplifier OriginalPacketOrientationNormalization
noncomputable section
set_option maxHeartbeats 4500000
universe u
variable {A B W : Type u}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

theorem canonical_actual_value_has_finite_infimum
    {outer nt : ℕ} (c : Config nt) (C : A ≃ₗᵢ[ℝ] B)
    (p : Parameters A W outer nt) (hRef : A) (tailRef : Fin (nt+2) → W)
    (L muTarget rho M Ctheta Gap Cmin eps LF RF : ℝ)
    (w : CanonicalWorld c C p hRef tailRef L muTarget rho M Ctheta Gap Cmin eps LF RF)
    (hbeta : 0 ≤ c.beta) (hM : 0 ≤ M) (hreward : 0 ≤ c.reward) :
    let Phi := actualPhi c (fun _ => C)
      (fun _ => publicZeroNormalizer c C hRef tailRef) (fun _ => publicOneNormalizer c C hRef tailRef) p
    (∀ X, -((outer+1:ℕ):ℝ)*(M+c.reward) ≤ Phi X) ∧ BddBelow (Set.range Phi) := by
  intro Phi
  obtain ⟨hDelta,hRange,hSmall,hJ,hGrad,hHess,hSC,Y,S,hMax,hDiff,hSup,hGap⟩ := w.finalFamily
  have hLower : ∀ X, -((outer+1:ℕ):ℝ)*(M+c.reward) ≤ Phi X := by
    intro X
    have hlocal : ∀ t, 0 ≤ endpoint c.beta c.lam
        (hZero c (fun _ => C) p t) (publicZeroNormalizer c C hRef tailRef) (X t) (0:PhysicalSpace A B W) := by
      intro t
      change 0 ≤ c.beta/2*‖X t‖^2 + c.lam*inner ℝ (X t) (0:PhysicalSpace A B W) -
        (H0 c C (p t).1 (p t).2 0-c.mu/2*‖(0:PhysicalSpace A B W)‖^2) + publicZeroNormalizer c C hRef tailRef
      rw [(w.publicNormalizers t).1]
      simp only [inner_zero_right,mul_zero,norm_zero,zero_pow (by norm_num : 2≠0),sub_zero,sub_add_cancel]
      positivity
    have hlo := family_lower_at_zero_relay outer c.beta c.lam c.a c.sigma c.reward M
      (hZero c (fun _ => C) p) (hOne c (fun _ => C) p)
      (fun _ => publicZeroNormalizer c C hRef tailRef) (fun _ => publicOneNormalizer c C hRef tailRef)
      (gates c (fun _ => C) p) X.ofLp (fun _ => (0:PhysicalSpace A B W)) hM hreward hRange hDelta hlocal
    have hm := hMax X (fun _ => (0:PhysicalSpace A B W)) (fun t => c.a • X t)
    have he : exactValue outer c.beta c.lam c.a c.sigma c.reward
        (hZero c (fun _ => C) p) (hOne c (fun _ => C) p)
        (fun _ => publicZeroNormalizer c C hRef tailRef) (fun _ => publicOneNormalizer c C hRef tailRef)
        (gates c (fun _ => C) p) Y S X = Phi X := hSup X
    exact hlo.trans (hm.trans he.le)
  exact ⟨hLower,⟨-((outer+1:ℕ):ℝ)*(M+c.reward),by rintro _ ⟨X,rfl⟩; exact hLower X⟩⟩

end
end FangqingCanonicalWorldFiniteInf
end

section
-- Source component: CompositionEuclideanSuccessBound.lean

open MeasureTheory
open scoped ENNReal

namespace FangqingCompositionEuclideanSuccessBound

open FangqingCanonicalWorldFiniteInf FangqingCompositionEuclideanHardFamily FangqingActualFixedRelaySuccessProbability
  FangqingCompositionParameterSelection FangqingCanonicalHierarchyProduct
  FangqingCanonicalHierarchyGlobalWorld FangqingCanonicalRelayStationarity
  FangqingCanonicalProductGradientFailure FangqingActualProductFrameSupport
  FangqingOriginalWorldExecutionCoordinates FangqingActualRelayPublicNormalizers
  FangqingHierarchyLateGateWorldFactory FangqingActualRelayScaling FangqingThirdGroupScaling
  FangqingActualPaddedRelayReplies FangqingRelayStationarity

noncomputable section
set_option maxHeartbeats 6000000
universe v

abbrev EuclideanBlock (d : ℕ) := EuclideanSpace ℝ (Fin d)

def referenceHandle (d : ℕ) (hd : 1 ≤ d) : EuclideanBlock d :=
  EuclideanSpace.basisFun (Fin d) ℝ ⟨0,hd⟩

def referenceTail (nt d : ℕ) (hd : nt+2 ≤ d) : Fin (nt+2) → EuclideanBlock d :=
  fun j => EuclideanSpace.basisFun (Fin d) ℝ (Fin.castLE hd j)

theorem reference_handle_unit (d : ℕ) (hd : 1 ≤ d) : ‖referenceHandle d hd‖=1 :=
  (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.norm_eq_one _

theorem reference_tail_orthonormal (nt d : ℕ) (hd : nt+2 ≤ d) :
    Orthonormal ℝ (referenceTail nt d hd) :=
  (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.comp (Fin.castLE hd) (Fin.castLE_injective hd)

def VerifiedSelectedWorldOutcome (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Cm Cw : ℝ)
    (H : HierarchyConstants.{0} P phi Cm Cw) (L mu eps r Delta : ℝ)
    (s : SelectedParameters P phi Cm Cw H L mu eps r Delta)
    {Seed : Type v} [MeasurableSpace Seed]
    (query : OriginalQuery Seed (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer)
    (out : OriginalOutput Seed (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer)
    (N : ℕ) (seeds : Measure Seed) : Prop :=
  let c := productConfig P phi Cm Cw H s.nt s.q L mu eps r s.rhop s.omega
  let C := LinearIsometryEquiv.refl ℝ (EuclideanBlock s.d)
  let hRef := referenceHandle s.d (by have h:=s.dimensionEnough; omega)
  let tailRef := referenceTail s.nt s.d (by have h:=s.dimensionEnough; omega)
  let CL := 7/2+4*(H.Ce:ℝ)*Cw*(16*H.K+(64*H.K+1)*H.Kc)
  let Crho := 8*H.K*(H.Ce:ℝ)+4*(H.Ce:ℝ)*(21*H.K+(64*H.K+1)*H.Kc)+H.Ks*(2*Cw)
  ∃ frames : Frames (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer s.nt,
    frames ∈ validFrames ∧
    CanonicalWorld c C (frameParameters frames) hRef tailRef L mu (rho L mu eps r)
      (rawBudget H.Cdelta 8 c.beta c.mu H.KD eps) H.Ctheta Delta (2*Cw*(Cm+2)) eps
      (CL*(c.scale*c.barlam)*(s.q:ℝ)^2) (Crho*c.scale) ∧
    BddBelow (Set.range (actualPhi c (fun _ => C)
      (fun _ => publicZeroNormalizer c C hRef tailRef) (fun _ => publicOneNormalizer c C hRef tailRef) (frameParameters frames))) ∧
    seeds {seed | ‖gradient (actualPhi c (fun _ => C)
      (fun _ => publicZeroNormalizer c C hRef tailRef) (fun _ => publicOneNormalizer c C hRef tailRef) (frameParameters frames))
      (primalBlocks (globalOutput c (fun _ => C) (fun _ => publicZeroNormalizer c C hRef tailRef)
        (fun _ => publicOneNormalizer c C hRef tailRef) query out N (seed,frames)))‖ ≤ eps} ≤ (1/3:ℝ≥0∞)

theorem actual_selected_euclidean_success_lower
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Cm Cw : ℝ)
    (H : HierarchyConstants.{0} P phi Cm Cw)
    (hCm : 1 ≤ Cm) (hCw : 4*(Cm+2) ≤ Cw) (hp : ContDiff ℝ 3 phi)
    (hcore : ∀ t, |t| < 1 → phi t = t)
    (L mu eps r Delta : ℝ) (hL : 0 < L) (hmu : 0 < mu) (heps : 0 < eps) (hr : 1 ≤ r) (hDelta : 0 ≤ Delta)
    (s : SelectedParameters P phi Cm Cw H L mu eps r Delta)
    {Seed : Type v} [MeasurableSpace Seed] (seeds : Measure Seed) [IsProbabilityMeasure seeds]
    (query : OriginalQuery Seed (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer)
    (out : OriginalOutput Seed (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer)
    (hqMeas : ∀ n, Measurable (fun x : Seed × Point (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer ×
      (ℕ → Response (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer) => query n x.1 x.2.1 x.2.2))
    (hout : Measurable (fun x : Seed × Point (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer ×
      (ℕ → Response (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer) => out x.1 x.2.1 x.2.2))
    (N : ℕ)
    (hN : (N:ℝ) < compositionRateConstant P phi Cm Cw H*(Delta/energy L eps)*rateFactor r (L/mu)) :
    VerifiedSelectedWorldOutcome P phi Cm Cw H L mu eps r Delta s query out N seeds := by
  have hdA : 1 ≤ s.d := by have h:=s.dimensionEnough; omega
  letI : Nonempty (Fin s.d) := ⟨⟨0,hdA⟩⟩
  obtain ⟨frames,hvalid,hWorld,hFail⟩ := actual_selected_euclidean_instance_lower P phi Cm Cw H hCm hCw hp hcore
    L mu eps r Delta hL hmu heps hr hDelta s seeds query out hqMeas hout N hN
  let c := productConfig P phi Cm Cw H s.nt s.q L mu eps r s.rhop s.omega
  have hcL := H.hcL
  have hCD := H.hCD
  have hBeta : 0 ≤ c.beta := by change 0 ≤ 2*H.cL*L; positivity
  have hM : 0 ≤ rawBudget H.Cdelta 8 c.beta c.mu H.KD eps :=
    (abs_nonneg _).trans (hWorld.finalFamily.1 0 0)
  have hReward : 0 ≤ c.reward := by
    change 0 ≤ reward H.Cdelta 8 (2*H.cL*L) H.KD eps
    unfold reward rewardCoefficient energy
    positivity
  have hFinite := (canonical_actual_value_has_finite_infimum _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hWorld hBeta hM hReward).2
  refine ⟨frames,hvalid,hWorld,hFinite,?_⟩
  apply actual_fixed_frame_failure_bound_implies_success_bound _ _ _ _ _ _ hp frames _ query out hqMeas hout N eps seeds hFail
  · change 0 < (1/8:ℝ)*s.omega
    exact mul_pos (by norm_num) s.widthPositive
  · change (1/8:ℝ)*s.omega ≤ s.omega
    linarith only [s.widthPositive]

theorem select_actual_euclidean_composition_family_with_success_bound
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Cm Cw : ℝ)
    (H : HierarchyConstants.{0} P phi Cm Cw)
    (hCm : 4 ≤ Cm) (hCw : 4*(Cm+2) ≤ Cw) (hp : ContDiff ℝ 3 phi)
    (hcore : ∀ t, |t| < 1 → phi t = t)
    (L mu eps r Delta : ℝ) (hL : 0 < L) (hmu : 0 < mu) (heps : 0 < eps) (hr : 1 ≤ r) (hDelta : 0 ≤ Delta)
    (hA : 2/H.cT ≤ Delta/energy L eps) (hLarge : 128 ≤ H.cq*rateFactor r (L/mu)) :
    ∃ s : SelectedParameters P phi Cm Cw H L mu eps r Delta,
    ∀ (Seed : Type v) [MeasurableSpace Seed] (seeds : Measure Seed) [IsProbabilityMeasure seeds]
      (query : OriginalQuery Seed (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer)
      (out : OriginalOutput Seed (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer)
      (hqMeas : ∀ n, Measurable (fun x : Seed × Point (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer ×
        (ℕ → Response (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer) => query n x.1 x.2.1 x.2.2))
      (hout : Measurable (fun x : Seed × Point (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer ×
        (ℕ → Response (EuclideanBlock s.d) (EuclideanBlock s.d) (EuclideanBlock s.d) s.outer) => out x.1 x.2.1 x.2.2))
      (N : ℕ) (hN : (N:ℝ) < compositionRateConstant P phi Cm Cw H*(Delta/energy L eps)*rateFactor r (L/mu)),
      VerifiedSelectedWorldOutcome P phi Cm Cw H L mu eps r Delta s query out N seeds := by
  have hCw0 : 0 < Cw := by linarith only [hCm,hCw]
  obtain ⟨s⟩ := select_original_composition_parameters P phi Cm Cw H hCm hCw0 L mu eps r Delta hL hmu heps hr hA hLarge
  exact ⟨s,fun Seed _ seeds _ query out hq ho N hN =>
    actual_selected_euclidean_success_lower P phi Cm Cw H (by linarith only [hCm]) hCw hp hcore
      L mu eps r Delta hL hmu heps hr hDelta s seeds query out hq ho N hN⟩

end
end FangqingCompositionEuclideanSuccessBound
end

section
-- Source component: SingleLowerScalarProfiles.lean

open scoped ContDiff Topology

namespace FangqingSingleLowerScalarProfiles

noncomputable section

/-- Fixed, smooth, monotone gate for the all-derivative robust chain. -/
def psi (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1)

/-- A bounded positive primitive with a uniformly positive slope on [-1,1]. -/
def phi (t : ℝ) : ℝ := 2 * Real.arctan t + Real.pi

theorem psi_smooth : ContDiff ℝ ∞ psi := by unfold psi; fun_prop

theorem phi_smooth : ContDiff ℝ ∞ phi :=
  (contDiff_const.mul (Real.contDiff_arctan : ContDiff ℝ ∞ Real.arctan)).add contDiff_const

theorem psi_range (t : ℝ) : 0 ≤ psi t ∧ psi t ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem psi_monotone : Monotone psi := by
  intro x y h
  apply Real.smoothTransition.monotone
  linarith only [h]

theorem psi_zero (t : ℝ) (ht : t ≤ 1 / 2) : psi t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith only [ht]

theorem psi_one (t : ℝ) (ht : 1 ≤ t) : psi t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith only [ht]

theorem phi_range (t : ℝ) : 0 < phi t ∧ phi t < 2 * Real.pi := by
  have h0 := Real.neg_pi_div_two_lt_arctan t
  have h1 := Real.arctan_lt_pi_div_two t
  constructor <;> dsimp [phi] <;> linarith only [h0, h1]

theorem phi_hasDerivAt (t : ℝ) :
    HasDerivAt phi (2 / (1 + t ^ 2)) t := by
  convert! ((Real.hasDerivAt_arctan t).const_mul 2).add_const Real.pi using 1
  simp [div_eq_mul_inv]

theorem phi_deriv (t : ℝ) : deriv phi t = 2 / (1 + t ^ 2) :=
  (phi_hasDerivAt t).deriv

theorem scalar_derivatives_nonnegative (t : ℝ) :
    0 ≤ deriv psi t ∧ 0 ≤ deriv phi t := by
  refine ⟨psi_monotone.deriv_nonneg, ?_⟩
  rw [phi_deriv]
  positivity

theorem phi_slope_bounds (t : ℝ) :
    0 < deriv phi t ∧ deriv phi t ≤ 2 := by
  rw [phi_deriv]
  have hp : 0 < 1 + t ^ 2 := by positivity
  refine ⟨by positivity, ?_⟩
  apply (div_le_iff₀ hp).mpr
  nlinarith only [sq_nonneg t]

theorem phi_slope_ge_one (t : ℝ) (ht : |t| ≤ 1) :
    1 ≤ deriv phi t := by
  rw [phi_deriv]
  have hs : t ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg t) ht 2
  apply (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).mpr
  linarith only [hs]

/-- Inactive edges vanish on a whole neighborhood, so every derivative vanishes. -/
theorem psi_eventually_zero (t : ℝ) (ht : t < 1 / 2) :
    psi =ᶠ[𝓝 t] (fun _ => 0) := by
  filter_upwards [Iio_mem_nhds ht] with u hu
  exact psi_zero u hu.le

theorem psi_iterated_derivative_zero (t : ℝ) (ht : t < 1 / 2) (j : ℕ) :
    iteratedFDeriv ℝ j psi t = 0 := by
  have h := (psi_eventually_zero t ht).iteratedFDeriv ℝ j
  simpa using h.self_of_nhds

end
end FangqingSingleLowerScalarProfiles
end

section
-- Source component: SingleLowerChainEdge.lean

open scoped ContDiff Topology

namespace FangqingSingleLowerChainEdge

open FangqingSingleLowerScalarProfiles

noncomputable section

def edge (p : ℝ × ℝ) : ℝ := psi (-p.1) * phi (-p.2) - psi p.1 * phi p.2

def leftSlope (a b : ℝ) : ℝ :=
  -(deriv psi (-a) * phi (-b)) - deriv psi a * phi b

def rightSlope (a b : ℝ) : ℝ :=
  -(psi (-a) * deriv phi (-b)) - psi a * deriv phi b

theorem edge_smooth : ContDiff ℝ ∞ edge := by
  exact ((psi_smooth.comp contDiff_fst.neg).mul
    (phi_smooth.comp contDiff_snd.neg)).sub
      ((psi_smooth.comp contDiff_fst).mul (phi_smooth.comp contDiff_snd))

theorem edge_value_bound (p : ℝ × ℝ) : |edge p| ≤ 4 * Real.pi := by
  have ha := psi_range (-p.1)
  have hb := psi_range p.1
  have hc := phi_range (-p.2)
  have hd := phi_range p.2
  have h1 : 0 ≤ psi (-p.1) * phi (-p.2) := mul_nonneg ha.1 hc.1.le
  have h2 : 0 ≤ psi p.1 * phi p.2 := mul_nonneg hb.1 hd.1.le
  have h3 : psi (-p.1) * phi (-p.2) ≤ 2 * Real.pi := by
    exact (mul_le_mul_of_nonneg_right ha.2 hc.1.le).trans (by simpa using hc.2.le)
  have h4 : psi p.1 * phi p.2 ≤ 2 * Real.pi := by
    exact (mul_le_mul_of_nonneg_right hb.2 hd.1.le).trans (by simpa using hd.2.le)
  rw [edge, abs_le]
  constructor <;> linarith only [h1, h2, h3, h4, Real.pi_pos]

theorem slopes_nonpositive (a b : ℝ) : leftSlope a b ≤ 0 ∧ rightSlope a b ≤ 0 := by
  have h0 := scalar_derivatives_nonnegative (-a)
  have h1 := scalar_derivatives_nonnegative a
  have h2 := scalar_derivatives_nonnegative (-b)
  have h3 := scalar_derivatives_nonnegative b
  have h4 := phi_range (-b)
  have h5 := phi_range b
  have h6 := psi_range (-a)
  have h7 := psi_range a
  constructor
  · exact sub_nonpos.mpr (le_trans (neg_nonpos.mpr (mul_nonneg h0.1 h4.1.le))
      (mul_nonneg h1.1 h5.1.le))
  · exact sub_nonpos.mpr (le_trans (neg_nonpos.mpr (mul_nonneg h6.1 h2.2))
      (mul_nonneg h7.1 h3.2))

theorem incoming_slope_le_neg_one (a b : ℝ) (ha : 1 ≤ |a|) (hb : |b| ≤ 1) :
    rightSlope a b ≤ -1 := by
  have h0 := (psi_range (-a)).1
  have h1 := (psi_range a).1
  have h2 := (scalar_derivatives_nonnegative (-b)).2
  have h3 := (scalar_derivatives_nonnegative b).2
  have h4 := phi_slope_ge_one b hb
  have h5 := phi_slope_ge_one (-b) (by simpa only [abs_neg] using hb)
  rcases le_total 0 a with hpos | hneg
  · have haa : 1 ≤ a := by simpa only [abs_of_nonneg hpos] using ha
    rw [rightSlope, psi_one a haa, one_mul]
    have hh := mul_nonneg h0 h2
    linarith only [hh, h4]
  · have haa : 1 ≤ -a := by simpa only [abs_of_nonpos hneg] using ha
    rw [rightSlope, psi_one (-a) haa, one_mul]
    have hh := mul_nonneg h1 h3
    linarith only [hh, h5]

theorem hasDerivAt_edge_line (a b u v : ℝ) :
    HasDerivAt (fun t : ℝ => edge (a + t * u, b + t * v))
      (leftSlope a b * u + rightSlope a b * v) 0 := by
  have ha : HasDerivAt (fun t : ℝ => a + t * u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const u).const_add a
  have hb : HasDerivAt (fun t : ℝ => b + t * v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v).const_add b
  have hp (x : ℝ) : HasDerivAt psi (deriv psi x) x :=
    (psi_smooth.differentiable (by decide) x).hasDerivAt
  have hf (x : ℝ) : HasDerivAt phi (deriv phi x) x :=
    (phi_smooth.differentiable (by decide) x).hasDerivAt
  have hpa : HasDerivAt (fun t : ℝ => psi (a + t * u)) (deriv psi a * u) 0 := by
    convert! (hp (a + 0 * u)).comp 0 ha using 1
    simp only [zero_mul, add_zero]
  have hpna : HasDerivAt (fun t : ℝ => psi (-(a + t * u)))
      (deriv psi (-a) * (-u)) 0 := by
    convert! (hp (-(a + 0 * u))).comp 0 ha.neg using 1
    simp only [zero_mul, add_zero]
  have hfb : HasDerivAt (fun t : ℝ => phi (b + t * v)) (deriv phi b * v) 0 := by
    convert! (hf (b + 0 * v)).comp 0 hb using 1
    simp only [zero_mul, add_zero]
  have hfnb : HasDerivAt (fun t : ℝ => phi (-(b + t * v)))
      (deriv phi (-b) * (-v)) 0 := by
    convert! (hf (-(b + 0 * v))).comp 0 hb.neg using 1
    simp only [zero_mul, add_zero]
  have hh := (hpna.mul hfnb).sub (hpa.mul hfb)
  convert! hh using 1
  simp only [leftSlope, rightSlope, zero_mul, add_zero]
  ring

/-- A whole invisible edge is locally zero, including every order of derivative. -/
theorem edge_eventually_zero (p : ℝ × ℝ) (hp : |p.1| < 1 / 2) :
    edge =ᶠ[𝓝 p] (fun _ => 0) := by
  have ha : -p.1 < 1 / 2 := by linarith only [(abs_lt.mp hp).1]
  have hb : p.1 < 1 / 2 := (abs_lt.mp hp).2
  have h0 := (psi_eventually_zero (-p.1) ha).comp_tendsto
    (continuous_fst.neg.tendsto p)
  have h1 := (psi_eventually_zero p.1 hb).comp_tendsto
    (continuous_fst.tendsto p)
  filter_upwards [h0, h1] with y hy0 hy1
  change psi (-y.1) = 0 at hy0
  simp only [edge, Function.comp_apply] at *
  rw [hy0, hy1]
  ring

theorem edge_all_derivatives_zero (p : ℝ × ℝ) (hp : |p.1| < 1 / 2) (j : ℕ) :
    iteratedFDeriv ℝ j edge p = 0 := by
  simpa using ((edge_eventually_zero p hp).iteratedFDeriv ℝ j).self_of_nhds

end
end FangqingSingleLowerChainEdge
end

section
-- Source component: SingleLowerRobustChain.lean

open scoped BigOperators ContDiff Topology

namespace FangqingSingleLowerRobustChain

open FangqingSingleLowerScalarProfiles FangqingSingleLowerChainEdge

noncomputable section

def chain (n : ℕ) (x : Fin (n + 1) → ℝ) : ℝ :=
  -phi (x 0) + ∑ i : Fin n, edge (x i.castSucc, x i.succ)

def basis {n : ℕ} (j i : Fin (n + 1)) : ℝ := if i = j then 1 else 0

def edgeDirection (n : ℕ) (x v : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  leftSlope (x i.castSucc) (x i.succ) * v i.castSucc +
    rightSlope (x i.castSucc) (x i.succ) * v i.succ

def direction (n : ℕ) (x v : Fin (n + 1) → ℝ) : ℝ :=
  -(deriv phi (x 0) * v 0) + ∑ i : Fin n, edgeDirection n x v i

theorem chain_abs_bound (n : ℕ) (x : Fin (n + 1) → ℝ) :
    |chain n x| ≤ 4 * Real.pi * (n + 1) := by
  have hp := (phi_range (x 0)).2.le
  have hn := (phi_range (x 0)).1.le
  have hs : (∑ i : Fin n, |edge (x i.castSucc, x i.succ)|) ≤
      (n : ℝ) * (4 * Real.pi) := by
    calc
      _ ≤ ∑ _i : Fin n, (4 * Real.pi) :=
        Finset.sum_le_sum (fun i _ => edge_value_bound _)
      _ = _ := by simp
  have h := abs_add_le (-phi (x 0)) (∑ i : Fin n, edge (x i.castSucc, x i.succ))
  have ht := Finset.abs_sum_le_sum_abs
    (fun i : Fin n => edge (x i.castSucc, x i.succ)) Finset.univ
  rw [abs_neg, abs_of_nonneg hn] at h
  unfold chain
  nlinarith only [h, ht, hs, hp, Real.pi_pos]

theorem chain_zero (n : ℕ) : chain n 0 = -Real.pi := by
  simp [chain, edge, psi_zero 0 (by norm_num), phi, Real.arctan_zero]

theorem chain_smooth (n : ℕ) : ContDiff ℝ ∞ (chain n) := by
  have hs (i : Fin n) : ContDiff ℝ ∞
      (fun x : Fin (n + 1) → ℝ => edge (x i.castSucc, x i.succ)) :=
    edge_smooth.comp ((contDiff_apply ℝ ℝ i.castSucc).prodMk (contDiff_apply ℝ ℝ i.succ))
  exact (phi_smooth.comp (contDiff_apply ℝ ℝ 0)).neg.add
    (ContDiff.sum (fun i _ => hs i))

theorem chain_line_hasDerivAt (n : ℕ) (x v : Fin (n + 1) → ℝ) :
    HasDerivAt (fun t : ℝ => chain n (fun i => x i + t * v i)) (direction n x v) 0 := by
  have he (i : Fin n) := hasDerivAt_edge_line (x i.castSucc) (x i.succ)
    (v i.castSucc) (v i.succ)
  have hlin : HasDerivAt (fun t : ℝ => x 0 + t * v 0) (v 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 0)).const_add (x 0)
  have hp : HasDerivAt (fun t : ℝ => phi (x 0 + t * v 0))
      (deriv phi (x 0) * v 0) 0 := by
    have hd := (phi_smooth.differentiable (by decide) (x 0 + 0 * v 0)).hasDerivAt
    convert! hd.comp 0 hlin using 1
    simp only [zero_mul, add_zero]
  convert! hp.neg.add (HasDerivAt.sum (u := Finset.univ) (fun i _ => he i)) using 1
  funext t
  simp only [chain, Pi.add_apply, Pi.neg_apply, Finset.sum_apply]

theorem basis_nonnegative {n : ℕ} (j i : Fin (n + 1)) : 0 ≤ basis j i := by
  unfold basis
  split_ifs <;> norm_num

theorem edge_direction_nonpositive (n : ℕ) (x : Fin (n + 1) → ℝ)
    (j : Fin (n + 1)) (i : Fin n) : edgeDirection n x (basis j) i ≤ 0 := by
  exact add_nonpos
    (mul_nonpos_of_nonpos_of_nonneg (slopes_nonpositive _ _).1 (basis_nonnegative _ _))
    (mul_nonpos_of_nonpos_of_nonneg (slopes_nonpositive _ _).2 (basis_nonnegative _ _))

theorem direction_at_first_small_coordinate (n : ℕ) (x : Fin (n + 1) → ℝ)
    (j : Fin (n + 1)) (hj : |x j| ≤ 1)
    (hprev : ∀ i : Fin (n + 1), i < j → 1 ≤ |x i|) :
    direction n x (basis j) ≤ -1 := by
  classical
  have hsum : (∑ i : Fin n, edgeDirection n x (basis j) i) ≤ 0 :=
    Finset.sum_nonpos (fun i _ => edge_direction_nonpositive n x j i)
  by_cases hj0 : j = 0
  · subst j
    have hp := phi_slope_ge_one (x 0) hj
    simp only [direction, basis, ite_true, mul_one]
    linarith only [hp, hsum]
  · have hjpos : 0 < j.val := by
      by_contra hn
      have hh : j.val = 0 := by omega
      exact hj0 (Fin.ext hh)
    let i : Fin n := ⟨j.val - 1, by omega⟩
    have his : i.succ = j := by apply Fin.ext; dsimp [i]; omega
    have hic : i.castSucc < j := by dsimp [i]; change j.val - 1 < j.val; omega
    have hicne : i.castSucc ≠ j := ne_of_lt hic
    have hi : edgeDirection n x (basis j) i ≤ -1 := by
      have hs := incoming_slope_le_neg_one (x i.castSucc) (x j) (hprev _ hic) hj
      simpa only [edgeDirection, basis, if_neg hicne, his, ite_true,
        mul_zero, mul_one, zero_add] using hs
    have hs : (∑ k : Fin n, edgeDirection n x (basis j) k) ≤ edgeDirection n x (basis j) i := by
      have he := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
        (fun k => edgeDirection n x (basis j) k) (Finset.mem_univ i)
      have hn : (∑ k ∈ (Finset.univ : Finset (Fin n)).erase i,
          edgeDirection n x (basis j) k) ≤ 0 :=
        Finset.sum_nonpos (fun k _ => edge_direction_nonpositive n x j k)
      linarith only [he, hn]
    have hseed : -(deriv phi (x 0) * basis j 0) ≤ 0 :=
      neg_nonpos.mpr (mul_nonneg (scalar_derivatives_nonnegative _).2 (basis_nonnegative _ _))
    unfold direction
    linarith only [hi, hs, hseed]

theorem exists_first_small_coordinate (n : ℕ) (x : Fin (n + 1) → ℝ)
    (hsmall : ∃ j, |x j| < 1) :
    ∃ j : Fin (n + 1), |x j| < 1 ∧ ∀ i : Fin (n + 1), i < j → 1 ≤ |x i| := by
  classical
  let s : Finset (Fin (n + 1)) := Finset.univ.filter (fun j => |x j| < 1)
  have hs : s.Nonempty := by
    obtain ⟨j, hj⟩ := hsmall
    exact ⟨j, by simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]; exact hj⟩
  obtain ⟨j, hjs, hjmin⟩ := Finset.exists_min_image s (fun j => j) hs
  have hj : |x j| < 1 := (Finset.mem_filter.mp hjs).2
  refine ⟨j, hj, ?_⟩
  intro i hij
  by_contra hi
  have his : i ∈ s := by simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]; exact lt_of_not_ge hi
  exact (not_le_of_gt hij) (hjmin i his)

theorem some_unit_coordinate_has_strict_negative_derivative (n : ℕ)
    (x : Fin (n + 1) → ℝ) (hsmall : ∃ j, |x j| < 1) :
    ∃ j : Fin (n + 1),
      HasDerivAt (fun t : ℝ => chain n (fun i => x i + t * basis j i))
        (direction n x (basis j)) 0 ∧ direction n x (basis j) ≤ -1 := by
  obtain ⟨j, hj, hprev⟩ := exists_first_small_coordinate n x hsmall
  exact ⟨j, chain_line_hasDerivAt n x (basis j),
    direction_at_first_small_coordinate n x j hj.le hprev⟩

end
end FangqingSingleLowerRobustChain
end

section
-- Source component: SingleLowerAllDerivativeLocality.lean

open scoped BigOperators ContDiff Topology

namespace FangqingSingleLowerAllDerivativeLocality

open FangqingSingleLowerScalarProfiles FangqingSingleLowerChainEdge
  FangqingSingleLowerRobustChain

noncomputable section

variable {X : Type*} [TopologicalSpace X]

def prefixChain (n k : ℕ) (U : Fin (n + 1) → X → ℝ) (x : X) : ℝ :=
  -phi (U 0 x) + ∑ i : Fin n,
    if i.val < k then edge (U i.castSucc x, U i.succ x) else 0

theorem actual_chain_germ_is_prefix (n k : ℕ) (U : Fin (n + 1) → X → ℝ)
    (hU : ∀ i, Continuous (U i)) (x : X)
    (hsmall : ∀ i : Fin (n + 1), k ≤ i.val → |U i x| < 1 / 2) :
    (fun y => chain n (fun i => U i y)) =ᶠ[𝓝 x] prefixChain n k U := by
  have he (i : Fin n) :
      (fun y => edge (U i.castSucc y, U i.succ y)) =ᶠ[𝓝 x]
        (fun y => if i.val < k then edge (U i.castSucc y, U i.succ y) else 0) := by
    by_cases hi : i.val < k
    · simp only [hi, if_true]
      exact Filter.EventuallyEq.rfl
    · have h0 := edge_eventually_zero (U i.castSucc x, U i.succ x)
        (hsmall i.castSucc (by simpa using Nat.le_of_not_gt hi))
      have hh := h0.comp_tendsto (((hU i.castSucc).prodMk (hU i.succ)).tendsto x)
      filter_upwards [hh] with y hy
      simpa only [Function.comp_apply, hi, if_false] using hy
  have hall : ∀ᶠ y in 𝓝 x, ∀ i : Fin n,
      edge (U i.castSucc y, U i.succ y) =
        if i.val < k then edge (U i.castSucc y, U i.succ y) else 0 := by
    rw [Filter.eventually_all]
    exact he
  filter_upwards [hall] with y hy
  unfold chain prefixChain
  congr 1
  exact Finset.sum_congr rfl (fun i _ => hy i)

omit [TopologicalSpace X] in
theorem prefixChain_eq_of_same_first_columns (n k : ℕ)
    (U V : Fin (n + 1) → X → ℝ)
    (hprefix : ∀ i, i.val ≤ k → U i = V i) :
    prefixChain n k U = prefixChain n k V := by
  funext x
  unfold prefixChain
  rw [hprefix 0 (by simp)]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hik : i.val < k
  · rw [if_pos hik, if_pos hik, hprefix i.castSucc (by change i.val ≤ k; omega),
      hprefix i.succ (by change i.val + 1 ≤ k; omega)]
  · rw [if_neg hik, if_neg hik]

/-- Revealing the one boundary column suffices for the complete infinite jet. -/
theorem actual_chain_germs_agree_after_one_boundary (n k : ℕ)
    (U V : Fin (n + 1) → X → ℝ)
    (hU : ∀ i, Continuous (U i)) (hV : ∀ i, Continuous (V i))
    (hprefix : ∀ i, i.val ≤ k → U i = V i) (x : X)
    (hu : ∀ i : Fin (n + 1), k ≤ i.val → |U i x| < 1 / 2)
    (hv : ∀ i : Fin (n + 1), k ≤ i.val → |V i x| < 1 / 2) :
    (fun y => chain n (fun i => U i y)) =ᶠ[𝓝 x]
      (fun y => chain n (fun i => V i y)) := by
  have h0 := actual_chain_germ_is_prefix n k U hU x hu
  have h1 := actual_chain_germ_is_prefix n k V hV x hv
  rw [prefixChain_eq_of_same_first_columns n k U V hprefix] at h0
  exact h0.trans h1.symm

section Derivatives

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem actual_all_order_responses_agree_after_one_boundary (n k : ℕ)
    (U V : Fin (n + 1) → E → ℝ)
    (hU : ∀ i, Continuous (U i)) (hV : ∀ i, Continuous (V i))
    (hprefix : ∀ i, i.val ≤ k → U i = V i) (x : E)
    (hu : ∀ i : Fin (n + 1), k ≤ i.val → |U i x| < 1 / 2)
    (hv : ∀ i : Fin (n + 1), k ≤ i.val → |V i x| < 1 / 2) (j : ℕ) :
    iteratedFDeriv ℝ j (fun y => chain n (fun i => U i y)) x =
      iteratedFDeriv ℝ j (fun y => chain n (fun i => V i y)) x :=
  ((actual_chain_germs_agree_after_one_boundary n k U V hU hV hprefix x hu hv).iteratedFDeriv
    ℝ j).self_of_nhds

end Derivatives
end
end FangqingSingleLowerAllDerivativeLocality
end

section
-- Source component: SingleLowerPhysicalGradient.lean

open scoped BigOperators ContDiff Topology

namespace FangqingSingleLowerPhysicalGradient

open FangqingSingleLowerRobustChain

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def physicalChain (n : ℕ) (V : Fin (n + 1) → E) (x : E) : ℝ :=
  chain n (fun i => inner ℝ (V i) x)

theorem physicalChain_smooth (n : ℕ) (V : Fin (n + 1) → E) :
    ContDiff ℝ ∞ (physicalChain n V) := by
  exact (chain_smooth n).comp (contDiff_pi.mpr (fun i => (innerSL ℝ (V i)).contDiff))

theorem actual_unit_line_derivative (n : ℕ) (V : Fin (n + 1) → E)
    (hV : Orthonormal ℝ V) (x : E) (j : Fin (n + 1)) :
    HasDerivAt (fun t : ℝ => physicalChain n V (x + t • V j))
      (direction n (fun i => inner ℝ (V i) x) (basis j)) 0 := by
  have h := chain_line_hasDerivAt n (fun i => inner ℝ (V i) x) (basis j)
  convert! h using 1
  funext t
  unfold physicalChain
  congr 1
  funext i
  rw [inner_add_right, inner_smul_right]
  congr 2
  unfold basis
  by_cases hij : i = j
  · subst i
    simp [hV.norm_eq_one]
  · simp [hij, hV.inner_eq_zero hij]

theorem actual_fderiv_direction (n : ℕ) (V : Fin (n + 1) → E)
    (hV : Orthonormal ℝ V) (x : E) (j : Fin (n + 1)) :
    fderiv ℝ (physicalChain n V) x (V j) =
      direction n (fun i => inner ℝ (V i) x) (basis j) := by
  have hline : HasDerivAt (fun t : ℝ => x + t • V j) (V j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (V j)).const_add x
  have hd := ((physicalChain_smooth n V).differentiable (by decide) (x + (0 : ℝ) • V j)).hasFDerivAt
  have hh : HasDerivAt (fun t : ℝ => physicalChain n V (x + t • V j))
      (fderiv ℝ (physicalChain n V) x (V j)) 0 := by
    convert! hd.comp_hasDerivAt 0 hline using 1
    simp
  exact hh.unique (actual_unit_line_derivative n V hV x j)

theorem actual_physical_chain_gradient_lower (n : ℕ) (V : Fin (n + 1) → E)
    (hV : Orthonormal ℝ V) (x : E)
    (hsmall : ∃ j, |inner ℝ (V j) x| < 1) :
    1 ≤ ‖fderiv ℝ (physicalChain n V) x‖ := by
  obtain ⟨j, hj, hprev⟩ := exists_first_small_coordinate n (fun i => inner ℝ (V i) x) hsmall
  have hg := direction_at_first_small_coordinate n (fun i => inner ℝ (V i) x) j hj.le hprev
  have hnorm := (fderiv ℝ (physicalChain n V) x).le_opNorm (V j)
  rw [hV.norm_eq_one j, mul_one, actual_fderiv_direction n V hV] at hnorm
  rw [Real.norm_eq_abs] at hnorm
  have hab := neg_le_abs (direction n (fun i => inner ℝ (V i) x) (basis j))
  linarith only [hg, hnorm, hab]

def regularizedChain (n : ℕ) (V : Fin (n + 1) → E) (x : E) : ℝ :=
  physicalChain n V x + (1 / 20 : ℝ) * ‖x‖ ^ 2

def localizedChain (theta : ℝ → ℝ) (R : ℝ) (n : ℕ)
    (V : Fin (n + 1) → E) (x : E) : ℝ :=
  theta (‖x‖ ^ 2 / R ^ 2) * physicalChain n V x + (1 / 20 : ℝ) * ‖x‖ ^ 2

theorem regularizedChain_smooth (n : ℕ) (V : Fin (n + 1) → E) :
    ContDiff ℝ ∞ (regularizedChain n V) :=
  (physicalChain_smooth n V).add (contDiff_const.mul (contDiff_id.norm_sq ℝ))

theorem actual_regularized_unit_line_derivative (n : ℕ) (V : Fin (n + 1) → E)
    (hV : Orthonormal ℝ V) (x : E) (j : Fin (n + 1)) :
    HasDerivAt (fun t : ℝ => regularizedChain n V (x + t • V j))
      (direction n (fun i => inner ℝ (V i) x) (basis j) +
        (1 / 10 : ℝ) * inner ℝ (V j) x) 0 := by
  have hline : HasDerivAt (fun t : ℝ => x + t • V j) (V j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (V j)).const_add x
  have hquad : HasDerivAt (fun t : ℝ => (1 / 20 : ℝ) * ‖x + t • V j‖ ^ 2)
      ((1 / 10 : ℝ) * inner ℝ (V j) x) 0 := by
    have hq := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (1 / 20 : ℝ)).comp_hasDerivAt_of_eq
      0 hline (by simp)
    convert! hq using 1
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, real_inner_comm]
    ring
  exact (actual_unit_line_derivative n V hV x j).add hquad

theorem actual_regularized_physical_gradient_lower (n : ℕ) (V : Fin (n + 1) → E)
    (hV : Orthonormal ℝ V) (x : E)
    (hsmall : ∃ j, |inner ℝ (V j) x| < 1) :
    (9 / 10 : ℝ) ≤ ‖fderiv ℝ (regularizedChain n V) x‖ := by
  obtain ⟨j, hj, hprev⟩ := exists_first_small_coordinate n (fun i => inner ℝ (V i) x) hsmall
  have hg := direction_at_first_small_coordinate n (fun i => inner ℝ (V i) x) j hj.le hprev
  have hx : inner ℝ (V j) x ≤ 1 := (le_abs_self _).trans hj.le
  have hline : HasDerivAt (fun t : ℝ => x + t • V j) (V j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (V j)).const_add x
  have hd := ((regularizedChain_smooth n V).differentiable (by decide) x).hasFDerivAt
  have hh := hd.comp_hasDerivAt_of_eq 0 hline (by simp)
  have heq := hh.unique (actual_regularized_unit_line_derivative n V hV x j)
  have hn := (fderiv ℝ (regularizedChain n V) x).le_opNorm (V j)
  rw [hV.norm_eq_one j, mul_one, heq, Real.norm_eq_abs] at hn
  have hab := neg_le_abs (direction n (fun i => inner ℝ (V i) x) (basis j) +
    (1 / 10 : ℝ) * inner ℝ (V j) x)
  linarith only [hg, hx, hn, hab]

end
end FangqingSingleLowerPhysicalGradient
end

section
-- Source component: SingleLowerLocalizedGap.lean

open scoped BigOperators ContDiff Topology

namespace FangqingSingleLowerLocalizedGap

open FangqingSingleLowerRobustChain FangqingSingleLowerPhysicalGradient

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem actual_localized_chain_smooth (theta : ℝ → ℝ) (htheta : ContDiff ℝ ∞ theta)
    (R : ℝ) (n : ℕ) (V : Fin (n + 1) → E) :
    ContDiff ℝ ∞ (localizedChain theta R n V) :=
  ((htheta.comp ((contDiff_id.norm_sq ℝ).div_const _)).mul
    (physicalChain_smooth n V)).add (contDiff_const.mul (contDiff_id.norm_sq ℝ))

theorem actual_localized_chain_global_lower_bound (theta : ℝ → ℝ)
    (htheta : ∀ t, 0 ≤ theta t ∧ theta t ≤ 1) (R : ℝ) (n : ℕ)
    (V : Fin (n + 1) → E) (x : E) :
    -(4 * Real.pi * (n + 1)) ≤ localizedChain theta R n V x := by
  have hb := chain_abs_bound n (fun i => inner ℝ (V i) x)
  have ht := htheta (‖x‖ ^ 2 / R ^ 2)
  have ha : |theta (‖x‖ ^ 2 / R ^ 2) * physicalChain n V x| ≤
      4 * Real.pi * (n + 1) := by
    rw [abs_mul, abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)).trans (by simpa [physicalChain] using hb)
  have h := (abs_le.mp ha).1
  unfold localizedChain
  have hq : 0 ≤ (1 / 20 : ℝ) * ‖x‖ ^ 2 := by positivity
  linarith only [h, hq]

theorem actual_localized_chain_initial_value (theta : ℝ → ℝ) (hzero : theta 0 = 1)
    (R : ℝ) (n : ℕ) (V : Fin (n + 1) → E) :
    localizedChain theta R n V 0 = -Real.pi := by
  simp [localizedChain, physicalChain, hzero]
  exact chain_zero n

theorem actual_localized_chain_initial_gap (theta : ℝ → ℝ)
    (htheta : ∀ t, 0 ≤ theta t ∧ theta t ≤ 1) (hzero : theta 0 = 1)
    (R : ℝ) (n : ℕ) (V : Fin (n + 1) → E) :
    localizedChain theta R n V 0 - sInf (Set.range (localizedChain theta R n V)) ≤
      4 * Real.pi * (n + 1) := by
  have hl : -(4 * Real.pi * (n + 1)) ≤ sInf (Set.range (localizedChain theta R n V)) := by
    apply le_csInf (Set.range_nonempty _)
    rintro y ⟨x, rfl⟩
    exact actual_localized_chain_global_lower_bound theta htheta R n V x
  rw [actual_localized_chain_initial_value theta hzero R n V]
  linarith only [hl, Real.pi_pos]

theorem actual_localized_inside_germ (theta : ℝ → ℝ)
    (htheta : ∀ t, t ≤ 9 / 4 → theta t = 1) (R : ℝ) (hR : 0 < R)
    (n : ℕ) (V : Fin (n + 1) → E) (x : E) (hx : ‖x‖ < (3 / 2 : ℝ) * R) :
    localizedChain theta R n V =ᶠ[𝓝 x] regularizedChain n V := by
  have hs : ‖x‖ ^ 2 / R ^ 2 < (9 / 4 : ℝ) := by
    apply (div_lt_iff₀ (pow_pos hR 2)).mpr
    have hh := pow_lt_pow_left₀ hx (norm_nonneg x) (show (2 : ℕ) ≠ 0 by omega)
    nlinarith only [hh]
  have hc : Continuous (fun y : E => ‖y‖ ^ 2 / R ^ 2) := by fun_prop
  have he := (hc.tendsto x).eventually (Iio_mem_nhds hs)
  filter_upwards [he] with y hy
  simp only [localizedChain, regularizedChain, htheta _ hy.le, one_mul]

theorem actual_localized_inside_gradient_lower (theta : ℝ → ℝ)
    (htheta : ∀ t, t ≤ 9 / 4 → theta t = 1) (R : ℝ) (hR : 0 < R)
    (n : ℕ) (V : Fin (n + 1) → E) (hV : Orthonormal ℝ V) (x : E)
    (hx : ‖x‖ < (3 / 2 : ℝ) * R) (hsmall : ∃ j, |inner ℝ (V j) x| < 1) :
    (9 / 10 : ℝ) ≤ ‖fderiv ℝ (localizedChain theta R n V) x‖ := by
  rw [(actual_localized_inside_germ theta htheta R hR n V x hx).fderiv_eq]
  exact actual_regularized_physical_gradient_lower n V hV x hsmall

end
end FangqingSingleLowerLocalizedGap
end

section
-- Source component: SingleLowerAllDerivativeOracle.lean

open scoped BigOperators ContDiff Topology

namespace FangqingSingleLowerAllDerivativeOracle

open FangqingSingleLowerRobustChain FangqingSingleLowerPhysicalGradient

noncomputable section

variable {Parameter E F : Type*}
  [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem every_partial_jet_is_jointly_smooth (f : Parameter → E → F)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (j : ℕ) :
    ContDiff ℝ ∞ (fun z : Parameter × E => iteratedFDeriv ℝ j (f z.1) z.2) := by
  induction j with
  | zero =>
      exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.contDiff.comp hf
  | succ j ih =>
      have hext : ContDiff ℝ ∞ (fun z : (Parameter × E) × E =>
          iteratedFDeriv ℝ j (f z.1.1) z.2) :=
        ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
      have hd : ContDiff ℝ ∞ (fun z : Parameter × E =>
          fderiv ℝ (iteratedFDeriv ℝ j (f z.1)) z.2) :=
        hext.fderiv contDiff_snd (by simp)
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).symm.toContinuousLinearEquiv.contDiff.comp hd

abbrev AllDerivativeResponse (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (j : ℕ) → E [×j]→L[ℝ] ℝ

def allDerivativeOracle (f : E → ℝ) (x : E) : AllDerivativeResponse E :=
  fun j => iteratedFDeriv ℝ j f x

theorem complete_infinite_oracle_family_continuous (f : Parameter → E → ℝ)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    Continuous (fun z : Parameter × E => allDerivativeOracle (f z.1) z.2) :=
  continuous_pi (fun j => (every_partial_jet_is_jointly_smooth f hf j).continuous)

section Physical

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem actual_localized_family_jointly_smooth (theta : ℝ → ℝ)
    (htheta : ContDiff ℝ ∞ theta) (R : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (fun z : (Fin (n + 1) → H) × H => localizedChain theta R n z.1 z.2) := by
  have hc : ContDiff ℝ ∞ (fun z : (Fin (n + 1) → H) × H =>
      (fun i : Fin (n + 1) => inner ℝ (z.1 i) z.2)) := by
    apply contDiff_pi.mpr
    intro i
    exact ((contDiff_apply ℝ H i).comp contDiff_fst).inner ℝ contDiff_snd
  exact ((htheta.comp ((contDiff_snd.norm_sq ℝ).div_const _)).mul
    ((chain_smooth n).comp hc)).add (contDiff_const.mul (contDiff_snd.norm_sq ℝ))

theorem actual_complete_infinite_oracle_jointly_continuous (theta : ℝ → ℝ)
    (htheta : ContDiff ℝ ∞ theta) (R : ℝ) (n : ℕ) :
    Continuous (fun z : (Fin (n + 1) → H) × H =>
      allDerivativeOracle (localizedChain theta R n z.1) z.2) :=
  complete_infinite_oracle_family_continuous (localizedChain theta R n)
    (actual_localized_family_jointly_smooth theta htheta R n)

end Physical
end
end FangqingSingleLowerAllDerivativeOracle
end

section
-- Source component: SingleLowerLocalizedOracleLocality.lean

open scoped BigOperators ContDiff Topology

namespace FangqingSingleLowerLocalizedOracleLocality

open FangqingSingleLowerRobustChain FangqingSingleLowerPhysicalGradient
  FangqingSingleLowerAllDerivativeLocality FangqingSingleLowerAllDerivativeOracle

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem actual_localized_entire_oracle_uses_one_boundary (theta : ℝ → ℝ) (R : ℝ)
    (n k : ℕ) (V W : Fin (n + 1) → E)
    (hprefix : ∀ i, i.val ≤ k → V i = W i) (x : E)
    (hv : ∀ i : Fin (n + 1), k ≤ i.val → |inner ℝ (V i) x| < 1 / 2)
    (hw : ∀ i : Fin (n + 1), k ≤ i.val → |inner ℝ (W i) x| < 1 / 2) :
    allDerivativeOracle (localizedChain theta R n V) x =
      allDerivativeOracle (localizedChain theta R n W) x := by
  have hg := actual_chain_germs_agree_after_one_boundary n k
    (fun i y => inner ℝ (V i) y) (fun i y => inner ℝ (W i) y)
    (fun i => (innerSL ℝ (V i)).continuous) (fun i => (innerSL ℝ (W i)).continuous)
    (fun i hi => by rw [hprefix i hi]) x hv hw
  have hl : localizedChain theta R n V =ᶠ[𝓝 x] localizedChain theta R n W := by
    filter_upwards [hg] with y hy
    unfold localizedChain physicalChain
    rw [hy]
  funext j
  exact (hl.iteratedFDeriv ℝ j).self_of_nhds

theorem actual_localized_outside_germ_is_public_quadratic (theta : ℝ → ℝ)
    (htheta : ∀ t, 49 / 16 ≤ t → theta t = 0) (R : ℝ) (hR : 0 < R)
    (n : ℕ) (V : Fin (n + 1) → E) (x : E) (hx : 2 * R ≤ ‖x‖) :
    localizedChain theta R n V =ᶠ[𝓝 x] (fun y => (1 / 20 : ℝ) * ‖y‖ ^ 2) := by
  have hs : (49 / 16 : ℝ) < ‖x‖ ^ 2 / R ^ 2 := by
    apply (lt_div_iff₀ (pow_pos hR 2)).mpr
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * R) hx 2
    nlinarith only [hh, sq_pos_of_pos hR]
  have hc : Continuous (fun y : E => ‖y‖ ^ 2 / R ^ 2) := by fun_prop
  filter_upwards [(hc.tendsto x).eventually (Ioi_mem_nhds hs)] with y hy
  simp only [localizedChain, htheta _ hy.le, zero_mul, zero_add]

theorem actual_localized_entire_oracle_is_public_outside (theta : ℝ → ℝ)
    (htheta : ∀ t, 49 / 16 ≤ t → theta t = 0) (R : ℝ) (hR : 0 < R)
    (n : ℕ) (V : Fin (n + 1) → E) (x : E) (hx : 2 * R ≤ ‖x‖) :
    allDerivativeOracle (localizedChain theta R n V) x =
      allDerivativeOracle (fun y : E => (1 / 20 : ℝ) * ‖y‖ ^ 2) x := by
  funext j
  exact ((actual_localized_outside_germ_is_public_quadratic theta htheta R hR n V x hx).iteratedFDeriv
    ℝ j).self_of_nhds

def clippedCandidate (R : ℝ) (x : E) : E := if ‖x‖ ≤ 2 * R then x else 0

omit [InnerProductSpace ℝ E] in
theorem clippedCandidate_norm_le (R : ℝ) (hR : 0 ≤ R) (x : E) :
    ‖clippedCandidate R x‖ ≤ 2 * R := by
  unfold clippedCandidate
  split_ifs with h
  · exact h
  · simpa using (show 0 ≤ 2 * R by positivity)

omit [InnerProductSpace ℝ E] in
theorem clippedCandidate_measurable [MeasurableSpace E] [BorelSpace E] (R : ℝ) :
    Measurable (clippedCandidate (E := E) R) :=
  Measurable.ite (measurableSet_le continuous_norm.measurable measurable_const)
    measurable_id measurable_const

end
end FangqingSingleLowerLocalizedOracleLocality
end
