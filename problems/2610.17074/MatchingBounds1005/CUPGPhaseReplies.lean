import MatchingBounds1005.CUPGReplies
import MatchingBounds1005.CUPGMeasurableChoice
import MatchingBounds1005.CUPGPhaseGeometry
import MatchingBounds1005.CUPGPhysicalEscape

/-! A finite phase expressed solely in terms of first-order replies. All maps
are measurable for arbitrary response histories, including inconsistent ones.
No objective is an argument to any of these executable maps. -/
noncomputable section
open MeasureTheory

namespace MatchingBounds1005.CUPG

abbrev PhaseData (d : ℕ) := Model.Space d × (ℕ → Model.Response d)

def rawState {d : ℕ} (q α : ℝ) (p : PhaseData d) (n : ℕ) : ReplyState d :=
  replyRun q α p.1 (p.2 0).1 (fun j => p.2 (3 * j + 2)) n
def rawY {d : ℕ} (q α : ℝ) (p : PhaseData d) (n : ℕ) : Model.Space d :=
  (rawState q α p n).1
def rawX {d : ℕ} (q α : ℝ) (p : PhaseData d) (n : ℕ) : Model.Space d :=
  replyQuery q (rawState q α p n)
def rawYReply {d : ℕ} (p : PhaseData d) (n : ℕ) : Model.Response d :=
  p.2 (if n = 0 then 0 else 3 * n)
def rawZReply {d : ℕ} (p : PhaseData d) (n : ℕ) : Model.Response d :=
  p.2 (if n = 0 then 1 else 3 * n + 1)
def rawProxY {d : ℕ} (q α : ℝ) (p : PhaseData d) (n : ℕ) : Model.Response d :=
  proximalReply α p.1 (rawY q α p n) (rawYReply p n)
def rawZ {d : ℕ} (q α : ℝ) (p : PhaseData d) (n : ℕ) : Model.Space d :=
  rawY q α p n - (q ^ 2 / α) • (rawProxY q α p n).2
def rawGap {d : ℕ} (q α : ℝ) (p : PhaseData d) (n : ℕ) : ℝ :=
  (p.2 0).1 - (proximalReply α p.1 (rawZ q α p n) (rawZReply p n)).1 +
    α / 2 * ‖rawZ q α p n - p.1‖ ^ 2
def RawPass {d : ℕ} (q α L : ℝ) (p : PhaseData d) (n : ℕ) : Prop :=
  (rawProxY q α p n).1 ≤ (p.2 0).1 ∧
    ‖(rawProxY q α p n).2‖ ^ 2 ≤ 2 * L * rawGap q α p n * Real.exp (-q * n)
def RawStopped {d : ℕ} (q α L ε : ℝ) (p : PhaseData d) (n : ℕ) : Prop :=
  ¬ RawPass q α L p n ∨ ‖(rawProxY q α p n).2‖ ≤ ε / 10
def rawStop {d : ℕ} (q α L ε : ℝ) (N : ℕ) (p : PhaseData d) : ℕ :=
  @firstIndex (RawStopped q α L ε p) (Classical.decPred _) N
def rawWitness {d : ℕ} (q α : ℝ) (p : PhaseData d) (n : ℕ) : Model.Space d :=
  if (rawProxY q α p n).1 ≤ (p.2 0).1 then rawZ q α p n else p.1

@[fun_prop] theorem continuous_rawState {d : ℕ} (q α : ℝ) (n : ℕ) :
    Continuous (fun p : PhaseData d => rawState q α p n) := by
  exact (continuous_replyRun q α n).comp
    (continuous_fst.prodMk (((continuous_apply 0).comp continuous_snd).fst.prodMk
      (continuous_pi (fun j => (continuous_apply (3 * j + 2)).comp continuous_snd))))
@[fun_prop] theorem continuous_rawY {d : ℕ} (q α : ℝ) (n : ℕ) :
    Continuous (fun p : PhaseData d => rawY q α p n) := (continuous_rawState q α n).fst
@[fun_prop] theorem continuous_rawX {d : ℕ} (q α : ℝ) (n : ℕ) :
    Continuous (fun p : PhaseData d => rawX q α p n) :=
  (continuous_replyQuery q).comp (continuous_rawState q α n)
@[fun_prop] theorem continuous_rawYReply {d : ℕ} (n : ℕ) :
    Continuous (fun p : PhaseData d => rawYReply p n) :=
  (continuous_apply _).comp continuous_snd
@[fun_prop] theorem continuous_rawZReply {d : ℕ} (n : ℕ) :
    Continuous (fun p : PhaseData d => rawZReply p n) :=
  (continuous_apply _).comp continuous_snd
@[fun_prop] theorem continuous_rawProxY {d : ℕ} (q α : ℝ) (n : ℕ) :
    Continuous (fun p : PhaseData d => rawProxY q α p n) := by
  unfold rawProxY proximalReply
  fun_prop
@[fun_prop] theorem continuous_rawZ {d : ℕ} (q α : ℝ) (n : ℕ) :
    Continuous (fun p : PhaseData d => rawZ q α p n) := by unfold rawZ; fun_prop
@[fun_prop] theorem continuous_rawGap {d : ℕ} (q α : ℝ) (n : ℕ) :
    Continuous (fun p : PhaseData d => rawGap q α p n) := by
  unfold rawGap proximalReply
  fun_prop

theorem measurableSet_rawPass {d : ℕ} (q α L : ℝ) (n : ℕ) :
    MeasurableSet {p : PhaseData d | RawPass q α L p n} := by
  apply MeasurableSet.inter
  · exact measurableSet_le (continuous_rawProxY q α n).fst.measurable
      (((continuous_apply 0).comp continuous_snd).fst.measurable)
  · exact measurableSet_le ((continuous_rawProxY q α n).snd.norm.pow 2).measurable
      ((continuous_const.mul (continuous_rawGap q α n)).mul continuous_const).measurable
theorem measurableSet_rawStopped {d : ℕ} (q α L ε : ℝ) (n : ℕ) :
    MeasurableSet {p : PhaseData d | RawStopped q α L ε p n} :=
  (measurableSet_rawPass q α L n).compl.union
    (measurableSet_le (continuous_rawProxY q α n).snd.norm.measurable measurable_const)
@[fun_prop] theorem measurable_rawStop {d : ℕ} (q α L ε : ℝ) (N : ℕ) :
    Measurable (rawStop (d := d) q α L ε N) :=
  measurable_firstIndex _ (measurableSet_rawStopped q α L ε) N
@[fun_prop] theorem measurable_rawWitness {d : ℕ} (q α : ℝ) (n : ℕ) :
    Measurable (fun p : PhaseData d => rawWitness q α p n) :=
  Measurable.ite
    (measurableSet_le (continuous_rawProxY q α n).fst.measurable
      (((continuous_apply 0).comp continuous_snd).fst.measurable))
    (continuous_rawZ q α n).measurable measurable_fst

theorem measurable_nat_evaluation {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (F : X → ℕ → Y) (hF : ∀ n, Measurable (fun x => F x n))
    (I : X → ℕ) (hI : Measurable I) : Measurable (fun x => F x (I x)) := by
  have hm : Measurable (fun p : X × ℕ => F p.1 p.2) := measurable_from_prod_countable hF
  exact hm.comp (measurable_id.prodMk hI)

/-- Before the final query, a phase makes 3N+2 AGD/monitor calls, 2N guard
calls, and 4N escape calls. The first two calls initialize y₀ and z₀. -/
def rawBodyQuery {d : ℕ} (q α τ L ε : ℝ) (N t : ℕ) (p : PhaseData d) : Model.Space d :=
  if t = 0 then p.1 else if t = 1 then rawZ q α p 0 else
  if t < 3 * N + 2 then
    let j := (t - 2) / 3
    if (t - 2) % 3 = 0 then rawX q α p j else
      if (t - 2) % 3 = 1 then rawY q α p (j + 1) else rawZ q α p (j + 1)
  else if t < 5 * N + 2 then
    let j := (t - (3 * N + 2)) / 2
    if (t - (3 * N + 2)) % 2 = 0 then guardNear (rawY q α p (j + 1)) (rawY q α p j)
      else guardFar (rawY q α p (j + 1)) (rawY q α p j)
  else
    let j := (t - (5 * N + 2)) / 4
    let u := if (t - (5 * N + 2)) % 4 < 2 then rawY q α p j else
      rawWitness q α p (rawStop q α L ε N p)
    if (t - (5 * N + 2)) % 2 = 0 then escapeMinus u (rawX q α p j) (16 * τ)
      else escapePlus u (rawX q α p j) (16 * τ)

@[fun_prop] theorem measurable_rawBodyQuery {d : ℕ} (q α τ L ε : ℝ) (N t : ℕ) :
    Measurable (rawBodyQuery (d := d) q α τ L ε N t) := by
  have hw : Measurable (fun p : PhaseData d => rawWitness q α p (rawStop q α L ε N p)) :=
    measurable_nat_evaluation _ (measurable_rawWitness q α) _ (measurable_rawStop q α L ε N)
  unfold rawBodyQuery
  split_ifs
  all_goals try simp only [guardNear, guardFar, escapeMinus, escapePlus]
  all_goals fun_prop

def rawCandidate {d : ℕ} (q α τ L ε : ℝ) (N : ℕ) (p : PhaseData d) : Model.Space d := by
  classical
  exact if RawPass q α L p (rawStop q α L ε N p) then rawY q α p (rawStop q α L ε N p)
  else (indexedBest (p.1, (p.2 0).1)
    (fun j => (rawBodyQuery q α τ L ε N j p, (p.2 j).1)) (9 * N + 2)).1

@[fun_prop] theorem measurable_rawCandidate {d : ℕ} (q α τ L ε : ℝ) (N : ℕ) :
    Measurable (rawCandidate (d := d) q α τ L ε N) := by
  unfold rawCandidate
  apply Measurable.ite
  · exact measurableSet_nat_choice _ (measurableSet_rawPass q α L) (measurable_rawStop q α L ε N)
  · exact measurable_nat_evaluation _ (fun n => (continuous_rawY q α n).measurable) _
      (measurable_rawStop q α L ε N)
  · exact ((measurable_indexedBest (9 * N + 2)).comp
      ((measurable_fst.prodMk (((measurable_pi_apply 0).comp measurable_snd).fst)).prodMk
        (measurable_pi_lambda _ (fun j => (measurable_rawBodyQuery q α τ L ε N j).prodMk
          (((measurable_pi_apply j).comp measurable_snd).fst))))).fst

def rawPhaseQuery {d : ℕ} (q α τ L ε : ℝ) (N t : ℕ) (p : PhaseData d) : Model.Space d :=
  if t < 9 * N + 2 then rawBodyQuery q α τ L ε N t p else rawCandidate q α τ L ε N p

@[fun_prop] theorem measurable_rawPhaseQuery {d : ℕ} (q α τ L ε : ℝ) (N t : ℕ) :
    Measurable (rawPhaseQuery (d := d) q α τ L ε N t) := by
  unfold rawPhaseQuery
  split_ifs
  · exact measurable_rawBodyQuery q α τ L ε N t
  · exact measurable_rawCandidate q α τ L ε N

end MatchingBounds1005.CUPG
