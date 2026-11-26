import MatchingBounds1005.CUPGProximal
import MatchingBounds1005.Model
import Mathlib.Tactic

/-! The accelerated recurrence as a continuous function of previously returned
first-order responses. The maps in this module do not inspect an objective. -/
noncomputable section
open scoped InnerProductSpace

namespace MatchingBounds1005.CUPG

abbrev ReplyState (d : ℕ) := Model.Space d × Model.Space d × ℝ

def stateOfReply {d : ℕ} (s : ReplyState d) : EstimateState (Model.Space d) :=
  ⟨s.1, s.2.1, s.2.2⟩

def replyOfState {d : ℕ} (s : EstimateState (Model.Space d)) : ReplyState d :=
  (s.point, s.center, s.minimum)

@[simp] theorem stateOfReply_replyOfState {d : ℕ} (s : EstimateState (Model.Space d)) :
    stateOfReply (replyOfState s) = s := by cases s; rfl

def proximalReply {d : ℕ} (α : ℝ) (start x : Model.Space d) (r : Model.Response d) :
    Model.Response d := (r.1 + α * ‖x - start‖ ^ 2, r.2 + (2 * α) • (x - start))

theorem proximalReply_correct {d : ℕ} {f : Model.Space d → ℝ}
    (hf : Differentiable ℝ f) (α : ℝ) (start x : Model.Space d) :
    proximalReply α start x (Model.oracle f x) = Model.oracle (regularized f α start) x := by
  simp only [proximalReply, Model.oracle, regularized_gradient hf, regularized]

def replyQuery {d : ℕ} (q : ℝ) (s : ReplyState d) : Model.Space d :=
  query q (stateOfReply s)

def replyStep {d : ℕ} (q α : ℝ) (start : Model.Space d) (s : ReplyState d)
    (r : Model.Response d) : ReplyState d :=
  let x := replyQuery q s
  let p := proximalReply α start x r
  (x - (q ^ 2 / α) • p.2,
    nextCenter q α s.2.1 x p.2, nextMinimum q α s.2.2 p.1 s.2.1 x p.2)

theorem replyStep_correct {d : ℕ} {f : Model.Space d → ℝ} (hf : Differentiable ℝ f)
    (q α : ℝ) (start : Model.Space d) (s : EstimateState (Model.Space d)) :
    stateOfReply (replyStep q α start (replyOfState s)
      (Model.oracle f (query q s))) = estimateStep (regularized f α start) q α s := by
  simp only [replyStep, replyQuery, stateOfReply_replyOfState, replyOfState,
    proximalReply, Model.oracle, stateOfReply, estimateStep, regularized_gradient hf,
    regularized]

def replyRun {d : ℕ} (q α : ℝ) (start : Model.Space d) (initialValue : ℝ)
    (r : ℕ → Model.Response d) : ℕ → ReplyState d
  | 0 => (start, start, initialValue)
  | n + 1 => replyStep q α start (replyRun q α start initialValue r n) (r n)

theorem replyRun_correct {d : ℕ} {f : Model.Space d → ℝ} (hf : Differentiable ℝ f)
    (q α : ℝ) (start : Model.Space d) (r : ℕ → Model.Response d) (n : ℕ)
    (hr : ∀ j < n, r j = Model.oracle f (query q
      (estimateRun (regularized f α start) q α start j))) :
    stateOfReply (replyRun q α start (f start) r n) =
      estimateRun (regularized f α start) q α start n := by
  induction n with
  | zero => simp [replyRun, stateOfReply, estimateRun, regularized]
  | succ n ih =>
    have hn := ih (fun j hj => hr j (by omega))
    have he : replyRun q α start (f start) r n =
        replyOfState (estimateRun (regularized f α start) q α start n) := by
      have hh := congrArg replyOfState hn
      exact hh
    rw [replyRun, he, hr n (by omega)]
    exact replyStep_correct hf q α start _

theorem continuous_replyQuery {d : ℕ} (q : ℝ) : Continuous (replyQuery (d := d) q) := by
  unfold replyQuery query stateOfReply
  fun_prop

theorem continuous_proximalReply {d : ℕ} (α : ℝ) :
    Continuous (fun p : Model.Space d × Model.Space d × Model.Response d =>
      proximalReply α p.1 p.2.1 p.2.2) := by
  unfold proximalReply
  fun_prop

theorem continuous_replyStep {d : ℕ} (q α : ℝ) :
    Continuous (fun p : Model.Space d × ReplyState d × Model.Response d =>
      replyStep q α p.1 p.2.1 p.2.2) := by
  unfold replyStep nextCenter nextMinimum proximalReply replyQuery query stateOfReply
  fun_prop

theorem continuous_replyRun {d : ℕ} (q α : ℝ) (n : ℕ) :
    Continuous (fun p : Model.Space d × ℝ × (ℕ → Model.Response d) =>
      replyRun q α p.1 p.2.1 p.2.2 n) := by
  induction n with
  | zero => exact continuous_fst.prodMk (continuous_fst.prodMk continuous_snd.fst)
  | succ n ih =>
    exact (continuous_replyStep q α).comp
      (continuous_fst.prodMk (ih.prodMk ((continuous_apply n).comp continuous_snd.snd)))

end MatchingBounds1005.CUPG
