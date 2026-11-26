import Bilevel.TransportRoundController
import Bilevel.TransportNetworkReconstruction

/-! Exact current-edge reconstruction of an executed frozen round. All
off-edge values are computed from the full context. Both orientations of the
current edge are accessed through the same fixed orthogonal map. -/
noncomputable section
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork OrthogonalAction
set_option maxHeartbeats 600000

def batchProgram {n D T : ℕ} (e : Edge n) (c : Context (d := D) e T) :
    {b : ℕ} → (Fin b → Probe n D) → EdgeProgram D (Fin b → Space D) b
  | 0,_ => .halt Fin.elim0
  | b+1,p =>
    let tail := batchProgram e c (fun i : Fin b => p i.succ)
    let q := p 0
    if h : q.2.1=e then
      if q.1 then .reverse q.2.2 (fun y => tail.map (Fin.cons y))
      else .forward q.2.2 (fun y => tail.map (Fin.cons y))
    else
      let O := c.2 ⟨q.2.1,h⟩
      let y := if q.1 then O⁻¹ • q.2.2 else O • q.2.2
      .skip (tail.map (Fin.cons y))

theorem batchProgram_correct {n D T b : ℕ} (hT : T ≤ D) (e : Edge n)
    (p : Fin b → Probe n D) (z : Latent n D) :
    EdgeProgram.eval (batchProgram e (context T hT e z) p) (z.2 e) = batchObservation p z := by
  induction b with
  | zero => funext i; exact Fin.elim0 i
  | succ b ih =>
    have ht := ih (fun i : Fin b => p i.succ)
    by_cases he : (p 0).2.1=e
    · cases hb : (p 0).1 with
      | false =>
        simp only [batchProgram,dif_pos he,hb,Bool.false_eq_true,ite_false,EdgeProgram.eval,EdgeProgram.eval_map,ht]
        funext i
        cases i using Fin.cases with
        | zero => simp only [Fin.cons_zero,batchObservation,probeObservation,hb,Bool.false_eq_true,ite_false,forwardObservation,he]
        | succ i => rfl
      | true =>
        simp only [batchProgram,dif_pos he,hb,ite_true,EdgeProgram.eval,EdgeProgram.eval_map,ht]
        funext i
        cases i using Fin.cases with
        | zero => simp only [Fin.cons_zero,batchObservation,probeObservation,hb,ite_true,reverseObservation,he]
        | succ i => rfl
    · simp only [batchProgram,dif_neg he,EdgeProgram.eval,EdgeProgram.eval_map,ht]
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i => rfl

def contextQueries {n D T p : ℕ} {e : Edge n} (c : Context (d := D) e T)
    (q : Queries n D p) : Answers n p T := fun v i j => inner (q v i) (c.1 v j)

def contextDisclosures {n D T c' : ℕ} {e : Edge n} (c : Context (d := D) e T)
    (names : Vertex n → Fin c' → Option (Fin T)) : Generators n D c' :=
  fun v i => match names v i with | none => 0 | some j => c.1 v j

def roundProgram {H : Type*} {n D m p c T : ℕ} (e : Edge n) (ctx : Context (d := D) e T)
    (choose : H × Generators n D m → Queries n D p)
    (respond : StepData H n D m p T → H) (names : Vertex n → Fin c → Option (Fin T))
    (s : H × Generators n D m) :
    EdgeProgram D (H × Generators n D (nextSize n p c m)) (n*(m+p)+n*(m+p)) :=
  let q := choose s
  let frozen := augment s.2 q
  (batchProgram e ctx (probes frozen)).map (fun y =>
    (respond (s,contextQueries ctx q,y),augment (outputs frozen y) (contextDisclosures ctx names)))

theorem roundProgram_correct {H : Type*} {n D m p c T : ℕ} (hT : T ≤ D) (e : Edge n)
    (choose : H × Generators n D m → Queries n D p)
    (respond : StepData H n D m p T → H) (names : Vertex n → Fin c → Option (Fin T))
    (s : H × Generators n D m) (z : Latent n D) :
    EdgeProgram.eval (roundProgram e (context T hT e z) choose respond names s) (z.2 e) =
      round T hT choose respond names s z := by
  simp only [roundProgram,EdgeProgram.eval_map,batchProgram_correct]
  rfl

end Bilevel.TransportRound
