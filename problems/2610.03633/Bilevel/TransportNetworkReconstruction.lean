import Bilevel.TransportNetworkProtocol
import Bilevel.TransportNetworkContext

/-! Exact adaptive history reconstruction after fixing the full frames and
the other edge maps. All information still required is obtained by successive
linear probes of the CURRENT edge. This is an execution identity. -/
noncomputable section
namespace Bilevel.TransportNetwork
open EuclideanGaussian OrthogonalAction
set_option maxHeartbeats 500000

inductive Event (n D T : ℕ)
  | query (v : Vertex n) (q : Space D) (answer : Fin T → ℝ)
  | named (v : Vertex n) (i : Fin T) (answer : Space D)
  | forward (e : Edge n) (q answer : Space D)
  | reverse (e : Edge n) (q answer : Space D)

def transcript {n D T : ℕ} (hT : T ≤ D) :
    {m : ℕ} → Protocol n D T m → Latent n D → List (Event n D T)
  | _,.halt,_ => []
  | _,.query v q next,z =>
      let y := queryObservation T hT v q z
      .query v q y :: transcript hT (next y) z
  | _,.named v i next,z =>
      let y := namedObservation T hT v i z
      .named v i y :: transcript hT (next y) z
  | _,.forward e q next,z =>
      let y := forwardObservation e q z
      .forward e q y :: transcript hT (next y) z
  | _,.reverse e q next,z =>
      let y := reverseObservation e q z
      .reverse e q y :: transcript hT (next y) z

/-- A finite adaptive program accessing just one fixed edge. A skip is a
deterministic context computation and makes no observation of that edge. -/
inductive EdgeProgram (D : ℕ) (β : Type*) : ℕ → Type _
  | halt {m : ℕ} (value : β) : EdgeProgram D β m
  | skip {m : ℕ} (next : EdgeProgram D β m) : EdgeProgram D β (m+1)
  | forward {m : ℕ} (q : Space D) (next : Space D → EdgeProgram D β m) : EdgeProgram D β (m+1)
  | reverse {m : ℕ} (q : Space D) (next : Space D → EdgeProgram D β m) : EdgeProgram D β (m+1)

namespace EdgeProgram

def eval {D : ℕ} {β : Type*} : {m : ℕ} → EdgeProgram D β m → OrthogonalHaar.Group D → β
  | _,.halt x,_ => x
  | _,.skip P,O => eval P O
  | _,.forward q next,O => eval (next (O • q)) O
  | _,.reverse q next,O => eval (next (O⁻¹ • q)) O

def map {D : ℕ} {β γ : Type*} (f : β → γ) : {m : ℕ} → EdgeProgram D β m → EdgeProgram D γ m
  | _,.halt x => .halt (f x)
  | _,.skip P => .skip (map f P)
  | _,.forward q next => .forward q (fun y => map f (next y))
  | _,.reverse q next => .reverse q (fun y => map f (next y))

theorem eval_map {D m : ℕ} {β γ : Type*} (f : β → γ) (P : EdgeProgram D β m)
    (O : OrthogonalHaar.Group D) : eval (map f P) O = f (eval P O) := by
  induction P with
  | halt x => rfl
  | skip P ih => exact ih
  | forward q next ih => exact ih (O • q)
  | reverse q next ih => exact ih (O⁻¹ • q)

end EdgeProgram

def reconstruct {n D T : ℕ} (hT : T ≤ D) (e : Edge n) (z₀ : Latent n D) :
    {m : ℕ} → Protocol n D T m → EdgeProgram D (List (Event n D T)) m
  | _,.halt => .halt []
  | _,.query v q next =>
      let y := queryObservation T hT v q z₀
      .skip ((reconstruct hT e z₀ (next y)).map (fun xs => Event.query v q y :: xs))
  | _,.named v i next =>
      let y := namedObservation T hT v i z₀
      .skip ((reconstruct hT e z₀ (next y)).map (fun xs => Event.named v i y :: xs))
  | _,.forward f q next =>
      if f=e then .forward q (fun y =>
        (reconstruct hT e z₀ (next y)).map (fun xs => Event.forward f q y :: xs))
      else
        let y := forwardObservation f q z₀
        .skip ((reconstruct hT e z₀ (next y)).map (fun xs => Event.forward f q y :: xs))
  | _,.reverse f q next =>
      if f=e then .reverse q (fun y =>
        (reconstruct hT e z₀ (next y)).map (fun xs => Event.reverse f q y :: xs))
      else
        let y := reverseObservation f q z₀
        .skip ((reconstruct hT e z₀ (next y)).map (fun xs => Event.reverse f q y :: xs))

theorem context_named_eq {n D : ℕ} (T : ℕ) (hT : T ≤ D) (e : Edge n)
    (z z₀ : Latent n D) (hctx : context T hT e z = context T hT e z₀)
    (v : Vertex n) (i : Fin T) : namedObservation T hT v i z = namedObservation T hT v i z₀ :=
  congrArg (fun c : Context (d := D) e T => c.1 v i) hctx

theorem context_query_eq {n D : ℕ} (T : ℕ) (hT : T ≤ D) (e : Edge n)
    (z z₀ : Latent n D) (hctx : context T hT e z = context T hT e z₀)
    (v : Vertex n) (q : Space D) : queryObservation T hT v q z = queryObservation T hT v q z₀ := by
  funext i
  exact congrArg (fun w : Space D => inner q w) (context_named_eq T hT e z z₀ hctx v i)

theorem context_other_edge_eq {n D : ℕ} (T : ℕ) (hT : T ≤ D) (e f : Edge n) (hf : f ≠ e)
    (z z₀ : Latent n D) (hctx : context T hT e z = context T hT e z₀) : z.2 f = z₀.2 f :=
  congrArg (fun c : Context (d := D) e T => c.2 ⟨f,hf⟩) hctx

/-- Every query, answer, named index, and transport direction in the full
adaptive transcript is recovered from the conditioned context and probes of
the single current edge. No global history sufficiency premise is assumed. -/
theorem reconstruct_transcript {n D T m : ℕ} (hT : T ≤ D) (e : Edge n)
    (P : Protocol n D T m) (z₀ z : Latent n D)
    (hctx : context T hT e z = context T hT e z₀) :
    EdgeProgram.eval (reconstruct hT e z₀ P) (z.2 e) = transcript hT P z := by
  induction P with
  | halt => rfl
  | query v q next ih =>
    have hy := context_query_eq T hT e z z₀ hctx v q
    simp only [reconstruct,EdgeProgram.eval,EdgeProgram.eval_map,transcript,hy]
    rw [ih]
  | named v i next ih =>
    have hy := context_named_eq T hT e z z₀ hctx v i
    simp only [reconstruct,EdgeProgram.eval,EdgeProgram.eval_map,transcript,hy]
    rw [ih]
  | forward f q next ih =>
    by_cases hf : f=e
    · subst f
      simp only [reconstruct,if_pos rfl,ite_true,EdgeProgram.eval,EdgeProgram.eval_map,transcript]
      exact congrArg (List.cons (Event.forward e q (forwardObservation e q z))) (ih (forwardObservation e q z))
    · have hO := context_other_edge_eq T hT e f hf z z₀ hctx
      have hy : forwardObservation f q z = forwardObservation f q z₀ := congrArg (fun O => O • q) hO
      simp only [reconstruct,if_neg hf,EdgeProgram.eval,EdgeProgram.eval_map,transcript,hy]
      rw [ih]
  | reverse f q next ih =>
    by_cases hf : f=e
    · subst f
      simp only [reconstruct,if_pos rfl,ite_true,EdgeProgram.eval,EdgeProgram.eval_map,transcript]
      exact congrArg (List.cons (Event.reverse e q (reverseObservation e q z))) (ih (reverseObservation e q z))
    · have hO := context_other_edge_eq T hT e f hf z z₀ hctx
      have hy : reverseObservation f q z = reverseObservation f q z₀ := congrArg (fun O => O⁻¹ • q) hO
      simp only [reconstruct,if_neg hf,EdgeProgram.eval,EdgeProgram.eval_map,transcript,hy]
      rw [ih]

end Bilevel.TransportNetwork
