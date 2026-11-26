import Bilevel.TransportControllerReconstruction

/-! Full-horizon current-edge reconstruction of the actual adaptive frozen
round controller. It uses the same single edge map at every round and feeds
all previous reconstructed responses into the next adaptive request. -/
noncomputable section
namespace Bilevel.TransportNetwork.EdgeProgram
open EuclideanGaussian

def pad {D b : ℕ} {β : Type*} (P : EdgeProgram D β b) : (a : ℕ) → EdgeProgram D β (b+a)
  | 0 => P
  | a+1 => .skip (pad P a)

theorem eval_pad {D b : ℕ} {β : Type*} (P : EdgeProgram D β b) (a : ℕ) (O : OrthogonalHaar.Group D) :
    eval (pad P a) O = eval P O := by
  induction a with
  | zero => rfl
  | succ a ih => exact ih

def bind {D b : ℕ} {α β : Type*} : {a : ℕ} → EdgeProgram D α a →
    (α → EdgeProgram D β b) → EdgeProgram D β (b+a)
  | a,.halt x,f => pad (f x) a
  | _,.skip P,f => .skip (bind P f)
  | _,.forward q next,f => .forward q (fun y => bind (next y) f)
  | _,.reverse q next,f => .reverse q (fun y => bind (next y) f)

theorem eval_bind {D a b : ℕ} {α β : Type*} (P : EdgeProgram D α a)
    (f : α → EdgeProgram D β b) (O : OrthogonalHaar.Group D) :
    eval (bind P f) O = eval (f (eval P O)) O := by
  induction P with
  | halt x => exact eval_pad (f x) _ O
  | skip P ih => exact ih
  | forward q next ih => exact ih (O • q)
  | reverse q next ih => exact ih (O⁻¹ • q)

end Bilevel.TransportNetwork.EdgeProgram

namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork

def historySize (n p c m : ℕ) : ℕ → ℕ
  | 0 => 0
  | t+1 => n*(size n p c m t+p)+n*(size n p c m t+p)+historySize n p c m t

def historyProgram {H : Type*} {n D p c m T : ℕ} (e : Edge n) (ctx : Context (d := D) e T)
    (choose : ∀ t, H × Generators n D (size n p c m t) → Queries n D p)
    (respond : ∀ t, StepData H n D (size n p c m t) p T → H)
    (names : ℕ → Vertex n → Fin c → Option (Fin T)) (s : H × Generators n D m) :
    (t : ℕ) → EdgeProgram D (H × Generators n D (size n p c m t)) (historySize n p c m t)
  | 0 => .halt s
  | t+1 => (historyProgram e ctx choose respond names s t).bind
      (fun st => roundProgram e ctx (choose t) (respond t) (names t) st)

theorem historyProgram_correct {H : Type*} {n D p c m T : ℕ} (hT : T ≤ D) (e : Edge n)
    (choose : ∀ t, H × Generators n D (size n p c m t) → Queries n D p)
    (respond : ∀ t, StepData H n D (size n p c m t) p T → H)
    (names : ℕ → Vertex n → Fin c → Option (Fin T)) (s : H × Generators n D m)
    (z : Latent n D) (t : ℕ) :
    EdgeProgram.eval (historyProgram e (context T hT e z) choose respond names s t) (z.2 e) =
      run T hT choose respond names s z t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [historyProgram,EdgeProgram.eval_bind,ih,roundProgram_correct]
    rfl

theorem size_uniform (n p c m h t : ℕ) (ht : t≤h) :
    size n p c m t+p ≤ (m+p+c)*(2*n+2)^h := by
  have hp : (2*n+2)^t ≤ (2*n+2)^h := Nat.pow_le_pow_right (by omega) ht
  exact (Nat.le_add_right _ _).trans ((size_bound n p c m t).trans (Nat.mul_le_mul_left _ hp))

theorem historySize_bound (n p c m h : ℕ) :
    historySize n p c m h ≤ 2*n*h*((m+p+c)*(2*n+2)^h) := by
  have hh : ∀ t≤h, historySize n p c m t ≤ 2*n*t*((m+p+c)*(2*n+2)^h) := by
    intro t
    induction t with
    | zero => intro _; simp [historySize]
    | succ t ih =>
      intro ht
      have hi := ih (by omega)
      have hs := size_uniform n p c m h t (by omega)
      dsimp only [historySize]
      nlinarith
  exact hh h le_rfl

end Bilevel.TransportRound
