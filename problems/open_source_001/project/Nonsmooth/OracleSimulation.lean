import Nonsmooth.Embedding

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- A state machine with an external seed. Each recursive step makes one scalar-value call. -/
structure Policy (Ω S X : Type*) where
  initial : Ω → S
  query : ℕ → Ω → S → X
  update : ℕ → Ω → S → ℝ → S
  output : Ω → S → X

def Policy.run {Ω S X : Type*} (p : Policy Ω S X) (f : X → ℝ) (ω : Ω) : ℕ → S
  | 0 => p.initial ω
  | n + 1 => let st := p.run f ω n
    p.update n ω st (f (p.query n ω st))

def Policy.result {Ω S X : Type*} (p : Policy Ω S X) (f : X → ℝ) (ω : Ω) (T : ℕ) : X :=
  p.output ω (p.run f ω T)

def Policy.simulate {Ω S X Z : Type*} (p : Policy Ω S X) (q : X → Z)
    (reconstruct : X → ℝ → ℝ) : Policy Ω S Z where
  initial := p.initial
  query n ω st := q (p.query n ω st)
  update n ω st y := p.update n ω st (reconstruct (p.query n ω st) y)
  output ω st := q (p.output ω st)

/-- Exact reconstruction of every response implies equality of states for every seed and budget. -/
theorem simulation_run_exact {Ω S X Z : Type*} (p : Policy Ω S X)
    (q : X → Z) (reconstruct : X → ℝ → ℝ) (f : Z → ℝ) (F : X → ℝ)
    (h : ∀ x, reconstruct x (f (q x)) = F x) (ω : Ω) (T : ℕ) :
    (p.simulate q reconstruct).run f ω T = p.run F ω T := by
  induction T with
  | zero => rfl
  | succ n ih =>
    simp only [Policy.run]
    rw [ih]
    change p.update n ω (p.run F ω n)
      (reconstruct (p.query n ω (p.run F ω n)) (f (q (p.query n ω (p.run F ω n))))) = _
    rw [h]

theorem simulation_output_exact {Ω S X Z : Type*} (p : Policy Ω S X)
    (q : X → Z) (reconstruct : X → ℝ → ℝ) (f : Z → ℝ) (F : X → ℝ)
    (h : ∀ x, reconstruct x (f (q x)) = F x) (ω : Ω) (T : ℕ) :
    (p.simulate q reconstruct).result f ω T = q (p.result F ω T) := by
  unfold Policy.result
  rw [simulation_run_exact p q reconstruct f F h ω T]
  rfl

def lifted {X : Type*} (A s : ℝ) (coord penalty : X → ℝ) (f : ℝ → ℝ) (x : X) : ℝ :=
  A * extended f (coord x / s) + penalty x

def reconstructValue {X : Type*} (A s : ℝ) (coord penalty : X → ℝ) (x : X) (y : ℝ) : ℝ :=
  A * ((coord x / s) ^ 2 / 2 + y - (clip (coord x / s)) ^ 2 / 2 +
    max (|coord x / s| - 1) 0) + penalty x

theorem lifted_one_call {X : Type*} (A s : ℝ) (coord penalty : X → ℝ)
    (f : ℝ → ℝ) (x : X) :
    reconstructValue A s coord penalty x (f (clip (coord x / s))) = lifted A s coord penalty f x := by
  rw [lifted, extension_exact_reconstruction]
  rfl

theorem lifted_simulation_exact {Ω S X : Type*} (p : Policy Ω S X) (A s : ℝ)
    (coord penalty : X → ℝ) (f : ℝ → ℝ) (ω : Ω) (T : ℕ) :
    (p.simulate (fun x => clip (coord x / s)) (reconstructValue A s coord penalty)).result f ω T =
      clip (coord (p.result (lifted A s coord penalty f) ω T) / s) :=
  simulation_output_exact p _ _ f _ (lifted_one_call A s coord penalty f) ω T

theorem lifted_loss_transfer {X : Type*} {A s : ℝ} (hA : 0 ≤ A)
    (coord penalty : X → ℝ) (hp : ∀ x, 0 ≤ penalty x) (f : ℝ → ℝ) (fstar : ℝ) (x : X) :
    A * (f (clip (coord x / s)) - fstar) ≤ lifted A s coord penalty f x - A * fstar := by
  have h := mul_le_mul_of_nonneg_left (extension_loss f (coord x / s)) hA
  unfold lifted
  linarith [hp x]

end
end Nonsmooth
