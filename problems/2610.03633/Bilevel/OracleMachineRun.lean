import Bilevel.OracleMachine
import Bilevel.OracleCodeConsumption

/-! Pathwise execution laws for the concrete compiled machines. Bind switches
to the continuation immediately at the first component's final actual call. -/
noncomputable section
namespace Bilevel.OracleCode.Machine
open BorelAdaptive
variable {Q O A B C : Space} {Seed : Type*}

def execute (p : Machine Q O A B) (response : Q → Seed → O)
    (s : ℕ → Seed) (a : A) (n : ℕ) : p.state :=
  run p.program (fun _ : Unit => response) () s (p.start a) n

def Correct (p : Machine Q O A B) (c : Code Q O A B) : Prop :=
  ∀ (Seed : Type) (response : Q → Seed → O) (s : ℕ → Seed) (a : A),
    let v := eval response c (a,s)
    p.program.halt (execute p response s a v.1.2.2)=true ∧
    (∀ n<v.1.2.2,p.program.halt (execute p response s a n)=false) ∧
    p.program.output (execute p response s a v.1.2.2)=v.1.1

theorem pure_correct (q₀ : Q) (f : A → B) (hf : Measurable f) :
    Correct (pure (O:=O) q₀ f hf) (.pure f hf) := by
  intro Seed response s a
  exact ⟨rfl,fun n hn => False.elim (Nat.not_lt_zero _ hn),rfl⟩

theorem call_correct (o₀ : O) : Correct (call (Q:=Q) o₀) .call := by
  intro Seed response s a
  refine ⟨rfl,?_,rfl⟩
  intro n hn
  have hn0 : n=0 := by simpa only [eval] using Nat.lt_one_iff.mp hn
  subst n
  rfl

theorem reparam_correct (p : Machine Q O A B) (c : Code Q O A B) (hp : Correct p c)
    {I : Space} (f : I → A) (hf : Measurable f) :
    Correct (reparam p f hf) (.reparam c f hf) := by
  intro Seed response s a
  exact hp Seed response s (f a)

theorem run_add {S Y : Type*} [MeasurableSpace S] [MeasurableSpace Y]
    (p : Program S Q O Y) (response : Q → Seed → O) (s : ℕ → Seed)
    (u : S) (n m : ℕ) :
    run p (fun _ : Unit => response) () s u (n+m)=
      run p (fun _ : Unit => response) () (fun k => s (n+k))
        (run p (fun _ : Unit => response) () s u n) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change step p (fun _ : Unit => response) () (s (n+m))
        (run p (fun _ : Unit => response) () s u (n+m))=
        step p (fun _ : Unit => response) () (s (n+m))
          (run p (fun _ : Unit => response) () (fun k => s (n+k))
            (run p (fun _ : Unit => response) () s u n) m)
      rw [ih]

theorem bind_run_inr (p : Machine Q O A B) (q : Machine Q O (prod A B) C)
    (response : Q → Seed → O) (s : ℕ → Seed) (u : q.state) (n : ℕ) :
    run (bind p q).program (fun _ : Unit => response) () s (Sum.inr u) n=
      Sum.inr (run q.program (fun _ : Unit => response) () s u n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [run,ih,run]
      simp only [step,bind,Sum.elim_inr,bindUpdate]
      split <;> rfl

theorem bind_run_first (p : Machine Q O A B) (q : Machine Q O (prod A B) C)
    (response : Q → Seed → O) (s : ℕ → Seed) (a : A) (N : ℕ)
    (hN : ∀ k<N,p.program.halt (execute p response s a k)=false)
    (n : ℕ) (hn : n≤N) :
    execute (bind p q) response s a n=enter p q (a,execute p response s a n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hlt : n<N := Nat.lt_of_succ_le hn
      have hi := ih (Nat.le_of_lt hlt)
      have hh := hN n hlt
      change step (bind p q).program (fun _ : Unit => response) () (s n)
        (execute (bind p q) response s a n)=_
      rw [hi]
      simp only [enter,hh,Bool.false_eq_true,if_false,step,bind,Sum.elim_inl,bindUpdate]
      change enter p q (a,p.program.update (execute p response s a n,
        response (p.program.query (execute p response s a n)) (s n)))=
        enter p q (a,execute p response s a (n+1))
      have hs : execute p response s a (n+1)=p.program.update
          (execute p response s a n,response (p.program.query (execute p response s a n)) (s n)) := by
        change (if p.program.halt (execute p response s a n)=true then execute p response s a n else _)=_
        simp only [hh,Bool.false_eq_true,if_false]
        rfl
      exact congrArg (fun u => enter p q (a,u)) hs.symm

end Bilevel.OracleCode.Machine
