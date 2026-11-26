import GradientHessian.Machine
import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-! Public finite oracle schedules compile to measurable policies. Exact
execution and pathwise query budgets hold for arbitrary oracle functions. -/

noncomputable section
namespace GradientHessian.ClockedOracle
open MeasureTheory

variable {Seed W X Y Z : Type*} [MeasurableSpace Seed] [MeasurableSpace W]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

structure Program (Seed W X Y Z : Type*) [MeasurableSpace Seed] [MeasurableSpace W]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] where
  length : ℕ
  /-- 0: internal update, 1: ordinary query, 2: rich query. -/
  kind : ℕ → Fin 3
  initial : Seed → W
  point : ℕ → W → X
  output : W → X
  think : ℕ → W → W
  ordinaryNext : ℕ → W × Y → W
  richNext : ℕ → W × Z → W
  initial_measurable : Measurable initial
  point_measurable : ∀ n,Measurable (point n)
  output_measurable : Measurable output
  think_measurable : ∀ n,Measurable (think n)
  ordinaryNext_measurable : ∀ n,Measurable (ordinaryNext n)
  richNext_measurable : ∀ n,Measurable (richNext n)

theorem measurable_nat_param {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (f : ℕ → A → B) (hf : ∀ n,Measurable (f n)) : Measurable (fun p : ℕ × A => f p.1 p.2) := by
  have h : Measurable (fun q : A × ℕ => f q.2 q.1) := measurable_from_prod_countable hf
  exact h.comp measurable_swap

def queryMode (k : Fin 3) : Fin 4 := ⟨k.val+1,by omega⟩

@[simp] theorem queryMode_ne_zero (k : Fin 3) : queryMode k ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp only [queryMode,Fin.val_zero] at this
  omega

@[simp] theorem queryMode_eq_two (k : Fin 3) : queryMode k=2 ↔ k=1 := by
  fin_cases k <;> decide

@[simp] theorem queryMode_eq_three (k : Fin 3) : queryMode k=3 ↔ k=2 := by
  fin_cases k <;> decide

def Program.policy (p : Program Seed W X Y Z) : Machine.Policy Seed (ℕ × W) X Y Z where
  initial := fun seed => (0,p.initial seed)
  mode := fun s => if s.1<p.length then queryMode (p.kind s.1) else 0
  point := fun s => p.point s.1 s.2
  output := fun s => p.output s.2
  think := fun s => (s.1+1,p.think s.1 s.2)
  ordinaryNext := fun s => (s.1.1+1,p.ordinaryNext s.1.1 (s.1.2,s.2))
  richNext := fun s => (s.1.1+1,p.richNext s.1.1 (s.1.2,s.2))
  initial_measurable := measurable_const.prodMk p.initial_measurable
  mode_measurable := (measurable_of_countable (fun n => if n<p.length then queryMode (p.kind n) else 0)).comp measurable_fst
  point_measurable := measurable_nat_param p.point p.point_measurable
  output_measurable := p.output_measurable.comp measurable_snd
  think_measurable := ((measurable_of_countable (fun n : ℕ => n+1)).comp measurable_fst).prodMk
    (measurable_nat_param p.think p.think_measurable)
  ordinaryNext_measurable := by
    have h := (measurable_nat_param p.ordinaryNext p.ordinaryNext_measurable).comp
      (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
    exact ((measurable_of_countable (fun n : ℕ => n+1)).comp measurable_fst.fst).prodMk h
  richNext_measurable := by
    have h := (measurable_nat_param p.richNext p.richNext_measurable).comp
      (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
    exact ((measurable_of_countable (fun n : ℕ => n+1)).comp measurable_fst.fst).prodMk h

def Program.advance (p : Program Seed W X Y Z) (ordinary : X → Y) (rich : X → Z) (n : ℕ) (w : W) : W :=
  if p.kind n=0 then p.think n w
  else if p.kind n=1 then p.ordinaryNext n (w,ordinary (p.point n w))
  else p.richNext n (w,rich (p.point n w))

def Program.evaluate (p : Program Seed W X Y Z) (ordinary : X → Y) (rich : X → Z) : ℕ → Seed → W
  | 0 => p.initial
  | n+1 => fun seed => p.advance ordinary rich n (p.evaluate ordinary rich n seed)

theorem Program.step_of_lt (p : Program Seed W X Y Z) (ordinary : X → Y) (rich : X → Z)
    (n : ℕ) (w : W) (hn : n<p.length) :
    p.policy.step ordinary rich (n,w)=(n+1,p.advance ordinary rich n w) := by
  have hk := (p.kind n).isLt
  generalize he : p.kind n=k at *
  fin_cases k <;> simp [Machine.Policy.step,policy,advance,hn,he,queryMode]

theorem Program.run_prefix (p : Program Seed W X Y Z) (ordinary : X → Y) (rich : X → Z)
    (n : ℕ) (hn : n≤p.length) (seed : Seed) :
    p.policy.run ordinary rich n seed=(n,p.evaluate ordinary rich n seed) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change p.policy.step ordinary rich (p.policy.run ordinary rich n seed)=_
    rw [ih (by omega),p.step_of_lt ordinary rich n _ (by omega)]
    rfl

theorem Program.halt (p : Program Seed W X Y Z) (ordinary : X → Y) (rich : X → Z) (seed : Seed) :
    p.policy.mode (p.policy.run ordinary rich p.length seed)=0 := by
  rw [p.run_prefix ordinary rich _ le_rfl seed]
  simp [policy]

theorem Program.terminates (p : Program Seed W X Y Z) (ordinary : X → Y) (rich : X → Z) :
    p.policy.Terminates ordinary rich := fun seed => ⟨p.length,p.halt ordinary rich seed⟩

theorem Program.run_final (p : Program Seed W X Y Z) (ordinary : X → Y) (rich : X → Z)
    (n : ℕ) (hn : p.length≤n) (seed : Seed) :
    p.policy.run ordinary rich n seed=(p.length,p.evaluate ordinary rich p.length seed) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [p.policy.run_after_halt ordinary rich seed (p.halt ordinary rich seed),p.run_prefix ordinary rich _ le_rfl seed]

theorem Program.mode_run (p : Program Seed W X Y Z) (ordinary : X → Y) (rich : X → Z) (n : ℕ) (seed : Seed) :
    p.policy.mode (p.policy.run ordinary rich n seed)=if n<p.length then queryMode (p.kind n) else 0 := by
  by_cases hn : n<p.length
  · rw [p.run_prefix ordinary rich n hn.le seed]
    rfl
  · rw [p.run_final ordinary rich n (by omega) seed]
    simp [policy,hn]

def Program.count (p : Program Seed W X Y Z) (k : Fin 3) : ℕ :=
  ∑ n ∈ Finset.range p.length,if p.kind n=k then 1 else 0

theorem truncated_sum_le (f : ℕ → ℕ) (n L : ℕ) :
    (∑ i ∈ Finset.range n,if i<L then f i else 0) ≤∑ i ∈ Finset.range L,f i := by
  have he : (Finset.range n).filter (fun i => i<L)=Finset.range (min n L) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_range,lt_min_iff]
  rw [← Finset.sum_filter,he]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (min_le_right n L))

theorem Program.hasCaps (p : Program Seed W X Y Z) (ordinary : X → Y) (rich : X → Z) :
    p.policy.HasCaps ordinary rich (p.count 1) (p.count 2) := by
  intro seed n
  constructor
  · unfold Machine.Policy.ordinaryCount count
    convert truncated_sum_le (fun i => if p.kind i=1 then 1 else 0) n p.length using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [p.mode_run ordinary rich]
    by_cases hn : i<p.length <;> simp [hn]
  · unfold Machine.Policy.richCount count
    convert truncated_sum_le (fun i => if p.kind i=2 then 1 else 0) n p.length using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [p.mode_run ordinary rich]
    by_cases hn : i<p.length <;> simp [hn]

theorem Program.output_final (p : Program Seed W X Y Z) (ordinary : X → Y) (rich : X → Z) (seed : Seed) :
    p.policy.output (p.policy.run ordinary rich p.length seed)=p.output (p.evaluate ordinary rich p.length seed) := by
  rw [p.run_prefix ordinary rich _ le_rfl seed]
  rfl

end GradientHessian.ClockedOracle
