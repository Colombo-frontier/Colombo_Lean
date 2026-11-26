import Bilevel.SourceFrameActions

/-! Explicit accumulated spaces and named-column sets for the compiled
source actions. The terminal query is separate from the finite source run. -/
noncomputable section
namespace Bilevel.SourceFrameActions
open EuclideanGaussian ProjectionPosterior TransportControllerMachine
universe u

abbrev State (H : Memory.{u}) (d T : ℕ) := H × (Submodule ℝ (Space d) × Set (Fin T))

variable {H : Memory.{u}} {d T : ℕ}

def observeStep (L : Rules H d T) (t : ℕ) (s : State H d T) (U : Frame d T) : State H d T :=
  let V := (s.2.1 ⊔ Submodule.span ℝ {L.first t s.1}) ⊔ Submodule.span ℝ {L.second t s.1}
  if L.request t s.1 then
    (step L t s.1 U,(V ⊔ Submodule.span ℝ {U (L.column t s.1)},insert (L.column t s.1) s.2.2))
  else (step L t s.1 U,(V,s.2.2))

def observeRun (L : Rules H d T) : ℕ → ℕ → State H d T → Frame d T → State H d T
  | 0,_,s,_ => s
  | n+1,t,s,U => observeRun L n (t+1) (observeStep L t s U) U

def finishObservation (L : Rules H d T) (s : State H d T) : OrdinaryFrame.State (Marked H) d T :=
  ((s.1,false),(s.2.1 ⊔ Submodule.span ℝ {L.output s.1},s.2.2))

theorem observeStep_memory (L : Rules H d T) (t : ℕ) (s : State H d T) (U : Frame d T) :
    (observeStep L t s U).1 = step L t s.1 U := by
  unfold observeStep
  split <;> rfl

theorem observeRun_memory (L : Rules H d T) : ∀ n t (s : State H d T) (U : Frame d T),
    (observeRun L n t s U).1 = run L n t s.1 U := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih => intros; rw [observeRun,ih,observeStep_memory,run]

theorem observeRun_add (L : Rules H d T) (n m t : ℕ) (s : State H d T) (U : Frame d T) :
    observeRun L (n+m) t s U = observeRun L m (t+n) (observeRun L n t s U) U := by
  induction n generalizing t s with
  | zero => simp only [Nat.zero_add,Nat.add_zero,observeRun]
  | succ n ih =>
    rw [Nat.succ_add,observeRun,ih,observeRun]
    congr 1
    omega

theorem observeStep_space_mono (L : Rules H d T) (t : ℕ) (s : State H d T) (U : Frame d T) :
    s.2.1 ≤ (observeStep L t s U).2.1 := by
  unfold observeStep
  split
  · exact le_sup_of_le_left (le_sup_of_le_left le_sup_left)
  · exact le_sup_of_le_left le_sup_left

theorem observeRun_space_mono (L : Rules H d T) : ∀ n t (s : State H d T) (U : Frame d T),
    s.2.1 ≤ (observeRun L n t s U).2.1 := by
  intro n
  induction n with
  | zero => intros; exact le_rfl
  | succ n ih =>
    intro t s U
    exact (observeStep_space_mono L t s U).trans (ih (t+1) _ U)

theorem observeStep_first_mem (L : Rules H d T) (t : ℕ) (s : State H d T) (U : Frame d T) :
    L.first t s.1 ∈ (observeStep L t s U).2.1 := by
  have h : L.first t s.1 ∈ s.2.1 ⊔ Submodule.span ℝ {L.first t s.1} :=
    Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
  unfold observeStep
  split
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left h)
  · exact Submodule.mem_sup_left h

theorem observeRun_first_mem (L : Rules H d T) (n t : ℕ) (s : State H d T) (U : Frame d T)
    (k : ℕ) (hk : k<n) :
    L.first (t+k) (observeRun L k t s U).1 ∈ (observeRun L n t s U).2.1 := by
  have hn : n=k+1+(n-(k+1)) := by omega
  have he := observeRun_add L (k+1) (n-(k+1)) t s U
  rw [←hn] at he
  rw [he,observeRun_add L k 1]
  have h := observeStep_first_mem L (t+k) (observeRun L k t s U) U
  exact observeRun_space_mono L (n-(k+1)) (t+(k+1)) _ U h

theorem compiled_run_observation (L : Rules H d T) :
    ∀ n R t (s : State H d T) (U : Frame d T), n≤R →
      OrdinaryFrame.run (compileRules L) n R t ((s.1,false),s.2) U =
        finishObservation L (observeRun L n t s U) := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro R t s U hR
    cases R with
    | zero => omega
    | succ R =>
      by_cases hr : L.request t s.1=true
      · have hs : (OrdinaryFrame.precoin (compileRules L) t ((s.1,false),s.2) U).1 ∈
            (compileRules L).success t := by
          change (OrdinaryFrame.precoin (compileRules L) t ((s.1,false),s.2) U).1.2=true
          rw [precoin_memory]
          simp only [mark,if_pos hr]
        rw [OrdinaryFrame.run,if_pos hs,observeRun]
        simpa only [observeStep,step,if_pos hr,OrdinaryFrame.revealStep,OrdinaryFrame.precoin,
          OrdinaryFrame.queryStep,compileRules,mark] using
          ih R (t+1) (observeStep L t s U) U (by omega)
      · have hs : ¬(OrdinaryFrame.precoin (compileRules L) t ((s.1,false),s.2) U).1 ∈
            (compileRules L).success t := by
          change ¬(OrdinaryFrame.precoin (compileRules L) t ((s.1,false),s.2) U).1.2=true
          rw [precoin_memory]
          simp only [mark,if_neg hr,Bool.false_eq_true,not_false_eq_true]
        rw [OrdinaryFrame.run,if_neg hs,observeRun]
        simpa only [observeStep,step,if_neg hr,OrdinaryFrame.precoin,
          OrdinaryFrame.queryStep,compileRules,mark] using
          ih (R+1) (t+1) (observeStep L t s U) U (by omega)

end Bilevel.SourceFrameActions
