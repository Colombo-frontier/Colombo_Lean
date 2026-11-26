import Bilevel.OrdinaryFrameObserver

/-! Compilation of a Borel, success-driven single-frame reveal machine
into the actual two-precoin-insertion raw genie. Projection replies are
ignored by the source computation; the requested full column is supplied
only after both insertions. The terminal output is inserted as well. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.SourceFrameActions
open EuclideanGaussian ProjectionPosterior TransportControllerMachine

structure Rules (H : Memory.{u}) (d T : ℕ) where
  first : ℕ → H → Space d
  first_measurable : ∀ t, Measurable (first t)
  second : ℕ → H → Space d
  second_measurable : ∀ t, Measurable (second t)
  request : ℕ → H → Bool
  request_measurable : ∀ t, Measurable (request t)
  column : ℕ → H → Fin T
  column_measurable : ∀ t, Measurable (column t)
  finish : ℕ → H × Space d → H
  finish_measurable : ∀ t, Measurable (finish t)
  output : H → Space d
  output_measurable : Measurable output

abbrev Marked (H : Memory.{u}) := Memory.of (H × Bool)

def mark {H : Memory.{u}} {d T : ℕ} (L : Rules H d T) (t : ℕ) (h : H) : Marked H :=
  if L.request t h then (h,true) else (L.finish t (h,0),false)

theorem mark_measurable {H : Memory.{u}} {d T : ℕ} (L : Rules H d T) (t : ℕ) :
    Measurable (mark L t) := by
  have hreq := (L.request_measurable t) (measurableSet_singleton true)
  exact (measurable_id.prodMk measurable_const).ite hreq
    (((L.finish_measurable t).comp (measurable_id.prodMk measurable_const)).prodMk measurable_const)

def compileRules {H : Memory.{u}} {d T : ℕ} (L : Rules H d T) : OrdinaryFrame.Rules (Marked H) d T where
  first t h := L.first t h.1
  first_measurable t := (L.first_measurable t).comp measurable_fst
  afterFirst _ p := p.1
  afterFirst_measurable _ := measurable_fst
  second t h := L.second t h.1
  second_measurable t := (L.second_measurable t).comp measurable_fst
  afterSecond t p := mark L t p.1.1
  afterSecond_measurable t := (mark_measurable L t).comp (measurable_fst.comp measurable_fst)
  success _ := {h | h.2=true}
  success_measurable _ := measurable_snd (measurableSet_singleton true)
  column t h := L.column t h.1
  column_measurable t := (L.column_measurable t).comp measurable_fst
  afterReveal t p := (L.finish t (p.1.1,p.2.1),false)
  afterReveal_measurable t := ((L.finish_measurable t).comp
    ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))).prodMk measurable_const
  output h := L.output h.1
  output_measurable := L.output_measurable.comp measurable_fst

def step {H : Memory.{u}} {d T : ℕ} (L : Rules H d T) (t : ℕ) (h : H) (U : Frame d T) : H :=
  L.finish t (h,if L.request t h then U (L.column t h) else 0)

def run {H : Memory.{u}} {d T : ℕ} (L : Rules H d T) : ℕ → ℕ → H → Frame d T → H
  | 0,_,h,_ => h
  | n+1,t,h,U => run L n (t+1) (step L t h U) U

theorem precoin_memory {H : Memory.{u}} {d T : ℕ} (L : Rules H d T) (t : ℕ) (h : H)
    (V : Submodule ℝ (Space d)) (S : Set (Fin T)) (U : Frame d T) :
    (OrdinaryFrame.precoin (compileRules L) t ((h,false),(V,S)) U).1 = mark L t h := rfl

theorem compiled_run_memory {H : Memory.{u}} {d T : ℕ} (L : Rules H d T) :
    ∀ n R t (h : H) (V : Submodule ℝ (Space d)) (S : Set (Fin T)) (U : Frame d T),
      n ≤ R → (OrdinaryFrame.run (compileRules L) n R t ((h,false),(V,S)) U).1 = (run L n t h U,false) := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro R t h V S U hR
    cases R with
    | zero => omega
    | succ R =>
      have hn : n ≤ R := by omega
      by_cases hr : L.request t h=true
      · have hs : (OrdinaryFrame.precoin (compileRules L) t ((h,false),(V,S)) U).1 ∈
            (compileRules L).success t := by
          change (OrdinaryFrame.precoin (compileRules L) t ((h,false),(V,S)) U).1.2 = true
          rw [precoin_memory]
          simp only [mark,if_pos hr]
        rw [OrdinaryFrame.run,if_pos hs]
        simpa only [run,step,if_pos hr,OrdinaryFrame.revealStep,OrdinaryFrame.precoin,
          OrdinaryFrame.queryStep,compileRules,mark] using
          ih R (t+1) (L.finish t (h,U (L.column t h)))
            ((OrdinaryFrame.revealStep ((compileRules L).column t) ((compileRules L).afterReveal t)
              (OrdinaryFrame.precoin (compileRules L) t ((h,false),(V,S)) U) U).2.1)
            ((OrdinaryFrame.revealStep ((compileRules L).column t) ((compileRules L).afterReveal t)
              (OrdinaryFrame.precoin (compileRules L) t ((h,false),(V,S)) U) U).2.2) U hn
      · have hs : ¬(OrdinaryFrame.precoin (compileRules L) t ((h,false),(V,S)) U).1 ∈
            (compileRules L).success t := by
          change ¬(OrdinaryFrame.precoin (compileRules L) t ((h,false),(V,S)) U).1.2 = true
          rw [precoin_memory]
          simp only [mark,if_neg hr,Bool.false_eq_true,not_false_eq_true]
        rw [OrdinaryFrame.run,if_neg hs]
        simpa only [run,step,if_neg hr,OrdinaryFrame.precoin,OrdinaryFrame.queryStep,compileRules,mark] using
          ih (R+1) (t+1) (L.finish t (h,0))
            ((OrdinaryFrame.precoin (compileRules L) t ((h,false),(V,S)) U).2.1)
            ((OrdinaryFrame.precoin (compileRules L) t ((h,false),(V,S)) U).2.2) U (by omega)

end Bilevel.SourceFrameActions
