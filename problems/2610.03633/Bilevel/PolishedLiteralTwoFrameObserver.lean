import Bilevel.PolishedLiteralPrefixSchedules

/-! Two selected-frame views of one public virtual execution. Each view
stores the complete other frame as independent context, and only the
success-disclosed prefix of its selected frame. -/
noncomputable section
open MeasureTheory
namespace Bilevel.PolishedLiteralActualObserver
open EuclideanGaussian ProjectionPosterior TransportControllerMachine SourceFrameActions
set_option autoImplicit false
variable {dx du Kx Ku : ℕ} {S Q O Y : Type}
  [MeasurableSpace S] [MeasurableSpace Q] [MeasurableSpace O] [MeasurableSpace Y]
  (Px : PrefixSchedule Kx) (Pu : PrefixSchedule Ku)
  (A : BorelAdaptive.Program S Q O Y)
  (reply : Frame dx Kx → Frame du Ku → Q → ℕ → Bool → O)
  (hreply : Measurable (fun z : (Frame dx Kx × Frame du Ku) × (Q × (ℕ × Bool)) =>
    reply z.1.1 z.1.2 z.2.1 z.2.2.1 z.2.2.2))

def advance (a : ℕ) (b : Bool) : ℕ := a+if b=true then 1 else 0

def macroEvaluator (U : Frame du Ku) (q : Q) (a : ℕ) (b : Bool) (V : Frame dx Kx) : O :=
  reply V (prefixColumns U (Pu.count (advance a b))) q a b

def microEvaluator (U : Frame dx Kx) (q : Q) (a : ℕ) (b : Bool) (V : Frame du Ku) : O :=
  reply (prefixColumns U (Px.count (advance a b))) V q a b

include hreply in
theorem macroEvaluator_measurable :
    Measurable (fun z : Frame du Ku × (Q × (ℕ × (Bool × Frame dx Kx))) =>
      macroEvaluator Pu reply z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) := by
  have hp : Measurable (fun z : Frame du Ku × (Q × (ℕ × (Bool × Frame dx Kx))) =>
      prefixColumns z.1 (Pu.count (advance z.2.2.1 z.2.2.2.1))) :=
    prefixColumns_measurable.comp (measurable_fst.prodMk
      ((measurable_of_countable (fun p : ℕ × Bool => Pu.count (advance p.1 p.2))).comp
        ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
          (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))))
  have ht : Measurable (fun z : Frame du Ku × (Q × (ℕ × (Bool × Frame dx Kx))) =>
      ((z.2.2.2.2,prefixColumns z.1 (Pu.count (advance z.2.2.1 z.2.2.2.1))),
        (z.2.1,(z.2.2.1,z.2.2.2.1)))) :=
    ((measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).prodMk hp).prodMk
    ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
        (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))))
  exact hreply.comp ht

include hreply in
theorem microEvaluator_measurable :
    Measurable (fun z : Frame dx Kx × (Q × (ℕ × (Bool × Frame du Ku))) =>
      microEvaluator Px reply z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) := by
  have hp : Measurable (fun z : Frame dx Kx × (Q × (ℕ × (Bool × Frame du Ku))) =>
      prefixColumns z.1 (Px.count (advance z.2.2.1 z.2.2.2.1))) :=
    prefixColumns_measurable.comp (measurable_fst.prodMk
      ((measurable_of_countable (fun p : ℕ × Bool => Px.count (advance p.1 p.2))).comp
        ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
          (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))))
  have ht : Measurable (fun z : Frame dx Kx × (Q × (ℕ × (Bool × Frame du Ku))) =>
      ((prefixColumns z.1 (Px.count (advance z.2.2.1 z.2.2.2.1)),z.2.2.2.2),
        (z.2.1,(z.2.2.1,z.2.2.2.1)))) :=
    (hp.prodMk (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))).prodMk
    ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
        (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))))
  exact hreply.comp ht

/-- Both selected views use the same old-counter reply and actual update. -/
def masterStep (draws : ℕ → Bool) (U : Frame dx Kx) (V : Frame du Ku) (t : ℕ) (s : S × ℕ) : S × ℕ :=
  if A.halt s.1=true then s else
    let b := draws t
    let a' := advance s.2 b
    (A.update (s.1,reply (prefixColumns U (Px.count a')) (prefixColumns V (Pu.count a'))
      (A.query s.1) s.2 b),a')

def masterRun (draws : ℕ → Bool) (U : Frame dx Kx) (V : Frame du Ku) : ℕ → ℕ → S × ℕ → S × ℕ
  | 0,_,s => s
  | n+1,t,s => masterRun draws U V n (t+1) (masterStep Px Pu A reply draws U V t s)

theorem macro_public_run (draws : ℕ → Bool) (U : Frame dx Kx) (V : Frame du Ku) :
    ∀ n t s,publicRun Px A (macroEvaluator Pu reply) V draws U n t s=
      masterRun Px Pu A reply draws U V n t s := by
  intro n
  induction n with
  | zero => intros;rfl
  | succ n ih =>
    intro t s
    rw [publicRun,masterRun,ih]
    rfl

theorem micro_public_run (draws : ℕ → Bool) (U : Frame dx Kx) (V : Frame du Ku) :
    ∀ n t s,publicRun Pu A (microEvaluator Px reply) U draws V n t s=
      masterRun Px Pu A reply draws U V n t s := by
  intro n
  induction n with
  | zero => intros;rfl
  | succ n ih =>
    intro t s
    rw [publicRun,masterRun,ih]
    rfl

variable (hx : 0<Kx) (hu : 0<Ku)
  (xquery : Q → Space dx) (hxquery : Measurable xquery)
  (uquery vquery : Q → Space du) (huquery : Measurable uquery) (hvquery : Measurable vquery)
  (xoutput : Y → Space dx) (hxoutput : Measurable xoutput)
  (uoutput : Y → Space du) (huoutput : Measurable uoutput)

def macroRules : Rules (ObserverMemory (Frame du Ku) S dx Kx) dx Kx :=
  observerRules Px hx A (macroEvaluator Pu reply) (macroEvaluator_measurable Pu reply hreply)
    xquery (fun _ => 0) hxquery measurable_const xoutput hxoutput

def microRules : Rules (ObserverMemory (Frame dx Kx) S du Ku) du Ku :=
  observerRules Pu hu A (microEvaluator Px reply) (microEvaluator_measurable Px reply hreply)
    uquery vquery huquery hvquery uoutput huoutput

include hreply in
theorem macro_run_same (draws : ℕ → Bool) (U : Frame dx Kx) (V : Frame du Ku) (n t : ℕ) (s : S × ℕ) :
    run (macroRules Px Pu A reply hreply hx xquery hxquery xoutput hxoutput)
      n t (lift Px V draws s U) U=
      lift Px V draws (masterRun Px Pu A reply draws U V n t s) U := by
  rw [macroRules,run_lift,macro_public_run]

include hreply in
theorem micro_run_same (draws : ℕ → Bool) (U : Frame dx Kx) (V : Frame du Ku) (n t : ℕ) (s : S × ℕ) :
    run (microRules Px Pu A reply hreply hu uquery vquery huquery hvquery uoutput huoutput)
      n t (lift Pu U draws s V) V=
      lift Pu U draws (masterRun Px Pu A reply draws U V n t s) V := by
  rw [microRules,run_lift,micro_public_run]

end Bilevel.PolishedLiteralActualObserver
