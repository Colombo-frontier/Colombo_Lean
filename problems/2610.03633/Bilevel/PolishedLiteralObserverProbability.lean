import Bilevel.PolishedLiteralTwoFrameObserver

/-! The actual success-budgeted selected views inherit the source C=128
two-global-frame estimate with exactly N+1 macro raw vectors and 2N+1
micro raw vectors, including terminal outputs. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.PolishedLiteralActualObserver
open EuclideanGaussian ProjectionPosterior TransportControllerMachine SourceFrameActions RawGenieBorel
open PolishedProjectionDimension PolishedTwoFrameProjection
set_option autoImplicit false

private def reindexPolicy {d T m m' R : ℕ} {H : Memory} (e : m=m')
    (P : Policy d T H m R) : Policy d T H m' R := e ▸ P

private theorem safe_reindexPolicy {d T m m' R : ℕ} {H : Memory} (e : m=m')
    (P : Policy d T H m R) (h : H) (V : Submodule ℝ (Space d)) (S : Set (Fin T))
    (U : Frame d T) (cap : ℝ) :
    RawGenieProtocol.Safe cap (compile (reindexPolicy e P) h) V S U ↔
      RawGenieProtocol.Safe cap (compile P h) V S U := by
  subst m'
  rfl

/-- The raw two-frame event controls the actual source observations when
only real revelations consume the fixed source column budgets. -/
theorem two_frame_source_observed {dx du S M N : ℕ}
    {Hx Hu : Memory} {C : Type} [MeasurableSpace C]
    (ρ : Measure C) [IsProbabilityMeasure ρ]
    (Lx : Rules Hx dx S) (Lu : Rules Hu du (S*M))
    (hsecond : ∀ t h,Lx.second t h=0)
    (cx : Hx → ℕ) (cu : Hu → ℕ)
    (hxrequest : ∀ t h,Lx.request t h=true → 0<cx h)
    (hxyes : ∀ t h U,Lx.request t h=true → cx (step Lx t h U)+1≤cx h)
    (hxno : ∀ t h U,Lx.request t h≠true → cx (step Lx t h U)≤cx h)
    (hurequest : ∀ t h,Lu.request t h=true → 0<cu h)
    (huyes : ∀ t h U,Lu.request t h=true → cu (step Lu t h U)+1≤cu h)
    (huno : ∀ t h U,Lu.request t h≠true → cu (step Lu t h U)≤cu h)
    (ix : C × Frame du (S*M) → Hx) (hix : Measurable ix) (hcx : ∀ p,cx (ix p)≤S)
    (iu : C × Frame dx S → Hu) (hiu : Measurable iu) (hcu : ∀ p,cu (iu p)≤S*M)
    (Rx Ru τx τu δ : ℝ) (hS : 0<S) (hM : 0<M)
    (hRx : 0<Rx) (hRu : 0<Ru) (hτx : 0<τx) (hτu : 0<τu)
    (hδ : 0<δ) (hδ1 : δ≤1)
    (hdx : sourceDimension (N+1) S Rx τx δ≤dx)
    (hdu : sourceDimension (2*N+1) (S*M) Ru τu δ≤du) :
    ∃ hx : S≤dx, ∃ hu : S*M≤du,
      (ρ.prod ((HaarFrame.frameLaw dx S hx).prod (HaarFrame.frameLaw du (S*M) hu)))
        {p | ¬SourceObserved Lx (τx^2/(4*Rx^2)) N 0 (ix (p.1,p.2.2),(⊥,∅)) p.2.1 ∨
          ¬SourceObserved Lu (τu^2/(4*Ru^2)) N 0 (iu (p.1,p.2.1),(⊥,∅)) p.2.2}≤
        ENNReal.ofReal δ := by
  let Px := oneQueryPolicy Lx N S 0
  let Pu := reindexPolicy (OrdinaryFrame.queryCount_eq N)
    (OrdinaryFrame.policy (compileRules Lu) N (S*M) 0)
  let ium : C × Frame dx S → Marked Hu := fun p => (iu p,false)
  have hium : Measurable ium := hiu.prodMk measurable_const
  obtain ⟨hx,hu,hprob⟩ := source_two_frame_projection ρ Px Pu ix hix ium hium
    Rx Ru τx τu δ hS hM hRx hRu hτx hτu hδ hδ1 hdx hdu
  refine ⟨hx,hu,(measure_mono ?_).trans hprob⟩
  intro p hp
  by_contra hn
  have hgood := not_or.mp hn
  have hxs : RawGenieProtocol.Safe (τx^2/(4*Rx^2))
      (compile (oneQueryPolicy Lx N S 0) (ix (p.1,p.2.2))) ⊥ ∅ p.2.1 := not_not.mp hgood.1
  have hus : RawGenieProtocol.Safe (τu^2/(4*Ru^2))
      (compile (OrdinaryFrame.policy (compileRules Lu) N (S*M) 0) (iu (p.1,p.2.1),false)) ⊥ ∅ p.2.2 :=
    (safe_reindexPolicy _ _ _ _ _ _ _).mp (not_not.mp hgood.2)
  rcases hp with hx_bad | hu_bad
  · exact hx_bad (oneQuery_source_observed Lx _ hsecond cx hxrequest hxyes hxno N S 0
      (ix (p.1,p.2.2),(⊥,∅)) p.2.1 (hcx _) hxs)
  · exact hu_bad (compiled_source_observed_of_credit Lu _ cu hurequest huyes huno N (S*M) 0
      (iu (p.1,p.2.1),(⊥,∅)) p.2.2 (hcu _)
      (OrdinaryFrame.safe_observed (compileRules Lu) _ N (S*M) 0 _ _ hus))

variable {dx du S M : ℕ} {St Q O Y C : Type}
  [MeasurableSpace St] [MeasurableSpace Q] [MeasurableSpace O] [MeasurableSpace Y] [MeasurableSpace C]
  (A : BorelAdaptive.Program St Q O Y)
  (reply : Frame dx S → Frame du (S*M) → Q → ℕ → Bool → O)
  (hreply : Measurable (fun z : (Frame dx S × Frame du (S*M)) × (Q × (ℕ × Bool)) =>
    reply z.1.1 z.1.2 z.2.1 z.2.2.1 z.2.2.2))
  (hS : 0<S) (hM : 0<M)
  (xquery : Q → Space dx) (hxquery : Measurable xquery)
  (uquery vquery : Q → Space du) (huquery : Measurable uquery) (hvquery : Measurable vquery)
  (xoutput : Y → Space dx) (hxoutput : Measurable xoutput)
  (uoutput : Y → Space du) (huoutput : Measurable uoutput)
  (initial : C → St) (hi : Measurable initial)
  (draws : C → ℕ → Bool) (hdraws : Measurable draws)

abbrev sourceMacroRules := macroRules (macroSchedule S M) (microSchedule (S*M)) A reply hreply hS
  xquery hxquery xoutput hxoutput
abbrev sourceMicroRules := microRules (macroSchedule S M) (microSchedule (S*M)) A reply hreply (Nat.mul_pos hS hM)
  uquery vquery huquery hvquery uoutput huoutput

def macroInitial (p : C × Frame du (S*M)) : ObserverMemory (Frame du (S*M)) St dx S :=
  (p.2,(draws p.1,(initial p.1,(0,0))))
def microInitial (p : C × Frame dx S) : ObserverMemory (Frame dx S) St du (S*M) :=
  (p.2,(draws p.1,(initial p.1,(0,0))))

include hi hdraws in
theorem macroInitial_measurable : Measurable (macroInitial (dx:=dx) (du:=du) (S:=S) (M:=M) initial draws) :=
  measurable_snd.prodMk ((hdraws.comp measurable_fst).prodMk
    ((hi.comp measurable_fst).prodMk (measurable_const.prodMk measurable_const)))
include hi hdraws in
theorem microInitial_measurable : Measurable (microInitial (dx:=dx) (du:=du) (S:=S) (M:=M) initial draws) :=
  measurable_snd.prodMk ((hdraws.comp measurable_fst).prodMk
    ((hi.comp measurable_fst).prodMk (measurable_const.prodMk measurable_const)))

include hi hdraws in
/-- Source-facing two-frame probability for the two causally implemented
views of the same arbitrary public algorithm. It includes all N calls and
the arbitrary output and requires no N≤S or N≤S*M assumption. -/
theorem actual_two_frame_observed (ρ : Measure C) [IsProbabilityMeasure ρ] (N : ℕ)
    (Rx Ru τx τu δ : ℝ) (hRx : 0<Rx) (hRu : 0<Ru) (hτx : 0<τx) (hτu : 0<τu)
    (hδ : 0<δ) (hδ1 : δ≤1)
    (hdx : sourceDimension (N+1) S Rx τx δ≤dx)
    (hdu : sourceDimension (2*N+1) (S*M) Ru τu δ≤du) :
    ∃ hx : S≤dx, ∃ hu : S*M≤du,
      (ρ.prod ((HaarFrame.frameLaw dx S hx).prod (HaarFrame.frameLaw du (S*M) hu)))
        {p | ¬SourceObserved (sourceMacroRules A reply hreply hS xquery hxquery xoutput hxoutput)
          (τx^2/(4*Rx^2)) N 0 (macroInitial initial draws (p.1,p.2.2),(⊥,∅)) p.2.1 ∨
          ¬SourceObserved (sourceMicroRules A reply hreply hS hM uquery vquery huquery hvquery uoutput huoutput)
          (τu^2/(4*Ru^2)) N 0 (microInitial initial draws (p.1,p.2.1),(⊥,∅)) p.2.2}≤ENNReal.ofReal δ := by
  apply two_frame_source_observed ρ
    (sourceMacroRules A reply hreply hS xquery hxquery xoutput hxoutput)
    (sourceMicroRules A reply hreply hS hM uquery vquery huquery hvquery uoutput huoutput)
    (fun _ _ => rfl) (credit (macroSchedule S M)) (credit (microSchedule (S*M)))
  · exact request_credit (macroSchedule S M) hS A (macroEvaluator (microSchedule (S*M)) reply) (macroEvaluator_measurable (microSchedule (S*M)) reply hreply) xquery (fun _ => 0) hxquery measurable_const xoutput hxoutput
  · exact step_credit_decrease (macroSchedule S M) hS A (macroEvaluator (microSchedule (S*M)) reply) (macroEvaluator_measurable (microSchedule (S*M)) reply hreply) xquery (fun _ => 0) hxquery measurable_const xoutput hxoutput
  · exact fun t h U _ => step_credit_nonincrease (macroSchedule S M) hS A (macroEvaluator (microSchedule (S*M)) reply) (macroEvaluator_measurable (microSchedule (S*M)) reply hreply) xquery (fun _ => 0) hxquery measurable_const xoutput hxoutput t h U
  · exact request_credit (microSchedule (S*M)) (Nat.mul_pos hS hM) A (microEvaluator (macroSchedule S M) reply) (microEvaluator_measurable (macroSchedule S M) reply hreply) uquery vquery huquery hvquery uoutput huoutput
  · exact step_credit_decrease (microSchedule (S*M)) (Nat.mul_pos hS hM) A (microEvaluator (macroSchedule S M) reply) (microEvaluator_measurable (macroSchedule S M) reply hreply) uquery vquery huquery hvquery uoutput huoutput
  · exact fun t h U _ => step_credit_nonincrease (microSchedule (S*M)) (Nat.mul_pos hS hM) A (microEvaluator (macroSchedule S M) reply) (microEvaluator_measurable (macroSchedule S M) reply hreply) uquery vquery huquery hvquery uoutput huoutput t h U
  · exact macroInitial_measurable initial hi draws hdraws
  · intro p;exact Nat.sub_le _ _
  · exact microInitial_measurable initial hi draws hdraws
  · intro p;exact Nat.sub_le _ _
  · exact hS
  · exact hM
  · exact hRx
  · exact hRu
  · exact hτx
  · exact hτu
  · exact hδ
  · exact hδ1
  · exact hdx
  · exact hdu

end Bilevel.PolishedLiteralActualObserver
