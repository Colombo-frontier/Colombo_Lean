import Bilevel.PolishedLiteralObserverBlindBox

/-! End-to-end source two-frame execution certificate. Two independent
Haar groups generate exactly one macro frame and one global micro frame.
The actual original-gradient oracle and the causal virtual oracle run the
same arbitrary algorithm, with the same private state and activation
stream. All states, stopping decisions and the terminal output agree on
an event of failure probability at most delta. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.PolishedLiteralActualObserver
open EuclideanGaussian ProjectionPosterior PrimitiveGeometry SourceFrameActions PolishedProjectionDimension
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {dx du S M : ℕ} {C : Type} [MeasurableSpace C]

def haarFrames (hx : S≤dx) (hu : S*M≤du)
    (z : C × (OrthogonalHaar.Group dx × OrthogonalHaar.Group du)) :
    C × (Frame dx S × Frame du (S*M)) :=
  (z.1,(HaarFrame.frame dx S hx z.2.1,HaarFrame.frame du (S*M) hu z.2.2))

theorem haarFrames_preserving (ρ : Measure C) [IsProbabilityMeasure ρ]
    (hx : S≤dx) (hu : S*M≤du) :
    MeasurePreserving (haarFrames (C:=C) hx hu)
      (ρ.prod ((OrthogonalHaar.law dx).prod (OrthogonalHaar.law du)))
      (ρ.prod ((HaarFrame.frameLaw dx S hx).prod (HaarFrame.frameLaw du (S*M) hu))) := by
  have hpx : MeasurePreserving (HaarFrame.frame dx S hx) (OrthogonalHaar.law dx)
      (HaarFrame.frameLaw dx S hx) := ⟨HaarFrame.frame_measurable dx S hx,rfl⟩
  have hpu : MeasurePreserving (HaarFrame.frame du (S*M) hu) (OrthogonalHaar.law du)
      (HaarFrame.frameLaw du (S*M) hu) := ⟨HaarFrame.frame_measurable du (S*M) hu,rfl⟩
  exact (MeasurePreserving.id ρ).prod (hpx.prod hpu)

variable [MeasurableSpace (QuerySpace (dx:=dx) (du:=du))] [BorelSpace (QuerySpace (dx:=dx) (du:=du))]
  [MeasurableSpace (Joint (Space dx) (Space du))] [BorelSpace (Joint (Space dx) (Space du))]
  {St : Type} [MeasurableSpace St]
  (P : PolishedLiteral.Parameters (X:=Space dx) (U:=Space du))
  (A : BorelAdaptive.Program St (QuerySpace (dx:=dx) (du:=du))
    (QuerySpace (dx:=dx) (du:=du) × QuerySpace (dx:=dx) (du:=du)) (Joint (Space dx) (Space du)))
  (τ p : ℝ)

/-- Original source execution with exactly two global Haar frames. The
failure event includes both actual source observation events (with terminal
output insertions) and every coupled query-prefix state;
there is no bounded-query-norm or zero-respecting hypothesis. -/
theorem literal_source_coupling (initial : C → St) (hi : Measurable initial)
    (draws : C → ℕ → Bool) (hdraws : Measurable draws)
    (ρ : Measure C) [IsProbabilityMeasure ρ] (N : ℕ) (δ : ℝ)
    (hRx : 0<P.macroNode.radius) (hRu : 0<P.radius)
    (hb : 0<P.macroNode.width) (hβ : 0<P.β) (hτ : 0<τ) (hτβ : τ≤P.β/4)
    (hτb : τ≤P.macroNode.width) (hδsc : ∀ j,j<P.J → τ≤P.δ j)
    (hδ : 0<δ) (hδ1 : δ≤1)
    (hdx : sourceDimension (N+1) (P.macroNode.n+1) P.macroNode.radius (P.macroNode.width/4) δ≤dx)
    (hdu : sourceDimension (2*N+1) ((P.macroNode.n+1)*(P.n+1)) P.radius τ δ≤du) :
    ∃ hx : P.macroNode.n+1≤dx, ∃ hu : (P.macroNode.n+1)*(P.n+1)≤du,
      (ρ.prod ((OrthogonalHaar.law dx).prod (OrthogonalHaar.law du)))
        {z | let U := HaarFrame.frame dx (P.macroNode.n+1) hx z.2.1
          let V := HaarFrame.frame du ((P.macroNode.n+1)*(P.n+1)) hu z.2.2
          ¬SourceObserved (literalMacroRules P A τ p)
            ((P.macroNode.width/4)^2/(4*P.macroNode.radius^2)) N 0
            (macroInitial initial draws (z.1,V),(⊥,∅)) U ∨
          ¬SourceObserved (literalMicroRules P A τ p) (τ^2/(4*P.radius^2)) N 0
            (microInitial initial draws (z.1,U),(⊥,∅)) V ∨
          ∃ n,n≤N ∧ originalRun P A U (HaarFrame.frame_orthonormal _ _ hx _) V
            (HaarFrame.frame_orthonormal _ _ hu _) τ p (draws z.1) n 0 (initial z.1,0)≠
              literalRun P A τ p (draws z.1) U V n 0 (initial z.1,0)}≤ENNReal.ofReal δ := by
  obtain ⟨hx,hu,hprob⟩ := literal_two_frame_observed P A τ p initial hi draws hdraws ρ N
    P.macroNode.radius P.radius (P.macroNode.width/4) τ δ hRx hRu (by positivity) hτ hδ hδ1 hdx hdu
  let B : Set (C × (Frame dx (P.macroNode.n+1) × Frame du ((P.macroNode.n+1)*(P.n+1)))) :=
    {z | ¬SourceObserved (literalMacroRules P A τ p)
        ((P.macroNode.width/4)^2/(4*P.macroNode.radius^2)) N 0
        (macroInitial initial draws (z.1,z.2.2),(⊥,∅)) z.2.1 ∨
      ¬SourceObserved (literalMicroRules P A τ p) (τ^2/(4*P.radius^2)) N 0
        (microInitial initial draws (z.1,z.2.1),(⊥,∅)) z.2.2}
  have hmap := haarFrames_preserving ρ hx hu
  have hbound : (ρ.prod ((OrthogonalHaar.law dx).prod (OrthogonalHaar.law du)))
      (haarFrames hx hu ⁻¹' B)≤ENNReal.ofReal δ := by
    calc
      _≤((ρ.prod ((OrthogonalHaar.law dx).prod (OrthogonalHaar.law du))).map (haarFrames hx hu)) B :=
        Measure.le_map_apply hmap.measurable.aemeasurable B
      _= (ρ.prod ((HaarFrame.frameLaw dx (P.macroNode.n+1) hx).prod
          (HaarFrame.frameLaw du ((P.macroNode.n+1)*(P.n+1)) hu))) B := by rw [hmap.map_eq]
      _≤ENNReal.ofReal δ := hprob
  refine ⟨hx,hu,(measure_mono ?_).trans hbound⟩
  intro z hz
  by_contra hnot
  have hobs := not_or.mp hnot
  let U := HaarFrame.frame dx (P.macroNode.n+1) hx z.2.1
  let V := HaarFrame.frame du ((P.macroNode.n+1)*(P.n+1)) hu z.2.2
  have hU : Orthonormal ℝ U := HaarFrame.frame_orthonormal _ _ hx _
  have hV : Orthonormal ℝ V := HaarFrame.frame_orthonormal _ _ hu _
  have hinitx : macroInitial (dx:=dx) initial draws (z.1,V)=
      lift (macroSchedule (P.macroNode.n+1) (P.n+1)) V (draws z.1) (initial z.1,0) U := by
    simp [macroInitial,lift,prefixColumns,macroSchedule]
    change (0,(0:Frame dx (P.macroNode.n+1)))=(0,prefixColumns U 0)
    congr 1
  have hinitu : microInitial (du:=du) initial draws (z.1,U)=
      lift (microSchedule ((P.macroNode.n+1)*(P.n+1))) U (draws z.1) (initial z.1,0) V := by
    simp [microInitial,lift,prefixColumns,microSchedule]
    change (0,(0:Frame du ((P.macroNode.n+1)*(P.n+1))))=(0,prefixColumns V 0)
    congr 1
  have hxo : SourceObserved (literalMacroRules P A τ p)
      ((P.macroNode.width/4)^2/(4*P.macroNode.radius^2)) N 0
      (lift (macroSchedule (P.macroNode.n+1) (P.n+1)) V (draws z.1) (initial z.1,0) U,(⊥,∅)) U := by
    rw [←hinitx]
    exact not_not.mp hobs.1
  have huo : SourceObserved (literalMicroRules P A τ p) (τ^2/(4*P.radius^2)) N 0
      (lift (microSchedule ((P.macroNode.n+1)*(P.n+1))) U (draws z.1) (initial z.1,0) V,(⊥,∅)) V := by
    rw [←hinitu]
    exact not_not.mp hobs.2
  rcases hz with hx_bad | hu_bad | hz
  · exact hobs.1 hx_bad
  · exact hobs.2 hu_bad
  obtain ⟨n,hn,hneq⟩ := hz
  apply hneq
  apply originalRun_eq_virtual P A U hU V hV τ p hb hβ hτ hτβ hτb hδsc (draws z.1) n 0 (initial z.1,0)
  intro k hk
  exact source_observed_blindBox P A U hU V hV τ p (draws z.1) (initial z.1) N k
    (hk.trans_le hn) hRx hRu hb hτ hxo huo

end Bilevel.PolishedLiteralActualObserver
