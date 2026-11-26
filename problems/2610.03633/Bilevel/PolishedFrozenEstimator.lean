import Bilevel.CachedEstimatorAccuracy

/-! Literal anchor estimator: the already computed untilted point is reused.
Only one tilted solve and the two fresh lower-gradient means are performed. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.PolishedFrozenProcedure
open Stateful CachedEstimatorProcedure ConditionalConfidence
variable {X Y History : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace History] {σf σg : ℝ}
  (O : HistorySFO (Query:=X × Y) (History:=History) (X:=X) (Y:=Y) σf σg)

def reusePair (μ Lg t D r : ℝ) (q : ℕ) [NeZero q] :
    Procedure (Input X Y × Y) History (Y × Y) :=
  ((tilted O μ Lg t D r q).reparam Prod.fst measurable_fst).map
    (fun z => (z.1.2,z.2)) (by fun_prop)

def reuseFirst (δ : ℝ) (q : ℕ) [NeZero q] :
    Procedure ((Input X Y × Y) × (Y × Y)) History ((Y × Y) × X) :=
  (firstGradient O δ q).reparam (fun z => (z.1.1,z.2)) (by fun_prop)

def reuseLast (δ : ℝ) (q : ℕ) [NeZero q] :
    Procedure ((Input X Y × Y) × ((Y × Y) × X)) History (Transcript X Y) :=
  (lastGradient O δ q).reparam (fun z => (z.1.1,z.2)) (by fun_prop)

def reuseTranscript (μ Lg t D r δ : ℝ) (q : ℕ) [NeZero q] :
    Procedure (Input X Y × Y) History (Transcript X Y) :=
  ((reusePair O μ Lg t D r q).bind (reuseFirst O δ q)).bind (reuseLast O δ q)

def reuseEstimator (μ Lg t D r δ : ℝ) (q : ℕ) [NeZero q] :
    Procedure (Input X Y × Y) History X :=
  (reuseTranscript O μ Lg t D r δ q).map
    (fun z => estimate t z.1.1 z.2) (by unfold estimate;fun_prop)

theorem reusePair_failure (μ Lg t D r : ℝ) (q : ℕ) [NeZero q]
    (p : Input X Y × Y) (ys yt : Y) (hy : ‖p.2-ys‖≤r)
    (hT : ∀ h,((tilted O μ Lg t D r q).law (p.1,h)).real
      {z | r<‖z.1-yt‖}≤Real.exp (-(q:ℝ)/8)) (h : History) :
    ((reusePair O μ Lg t D r q).law (p,h)).real
      {z | z.1∈solveBad ys yt r}≤Real.exp (-(q:ℝ)/8) := by
  have hh := Procedure.map_failure_union_bound
    ((tilted O μ Lg t D r q).reparam Prod.fst measurable_fst)
    (fun z => (z.1.2,z.2)) (by fun_prop) p h (solveBad ys yt r) (solveBad_measurable ys yt r)
    {a | r<‖a-yt‖} (measurableSet_lt measurable_const (measurable_id.sub_const yt).norm)
    False (fun a ha => by
      right
      rcases ha with h0|ht
      · exact False.elim ((not_lt_of_ge hy) h0)
      · exact ht) (hT h)
  simpa only [ite_false,zero_add,reusePair] using hh

theorem reuseTranscript_failure (μ Lg t D r δ : ℝ) (hδ : 0<δ) (q : ℕ) [NeZero q]
    (p : Input X Y × Y) (ys yt : Y) (hy : ‖p.2-ys‖≤r)
    (hT : ∀ h,((tilted O μ Lg t D r q).law (p.1,h)).real
      {z | r<‖z.1-yt‖}≤Real.exp (-(q:ℝ)/8)) (h : History) :
    ((reuseTranscript O μ Lg t D r δ q).law (p,h)).real
      {z | z.1∈badEvent O p.1.1 ys yt r δ}≤3*Real.exp (-(q:ℝ)/8) := by
  have h1 := Procedure.bind_failure_bound (reusePair O μ Lg t D r q) (reuseFirst O δ q)
    p h _ (solveBad_measurable ys yt r) _ (firstBad_measurable O p.1.1 ys yt r δ)
    (reusePair_failure O μ Lg t D r q p ys yt hy hT h)
    (fun v h' => firstGradient_failure O δ hδ q p.1 v ys yt r h')
  have h2 := Procedure.bind_failure_bound
    ((reusePair O μ Lg t D r q).bind (reuseFirst O δ q)) (reuseLast O δ q)
    p h _ (firstBad_measurable O p.1.1 ys yt r δ) _ (badEvent_measurable O p.1.1 ys yt r δ)
    h1 (fun v h' => lastGradient_failure O δ hδ q p.1 v ys yt r h')
  exact h2.trans (by ring_nf;rfl)

variable {μ Lf Lg Cf ρ : ℝ}
  (P : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ)
  [FiniteDimensional ℝ Y] [Nontrivial Y]

theorem reuseEstimator_confidence
    (hgy : ∀ x y,O.lower.truth_y (x,y)=P.gy x y)
    (hgx : ∀ x y,O.lower.truth_x (x,y)=P.gx x y)
    (t D r δ : ℝ) (ht : 0<t) (hr : 0<r) (hδ : 0<δ) (q : ℕ) [NeZero q]
    (p : Input X Y × Y) {eC e : ℝ}
    (hy : ‖p.2-P.canonicalResponse.y p.1.1‖≤r)
    (hT : ‖p.1.2.2.2-P.tiltedResponse p.1.1 t p.1.2.2.1‖≤D)
    (hcache : ‖p.1.2.1-P.fx p.1.1 (P.canonicalResponse.y p.1.1)‖+
      Lg/μ*‖p.1.2.2.1-P.fy p.1.1 (P.canonicalResponse.y p.1.1)‖≤eC)
    (hbudget : eC+t⁻¹*(2*Lg*r+2*δ)+((1+Lg/μ)*ρ*Cf^2/(2*μ^2))*t≤e)
    (h : History) :
    ((reuseEstimator O μ Lg t D r δ q).law (p,h)).real
      {z | e<‖z.1-gradient (P.hyperobjective P.canonicalResponse) p.1.1‖}≤3*Real.exp (-(q:ℝ)/8) := by
  have htarg (h' : History) := tilted_confidence O P hgy t D r hr q p.1 hT h'
  have hh := Procedure.map_failure_union_bound (reuseTranscript O μ Lg t D r δ q)
    (fun z => estimate t z.1.1 z.2) (by unfold estimate;fun_prop) p h
    {v | e<‖v-gradient (P.hyperobjective P.canonicalResponse) p.1.1‖}
    (measurableSet_lt measurable_const (measurable_id.sub_const _).norm)
    (badEvent O p.1.1 (P.canonicalResponse.y p.1.1) (P.tiltedResponse p.1.1 t p.1.2.2.1) r δ)
    (badEvent_measurable O p.1.1 _ _ r δ) False (fun z hz => by
      right
      by_contra hgood
      exact (not_lt_of_ge (estimate_good_bound O P hgx p.1 z ht hcache hgood hbudget)) hz)
    (reuseTranscript_failure O μ Lg t D r δ hδ q p _ _ hy htarg h)
  simpa only [reuseEstimator,ite_false,zero_add] using hh

end Bilevel.PolishedFrozenProcedure
