import SecondOrder.TrackedPoints
import SecondOrder.EpochAnchorCost

open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

/-- The three local routine requests. These are endpoint requests; the
fresh-sample implementation and the eigensolver must supply their replies. -/
inductive TrackingRequest (d : ℕ)
  | anchor (x : Point d)
  | chord (x y : Point d)
  | curvature (x : Point d)

def trackedCurvatureNeeded {d L : ℕ} (τ : ℝ) (z : TrackedState d L) : Prop :=
  z.physical.running = true ∧ ‖trackerRead z.memory‖ ≤ 4*τ

def trackedChordRequests {d L : ℕ} (Lip s τ : ℝ) (z : TrackedState d L)
    (r : CurvatureReply d) (b : Bool) : List (TrackingRequest d) :=
  let p := trackedNext Lip s τ z r b
  if p.running then
    (createdNodes L z.memory.length).toList.map (fun i =>
      .chord (trackerPushPoints z.memory p.point (nodeLeft i)) (trackerPushPoints z.memory p.point (nodeRight i)))
  else []

def trackedRefreshRequests {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (z : TrackedState d L)
    (r : CurvatureReply d) (b : Bool) : List (TrackingRequest d) :=
  if (trackedNext Lip s τ z r b).running = true ∧ trackedRestart q τ z r
    then [.anchor (trackedNext Lip s τ z r b).point] else []

/-- The causal order is curvature first (when required), then every newly
created old-epoch chord, then the optional fresh anchor. An empty post-move
schedule follows a certificate or an already stopped state. -/
def trackedStepRequests {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (z : TrackedState d L)
    (r : CurvatureReply d) (b : Bool) : List (TrackingRequest d) :=
  (if trackedCurvatureNeeded τ z then [.curvature z.physical.point] else []) ++
    trackedChordRequests Lip s τ z r b ++ trackedRefreshRequests q Lip s τ z r b

def trackedRequestTrace {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (source : TrackingSource d L) :
    (t : ℕ) → (Fin t → Bool) → List (TrackingRequest d)
  | 0, _ => [.anchor 0]
  | t+1, w =>
      let z := trackedRun q Lip s τ source t (Fin.init w)
      let r := source.curvature t (Fin.init w) z
      trackedRequestTrace q Lip s τ source t (Fin.init w) ++ trackedStepRequests q Lip s τ z r (w (Fin.last t))

/-- Any additive charge on local requests can be read from the trace. In
particular, an indicator counts routine calls, while batch size counts
oracle queries. No query-cost conclusion for an eigensolver is assumed. -/
def requestCharge {d : ℕ} (c : TrackingRequest d → ℕ) (trace : List (TrackingRequest d)) : ℕ :=
  (trace.map c).sum

theorem requestCharge_append {d : ℕ} (c : TrackingRequest d → ℕ) (a b : List (TrackingRequest d)) :
    requestCharge c (a++b) = requestCharge c a+requestCharge c b := by
  simp [requestCharge]

def isAnchorRequest {d : ℕ} : TrackingRequest d → ℕ
  | .anchor _ => 1
  | _ => 0

def isChordRequest {d : ℕ} : TrackingRequest d → ℕ
  | .chord _ _ => 1
  | _ => 0

def isCurvatureRequest {d : ℕ} : TrackingRequest d → ℕ
  | .curvature _ => 1
  | _ => 0

def requestOracleCost {d : ℕ} (P : Parameters) (τ ρ δ : ℝ) (eigenCost : Point d → ℕ) : TrackingRequest d → ℕ
  | .anchor _ => localQueryCount (P.gradientNoise^2) (τ/4) δ
  | .chord x y => localQueryCount (chordVariance P x y) ρ δ
  | .curvature x => eigenCost x

def requestChordCost {d : ℕ} (P : Parameters) (ρ δ : ℝ) : TrackingRequest d → ℕ
  | .chord x y => localQueryCount (chordVariance P x y) ρ δ
  | _ => 0

theorem trackedChordRequests_length {d L : ℕ} (Lip s τ : ℝ) (z : TrackedState d L)
    (r : CurvatureReply d) (b : Bool) :
    (trackedChordRequests Lip s τ z r b).length =
      if (trackedNext Lip s τ z r b).running then (createdNodes L z.memory.length).card else 0 := by
  dsimp only [trackedChordRequests]
  split_ifs <;> simp

theorem trackedStepRequests_curvature {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (z : TrackedState d L)
    (r : CurvatureReply d) (b : Bool) :
    requestCharge isCurvatureRequest (trackedStepRequests q Lip s τ z r b) =
      if trackedCurvatureNeeded τ z then 1 else 0 := by
  simp only [trackedStepRequests,requestCharge_append]
  dsimp only [trackedChordRequests,trackedRefreshRequests]
  split_ifs <;> simp [requestCharge,isCurvatureRequest,List.map_map]

theorem trackedStepRequests_anchor {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (z : TrackedState d L)
    (r : CurvatureReply d) (b : Bool) :
    requestCharge isAnchorRequest (trackedStepRequests q Lip s τ z r b) =
      if (trackedNext Lip s τ z r b).running = true ∧ trackedRestart q τ z r then 1 else 0 := by
  simp only [trackedStepRequests,requestCharge_append]
  dsimp only [trackedChordRequests,trackedRefreshRequests]
  split_ifs <;> simp [requestCharge,isAnchorRequest,List.map_map]

theorem trackedStepRequests_chords {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (z : TrackedState d L)
    (r : CurvatureReply d) (b : Bool) :
    requestCharge isChordRequest (trackedStepRequests q Lip s τ z r b) =
      if (trackedNext Lip s τ z r b).running then (createdNodes L z.memory.length).card else 0 := by
  simp only [trackedStepRequests,requestCharge_append]
  dsimp only [trackedChordRequests,trackedRefreshRequests]
  split_ifs <;> simp [requestCharge,isChordRequest,List.map_map]

end
end SecondOrder
