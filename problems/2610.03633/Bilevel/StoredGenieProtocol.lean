import Bilevel.RawGenieProtocol
import Bilevel.ProjectionStore

/-! An explicit finite-coordinate implementation of raw-protocol normalization. -/
noncomputable section
namespace Bilevel.RawGenieProtocol
open EuclideanGaussian ProjectionPosterior ProjectionGeometry ProjectionObservation GenieProtocol

def normalizeStored {d T : ℕ} : {m r : ℕ} → RawGenieProtocol.Protocol d T m r →
    ProjectionStore.Store d → Frame d T → GenieProtocol.Protocol d T m r
  | _, _, .halt, _, _ => .halt
  | _, _, .query q next, A, Z => by
      classical
      exact if ProjectionStore.residual d A q = 0 then
        addQuery (normalizeStored (next Z) A Z)
      else
        let w := ProjectionStore.direction d A q
        GenieProtocol.Protocol.query w (fun y =>
          normalizeStored (next (queryUpdate d T Z w y)) (ProjectionStore.insert d A q) (queryUpdate d T Z w y))
  | _, _, .reveal j next, A, Z => .reveal j (fun y =>
      normalizeStored (next (y,revealUpdate d T Z j y)) (ProjectionStore.insert d A y) (revealUpdate d T Z j y))

theorem stored_eq_normalize {d T m r : ℕ} (P : RawGenieProtocol.Protocol d T m r)
    (V : Submodule ℝ (Space d)) (Z : Frame d T) :
    normalizeStored P (ProjectionStore.ofSubspace d V) Z = normalize P V Z := by
  induction P generalizing V Z with
  | halt => rfl
  | @query m r q next ih =>
    classical
    simp only [normalizeStored,normalize,ProjectionStore.residual_subspace]
    split_ifs with hq
    · rw [ih]
    · simp only [ProjectionStore.direction_subspace,ProjectionStore.insert_subspace]
      have hs := ProjectionNormalization.span_eq d V q hq
      rw [hs]
      congr 1
      funext y
      exact ih _ _ _
  | @reveal m r j next ih =>
    change GenieProtocol.Protocol.reveal j (fun y => _) = GenieProtocol.Protocol.reveal j (fun y => _)
    congr 1
    funext y
    rw [ProjectionStore.insert_subspace]
    exact ih _ _ _

end Bilevel.RawGenieProtocol
