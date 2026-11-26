import Bilevel.ModelBridge
import Bilevel.ResponseExistence
import Bilevel.Hypergradient
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Lower response stability and implicit differentiation

Response Lipschitzness is proved from primitive smoothness and strong
convexity. A joint derivative certificate for the lower gradient then suffices
to derive the response derivative by a Taylor remainder argument. No implicit
function theorem or differentiability of the response is assumed.

Deriving that joint derivative certificate, including equality of mixed
partial derivatives, from `Primitive` remains a separate task.
-/

noncomputable section
open scoped RealInnerProductSpace Topology
open Filter Asymptotics

namespace Bilevel.Model.Primitive

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
variable {μ Lf Lg Cf ρ : ℝ}
variable (P : Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)

theorem response_lipschitz (r : P.Response) :
    LipschitzWith ⟨Lg / μ, div_nonneg P.Lg_nonneg P.μ_pos.le⟩ r.y := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  simpa only [dist_eq_norm, NNReal.coe_mk] using P.response_distance_bound r x z

/-- Implicit differentiation derived from the joint Taylor expansion and
the already-proved response Lipschitz bound. -/
theorem response_hasFDerivAt (r : P.Response) (x : X)
    (A : X →L[ℝ] Y) (J : Y →L[ℝ] Y)
    (hleft : ∀ v, J (P.gyy x (r.y x) v) = v)
    (hG : HasFDerivAt (fun p : X × Y => P.gy p.1 p.2)
      (A.comp (ContinuousLinearMap.fst ℝ X Y) +
        (P.gyy x (r.y x)).comp (ContinuousLinearMap.snd ℝ X Y)) (x, r.y x)) :
    HasFDerivAt r.y (-(J.comp A)) x := by
  have hgraph : ContinuousAt (fun z => (z, r.y z)) x :=
    continuousAt_id.prodMk (P.response_continuous r).continuousAt
  have he := hG.isLittleO.comp_tendsto hgraph
  have hb : (fun z => (z, r.y z) - (x, r.y x)) =O[𝓝 x] (fun z => z - x) := by
    apply IsBigO.of_bound (max 1 (Lg / μ))
    apply Filter.Eventually.of_forall
    intro z
    rw [Prod.norm_def]
    apply max_le
    · exact le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _)
    · exact (P.response_distance_bound r z x).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  have he' := he.trans_isBigO hb
  have hJ := (J.isBigO_comp _ _).trans_isLittleO he'
  apply HasFDerivAtFilter.of_isLittleO
  apply hJ.neg_left.congr_left
  intro z
  have hz := P.minimizer_stationary z (r.y z) (r.minimizes z)
  have hx := P.minimizer_stationary x (r.y x) (r.minimizes x)
  change -(J (P.gy z (r.y z) - P.gy x (r.y x) -
    (A (z - x) + P.gyy x (r.y x) (r.y z - r.y x)))) =
      r.y z - r.y x - (-J (A (z - x)))
  rw [hz, hx, sub_self, zero_sub, map_neg, neg_neg, map_add, hleft]
  abel

end Bilevel.Model.Primitive
