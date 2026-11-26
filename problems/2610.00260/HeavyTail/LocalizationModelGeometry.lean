import HeavyTail.FeasibleOracleModel
import HeavyTail.PhaseSum

/-! Public feasible warm center and the one-way extended-loss-to-radius
implication used by localization. No radius-to-error implication is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HeavyTail
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {θ : OracleParameters}

def PublicProblem.warmCenter (B : PublicProblem E θ) : B.X :=
  ⟨warmStartPoint B.prox θ.μ θ.D θ.G B.initial,
    warmStartPoint_feasible B.prox B.domain_subset θ.μ_nonneg θ.D_pos θ.G_pos
      B.initial B.initial_feasible⟩

namespace PrivateInstance
variable {B : PublicProblem E θ}

theorem warmCenter_radius (I : PrivateInstance B) (hμ : 0 < θ.μ) :
    ‖(B.warmCenter : E) - I.minimizer‖ ≤ warmStartRadius θ.μ θ.D θ.G :=
  (I.model_warm_start hμ).2.1

theorem radius_of_loss_le (I : PrivateInstance B) (hμ : 0 < θ.μ)
    {R : ℝ} (hR : 0 ≤ R) (x : B.X)
    (herr : I.loss x ≤ ENNReal.ofReal (θ.μ / 2 * R ^ 2)) :
    ‖(x : E) - I.minimizer‖ ≤ R := by
  have hx : (x : E) ∈ B.S := (I.loss_lt_top_iff x).mp
    (herr.trans_lt ENNReal.ofReal_lt_top)
  rw [I.loss_of_mem x hx] at herr
  have hbound : I.f x + B.h x - I.optimalValue ≤ θ.μ / 2 * R ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp herr
  exact radius_of_objective_error hμ hR
    (composite_strongConvexOn (I.f_convex.subset B.domain_subset B.h_convex.1) B.h_strongConvex)
    I.minimizer_domain hx I.minimizing hbound

theorem radius_bad_subset_loss_bad (I : PrivateInstance B) (hμ : 0 < θ.μ)
    {R : ℝ} (hR : 0 ≤ R) :
    {x : B.X | R < ‖(x : E) - I.minimizer‖} ⊆
      {x | ENNReal.ofReal (θ.μ / 2 * R ^ 2) < I.loss x} := by
  intro x hx
  by_contra h
  exact not_lt_of_ge (I.radius_of_loss_le hμ hR x (le_of_not_gt h)) hx

theorem radiusBad_measurable (I : PrivateInstance B) (R : ℝ) :
    MeasurableSet {x : B.X | R < ‖(x : E) - I.minimizer‖} :=
  measurableSet_lt measurable_const (measurable_subtype_coe.sub_const I.minimizer).norm

theorem lossBad_measurable (I : PrivateInstance B) (ε : ℝ≥0∞) :
    MeasurableSet {x : B.X | ε < I.loss x} :=
  measurableSet_lt measurable_const I.loss_measurable

end PrivateInstance
end HeavyTail
