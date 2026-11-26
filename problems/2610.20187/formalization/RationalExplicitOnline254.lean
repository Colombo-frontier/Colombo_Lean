import RationalExplicitConstruction254
import RationalOnlineMain254

noncomputable section
namespace Paper254

/-- Binary magnitude exponents for a deterministic numerical instance.
The scale grid is fixed and contains no comparator-dependent choices. -/
structure ExplicitRationalSparseInput (d T : ℕ) (D G eta : ℝ) (W : Domain d D) where
  dimension_pos : 0 < d
  diameter_pos : 0 < D
  gradient_pos : 0 < G
  curvature_pos : 0 < eta
  s : ℕ
  v : ℕ
  v_pos : 1≤v
  dimension_bound : (d : ℝ)≤(2 : ℝ)^v
  diameter_bound : D≤(2 : ℝ)^v
  oracle : RationalProjectionProcedure d
  oracle_spec : RationalProjectionSpec W oracle
  hi : ℚ
  hi_eq : (hi : ℝ)=D^2
  hi_bound : (hi : ℝ)≤(2 : ℝ)^v
  scale_inverse_bound : ∀ k : Fin (scaleCount T+1),
    (rationalCappedVariance hi k.val : ℝ)⁻¹≤(2 : ℝ)^v
  gap_inverse_bound : ∀ k : Fin (scaleCount T+1),
    ((hi : ℝ)-(rationalCappedVariance hi k.val : ℝ))⁻¹≤(2 : ℝ)^v
  lam : ℚ
  lam_eq : 2*(lam : ℝ)=curvature D G eta
  gradient_bound : G≤(2 : ℝ)^v
  lam_bound : (lam : ℝ)≤(2 : ℝ)^v
  live_bound : (standardLiveCap T (scaleCount T) : ℝ)≤(2 : ℝ)^v
  initial_mean : Fin d → ℚ
  initial_feasible : WithLp.toLp 2 (fun j => (initial_mean j : ℝ))∈W.carrier

namespace ExplicitRationalSparseInput
variable {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (I : ExplicitRationalSparseInput d T D G eta W)

def lo (k : Fin (scaleCount T+1)) : ℚ := rationalCappedVariance I.hi k.val
theorem lo_pos (k : Fin (scaleCount T+1)) : 0 < (I.lo k : ℝ) :=
  (rationalCappedVariance_range D I.diameter_pos I.hi I.hi_eq k.val).1
theorem lo_gap (k : Fin (scaleCount T+1)) : (I.lo k : ℝ)<(I.hi : ℝ) :=
  (rationalCappedVariance_range D I.diameter_pos I.hi I.hi_eq k.val).2
theorem lo_bound (k : Fin (scaleCount T+1)) : (I.lo k : ℝ)≤(2 : ℝ)^I.v :=
  (I.lo_gap k).le.trans I.hi_bound
include I in
theorem zero_query_bound : ∀ t : ℕ, ∀ w : Fin d → ℚ,
    WithLp.toLp 2 (fun j => (w j : ℝ))∈W.carrier →
      ‖WithLp.toLp 2 (fun j : Fin d => ((0 : ℚ) : ℝ))‖≤G := by
  intro t w hw
  have hz : WithLp.toLp 2 (fun j : Fin d => ((0 : ℚ) : ℝ))=(0 : Space d) := by ext j; simp
  rw [hz,norm_zero]
  exact I.gradient_pos.le

def construction : RationalSparseConstruction d T (scaleCount T) D G eta W :=
  explicitRationalSparseConstruction I.dimension_pos W I.diameter_pos I.gradient_pos I.curvature_pos
    I.s I.v (I.s+I.v+3) I.v_pos I.dimension_bound I.diameter_bound I.oracle I.oracle_spec
    I.hi I.hi_eq I.hi_bound I.lo I.lo_pos I.lo_gap I.lo_bound I.scale_inverse_bound I.gap_inverse_bound
    I.lam I.lam_eq I.gradient_bound I.lam_bound I.initial_mean I.initial_feasible
    (fun _ _ _ => 0) I.zero_query_bound

theorem construction_error (k : Fin (scaleCount T+1)) :
    I.construction.localError k≤((2 : ℝ)^I.s)⁻¹ :=
  explicitRationalSparseConstruction_error I.dimension_pos W I.diameter_pos I.gradient_pos I.curvature_pos
    I.s I.v (I.s+I.v+3) I.v_pos I.dimension_bound I.diameter_bound I.oracle I.oracle_spec
    I.hi I.hi_eq I.hi_bound I.lo I.lo_pos I.lo_gap I.lo_bound I.scale_inverse_bound I.gap_inverse_bound
    I.lam I.lam_eq I.gradient_bound I.lam_bound I.initial_mean I.initial_feasible
    (fun _ _ _ => 0) I.zero_query_bound k

theorem construction_master_error : I.construction.masterError≤((2 : ℝ)^I.s)⁻¹ ∧
    I.construction.masterError≤1 :=
  explicit_standardMasterPrecision T (scaleCount T) I.s I.v I.live_bound

theorem construction_tuning (delta : ℝ)
    (hbudget : ((2 : ℝ)^I.s)⁻¹≤(I.lam : ℝ)*delta/(2*T)) :
    RationalSparseTuning I.construction delta := by
  exact ⟨fun _ => rfl,I.construction_master_error.2,
    fun k => (I.construction_error k).trans hbudget,I.construction_master_error.1.trans hbudget⟩

def learner (oracle : RationalLossGradientOracle d)
    (hspec : RationalLossGradientOracleSpec W G eta oracle) : OnlineLearner W T :=
  I.construction.onlineLearner oracle hspec

/-- Explicit history and master precisions give the same clipped regret
bound for the causal learner.  There is no existential precision search. -/
theorem regret_clipped (hT : 0 < T) (oracle : RationalLossGradientOracle d)
    (hspec : RationalLossGradientOracleSpec W G eta oracle) (delta : ℝ) (hdelta : 0 < delta)
    (hbudget : ((2 : ℝ)^I.s)⁻¹≤(I.lam : ℝ)*delta/(2*T))
    (f : Fin T → Loss d) (hf : ∀ t, AdmissibleLoss W G eta (f t))
    (hcompatible : ∀ t, RationalLossCompatible W oracle (f t)) (u : Fin T → W.carrier)
    (tau : ℝ) (hlo : D/T≤tau) (hhi : tau≤D) :
    regret (I.learner oracle hspec) f u≤2048*((d+1 : ℝ)*logFactor T^2/curvature D G eta+
      Real.sqrt (d+1 : ℝ)*logFactor T^2/(curvature D G eta*tau)*pathLength u+
        curvature D G eta*G^2*T*tau^2)+delta :=
  I.construction.online_clipped hT oracle hspec delta hdelta (I.construction_tuning delta hbudget)
    f hf hcompatible u tau hlo hhi

theorem regret_curved (hT : 0 < T) (oracle : RationalLossGradientOracle d)
    (hspec : RationalLossGradientOracleSpec W G eta oracle) (delta : ℝ) (hdelta : 0 < delta)
    (hbudget : ((2 : ℝ)^I.s)⁻¹≤(I.lam : ℝ)*delta/(2*T))
    (f : Fin T → Loss d) (hf : ∀ t, AdmissibleLoss W G eta (f t))
    (hcompatible : ∀ t, RationalLossCompatible W oracle (f t)) (u : Fin T → W.carrier)
    (hsmall : pathLength u≤curvature D G eta^2*G^2*T*D^3/(Real.sqrt (d+1 : ℝ)*logFactor T^2)) :
    regret (I.learner oracle hspec) f u≤6144*((d+1 : ℝ)*logFactor T^2/curvature D G eta+
      explicitCurvedRate (curvature D G eta) G d T (pathLength u))+delta :=
  clipped_numeric_explicit D G eta (regret (I.learner oracle hspec) f u) (pathLength u) delta d T
    I.diameter_pos I.gradient_pos I.curvature_pos I.dimension_pos hT (pathLength_nonneg u) hsmall
    (I.regret_clipped hT oracle hspec delta hdelta hbudget f hf hcompatible u)

end ExplicitRationalSparseInput
end Paper254
#print axioms Paper254.ExplicitRationalSparseInput.regret_clipped
#print axioms Paper254.ExplicitRationalSparseInput.regret_curved
