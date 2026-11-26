import RationalSparseRegret254
import FiniteInterface254

noncomputable section
open scoped BigOperators
namespace Paper254

abbrev RationalLossGradientOracle (d : ℕ) := Loss d → RationalGradientQuery d

/-- Exact rational gradients for this particular loss, at feasible rational queries. -/
def RationalLossCompatible {d : ℕ} {D : ℝ} (W : Domain d D)
    (oracle : RationalLossGradientOracle d) (f : Loss d) : Prop :=
  ∀ w, WithLp.toLp 2 (fun j => (w j : ℝ))∈W.carrier →
    HasGradientWithinAt f (WithLp.toLp 2 (fun j => (oracle f w j : ℝ)))
      W.carrier (WithLp.toLp 2 (fun j => (w j : ℝ)))

/-- A total bounded oracle with valid zero padding. Exactness for the observed
loss sequence is a separate input condition, not an assertion about all real losses. -/
structure RationalLossGradientOracleSpec {d : ℕ} {D : ℝ} (W : Domain d D) (G eta : ℝ)
    (oracle : RationalLossGradientOracle d) : Prop where
  bounded : ∀ f w, WithLp.toLp 2 (fun j => (w j : ℝ))∈W.carrier →
    ‖WithLp.toLp 2 (fun j => (oracle f w j : ℝ))‖≤G
  zero_gradient : RationalLossCompatible W oracle (fun _ => 0)

namespace RationalSparseConstruction
variable {d T K : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (C : RationalSparseConstruction d T K D G eta W)

def withQuery (query : ℕ → RationalGradientQuery d)
    (hquery : ∀ t w, WithLp.toLp 2 (fun j => (w j : ℝ))∈W.carrier →
      ‖WithLp.toLp 2 (fun j => (query t w j : ℝ))‖≤G) :
    RationalSparseConstruction d T K D G eta W := { C with query := query, query_bound := hquery }

def forLosses (oracle : RationalLossGradientOracle d) (hspec : RationalLossGradientOracleSpec W G eta oracle)
    (f : ℕ → Loss d) : RationalSparseConstruction d T K D G eta W :=
  C.withQuery (fun t => oracle (f t)) (fun t w hw => hspec.bounded (f t) w hw)

def onlineLearner (oracle : RationalLossGradientOracle d) (hspec : RationalLossGradientOracleSpec W G eta oracle) :
    OnlineLearner W T := fun t history =>
      (C.forLosses oracle hspec (extendFinite (fun _ => 0) history)).playedPoint t.val

theorem forLosses_causal (oracle : RationalLossGradientOracle d) (hspec : RationalLossGradientOracleSpec W G eta oracle)
    (f g : ℕ → Loss d) (t : ℕ) (heq : ∀ j < t, f j=g j) :
    (C.forLosses oracle hspec f).run t=(C.forLosses oracle hspec g).run t := by
  exact rationalSparseRun_causal C.oracle C.allCfg C.master_precision C.lam
    (standardRationalSchedule T K) C.initial (fun j => oracle (f j)) (fun j => oracle (g j)) t
    (fun j hj w => by simp only [heq j hj])

theorem online_predictions (oracle : RationalLossGradientOracle d)
    (hspec : RationalLossGradientOracleSpec W G eta oracle) (f : Fin T → Loss d) (t : Fin T) :
    predictions (C.onlineLearner oracle hspec) f t=
      (C.forLosses oracle hspec (extendFinite (fun _ => 0) f)).playedPoint t.val := by
  have hh := C.forLosses_causal oracle hspec (extendFinite (fun _ => 0) (past f t))
    (extendFinite (fun _ => 0) f) t.val (by
      intro j hj
      have hjT : j<T := Nat.lt_trans hj t.isLt
      simp only [extendFinite,dif_pos hj,dif_pos hjT,past])
  apply Subtype.ext
  change WithLp.toLp 2 (fun j => (rationalSparsePrediction ((C.forLosses oracle hspec
      (extendFinite (fun _ => 0) (past f t))).run t.val) j : ℝ))=_
  rw [hh]
  rfl

theorem online_regret (oracle : RationalLossGradientOracle d)
    (hspec : RationalLossGradientOracleSpec W G eta oracle) (f : Fin T → Loss d) (u : Fin T → W.carrier) :
    regret (C.onlineLearner oracle hspec) f u=
      (C.forLosses oracle hspec (extendFinite (fun _ => 0) f)).cumulativeRegret
        (extendFinite (fun _ => 0) f) (extendFinite (C.playedPoint 0) u) := by
  simp only [regret,cumulativeRegret,intervalCharge,Nat.zero_add]
  rw [←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro t ht
  rw [C.online_predictions oracle hspec f t,extendFinite_at,extendFinite_at]

theorem forLosses_derivative (oracle : RationalLossGradientOracle d)
    (hspec : RationalLossGradientOracleSpec W G eta oracle) (f : Fin T → Loss d)
    (hcompatible : ∀ t, RationalLossCompatible W oracle (f t)) (t : ℕ) (ht : t<T) :
    let A := C.forLosses oracle hspec (extendFinite (fun _ => 0) f)
    HasGradientWithinAt (extendFinite (fun _ => 0) f t)
      (WithLp.toLp 2 (fun j => (A.gradient t j : ℝ))) W.carrier (A.playedPoint t).val := by
  have hc : RationalLossCompatible W oracle (extendFinite (fun _ => 0) f t) :=
    by simpa only [extendFinite,dif_pos ht] using hcompatible ⟨t,ht⟩
  exact hc
    ((C.forLosses oracle hspec (extendFinite (fun _ => 0) f)).prediction t)
    ((C.forLosses oracle hspec (extendFinite (fun _ => 0) f)).prediction_feasible t)

end RationalSparseConstruction
end Paper254
#print axioms Paper254.RationalSparseConstruction.online_predictions
#print axioms Paper254.RationalSparseConstruction.online_regret
#print axioms Paper254.RationalSparseConstruction.forLosses_causal
