import RationalAnytime254
import RationalRunBitCost254

noncomputable section
open scoped BigOperators
namespace Paper254

def rationalEpochConstruction {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
    (I : (H : ℕ) → ExplicitRationalSparseInput d H D G eta W)
    (oracle : RationalLossGradientOracle d) (hspec : RationalLossGradientOracleSpec W G eta oracle)
    (f : Fin T → Loss d) (j : Fin (epochCount T)) :
    RationalSparseConstruction d (2^j.val) (scaleCount (2^j.val)) D G eta W :=
  (I (2^j.val)).construction.forLosses oracle hspec
    (extendFinite (fun _ => 0) (paddedLoss (H := 2^j.val) (epochLoss f j)))

theorem rational_epoch_prediction {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
    (I : (H : ℕ) → ExplicitRationalSparseInput d H D G eta W)
    (oracle : RationalLossGradientOracle d) (hspec : RationalLossGradientOracleSpec W G eta oracle)
    (f : Fin T → Loss d) (j : Fin (epochCount T)) (k : Fin (epochLength T j.val)) :
    predictions (anytimeRestriction (doublingLearner (rationalDoublingFamily I 1 0 0 oracle hspec)) T)
      f (epochRound ⟨j,k⟩)=(rationalEpochConstruction I oracle hspec f j).playedPoint k.val := by
  rw [doubling_epoch_prediction]
  unfold rationalDoublingFamily
  rw [(I (2^j.val)).construction.materializedLearner_eq]
  rw [←prefix_predictions ((I (2^j.val)).construction.onlineLearner oracle hspec)
    (min_le_left _ _) (epochLoss f j) k]
  exact (I (2^j.val)).construction.online_predictions oracle hspec
    (paddedLoss (epochLoss f j)) ⟨k.val,lt_of_lt_of_le k.isLt (min_le_left _ _)⟩

/-- The maximum is over logarithmically many epochs, not over all rounds.
Each entry is the explicit polynomial bound supplied by that epoch's input
encoding certificate. -/
def rationalAnytimePerRound {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
    {I : (H : ℕ) → ExplicitRationalSparseInput d H D G eta W}
    {oracle : RationalLossGradientOracle d} {hspec : RationalLossGradientOracleSpec W G eta oracle}
    {f : Fin T → Loss d}
    (E : (j : Fin (epochCount T)) → RationalRunEncodingSetup (rationalEpochConstruction I oracle hspec f j))
    (model : PolynomialArithmeticCharge) (projectionCost gradientCost : ℕ) : ℕ :=
  Finset.univ.sup (fun j => (E j).bitPerRound model projectionCost gradientCost)

/-- This is the charge of the actual materialized transitions executed in
each epoch; unused padding rounds are not charged. -/
def rationalAnytimeBitCharge {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
    {I : (H : ℕ) → ExplicitRationalSparseInput d H D G eta W}
    {oracle : RationalLossGradientOracle d} {hspec : RationalLossGradientOracleSpec W G eta oracle}
    {f : Fin T → Loss d}
    (E : (j : Fin (epochCount T)) → RationalRunEncodingSetup (rationalEpochConstruction I oracle hspec f j))
    (model : PolynomialArithmeticCharge) (projectionCost gradientCost : ℕ) : ℕ :=
  ∑ j : Fin (epochCount T),∑ k : Fin (epochLength T j.val),
    (E j).bitRoundCharge model projectionCost gradientCost k.val

theorem rational_anytime_bit_charge {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
    {I : (H : ℕ) → ExplicitRationalSparseInput d H D G eta W}
    {oracle : RationalLossGradientOracle d} {hspec : RationalLossGradientOracleSpec W G eta oracle}
    {f : Fin T → Loss d}
    (E : (j : Fin (epochCount T)) → RationalRunEncodingSetup (rationalEpochConstruction I oracle hspec f j))
    (model : PolynomialArithmeticCharge) (projectionCost gradientCost : ℕ) :
    rationalAnytimeBitCharge E model projectionCost gradientCost≤
      T*rationalAnytimePerRound E model projectionCost gradientCost := by
  have hcount : (∑ j : Fin (epochCount T),epochLength T j.val)=T := by
    have hh := sum_epochs (T := T) (fun _ => (1 : ℝ))
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hh
    exact_mod_cast hh
  unfold rationalAnytimeBitCharge
  calc
    _ ≤ ∑ j : Fin (epochCount T),∑ _k : Fin (epochLength T j.val),
        rationalAnytimePerRound E model projectionCost gradientCost := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      exact ((E j).bit_round_charge_le model projectionCost gradientCost k.val).trans
        (Finset.le_sup (f := fun j => (E j).bitPerRound model projectionCost gradientCost)
          (Finset.mem_univ j))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_id,←Finset.sum_mul,hcount]

theorem rational_anytime_gradient_queries (T : ℕ) :
    (∑ j : Fin (epochCount T),∑ _k : Fin (epochLength T j.val),(1 : ℕ))=T := by
  have hh := sum_epochs (T := T) (fun _ => (1 : ℝ))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hh ⊢
  exact_mod_cast hh

end Paper254
#print axioms Paper254.rational_epoch_prediction
#print axioms Paper254.rational_anytime_bit_charge
#print axioms Paper254.rational_anytime_gradient_queries
