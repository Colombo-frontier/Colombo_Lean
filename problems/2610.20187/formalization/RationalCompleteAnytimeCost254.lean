import RationalCompleteCost254

noncomputable section
open scoped BigOperators
namespace Paper254

/-- Actual dyadic routing arithmetic; the epoch's materialized state is
retained, so routing does not replay its previous gradient responses. -/
def countedDoublingRoute (t : ℕ) : (ℕ×ℕ×ℕ×ℕ)×ℕ :=
  let j:=countedLogTwo (t+1)
  let H:=countedNatPowTwo j.1
  let start:=H.1-1
  ((j.1,H.1,start,t-start),j.2+H.2+5)

theorem countedDoublingRoute_program (t : ℕ) :
    (countedDoublingRoute t).1=(doublingEpoch t,doublingHorizon t,doublingStart t,t-doublingStart t) := by
  simp [countedDoublingRoute,countedLogTwo_spec,countedNatPowTwo_spec,
    doublingEpoch,doublingHorizon,doublingStart]

theorem countedDoublingRoute_cost (t : ℕ) :
    (countedDoublingRoute t).2=4*Nat.log 2 (t+1)+6 := by
  simp only [countedDoublingRoute,countedLogTwo_spec,countedNatPowTwo_spec]
  omega

/-- The router selects exactly the epoch and local time used by the
regret decomposition, including a final partial epoch. -/
theorem countedDoublingRoute_epoch {T : ℕ} (e : EpochRound T) :
    (countedDoublingRoute (epochRound e).val).1=(e.1.val,2^e.1.val,2^e.1.val-1,e.2.val) := by
  rw [countedDoublingRoute_program]
  have hj:=epochRound_log e
  simp only [doublingStart,doublingHorizon,hj]
  simp [epochRound]

theorem countedDoublingRoute_operand_bits (T t : ℕ) (ht : t<T) :
    (t+1).size≤metadataWordBits T 0 ∧
    (doublingEpoch t).size≤metadataWordBits T 0 ∧
    (doublingHorizon t).size≤metadataWordBits T 0 ∧
    (doublingStart t).size≤metadataWordBits T 0 ∧
    (t-doublingStart t).size≤metadataWordBits T 0 := by
  have hb:=metadataWordBound_basic T 0
  have hp:=metadata_power_prefix_words T 0 (t+1) (Nat.log 2 (t+1)) (Nat.log 2 (t+1)) (by omega) (by omega) le_rfl
  have hs: doublingStart t≤t := (doubling_bounds t).2.1
  exact ⟨metadata_size_le T 0 (t+1) (by omega),hp.1,hp.2.1,
    metadata_size_le T 0 (doublingStart t) (by omega),
    metadata_size_le T 0 (t-doublingStart t) (by omega)⟩
def doublingRouteCharge (T : ℕ) (integerModel : PolynomialArithmeticCharge) :=
  ∑ t : Fin T,(countedDoublingRoute t.val).2*integerModel.cost (metadataWordBits T 0)

def doublingRouteBound (T : ℕ) (integerModel : PolynomialArithmeticCharge) :=
  T*((4*Nat.log 2 (T+1)+6)*integerModel.coefficient*(metadataWordBits T 0+1)^integerModel.degree)

theorem doubling_route_charge_le (T : ℕ) (integerModel : PolynomialArithmeticCharge) :
    doublingRouteCharge T integerModel≤doublingRouteBound T integerModel := by
  unfold doublingRouteCharge doublingRouteBound
  calc
    _≤∑ _t : Fin T,((4*Nat.log 2 (T+1)+6)*integerModel.coefficient*
        (metadataWordBits T 0+1)^integerModel.degree) := by
      apply Finset.sum_le_sum
      intro t _
      have hl : Nat.log 2 (t.val+1)≤Nat.log 2 (T+1) := Nat.log_mono_right (by omega)
      rw [countedDoublingRoute_cost]
      have hc : 4*Nat.log 2 (t.val+1)+6≤4*Nat.log 2 (T+1)+6 := by omega
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul hc (integerModel.bound (metadataWordBits T 0))
    _=_ := by simp

section Anytime
variable {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
variable {I : (H : ℕ)→ExplicitRationalSparseInput d H D G eta W}
variable {oracle : RationalLossGradientOracle d} {hspec : RationalLossGradientOracleSpec W G eta oracle}
variable {f : Fin T→Loss d}
variable (E : (j : Fin (epochCount T))→RationalRunEncodingSetup (rationalEpochConstruction I oracle hspec f j))

def completeAnytimeCharge (b : ℕ) (rationalModel integerModel : PolynomialArithmeticCharge)
    (projectionCost gradientCost : ℕ) := doublingRouteCharge T integerModel+
  ∑ j : Fin (epochCount T),completeImplementationCharge (I (2^j.val)) (E j) b (epochLength T j.val)
    rationalModel integerModel projectionCost gradientCost

def completeAnytimeSetupBound (b : ℕ) (rationalModel integerModel : PolynomialArithmeticCharge) :=
  Finset.univ.sup (fun j : Fin (epochCount T)=>(I (2^j.val)).preparationBound b rationalModel integerModel)

def completeAnytimePerRound (rationalModel integerModel : PolynomialArithmeticCharge)
    (projectionCost gradientCost : ℕ) :=
  Finset.univ.sup (fun j : Fin (epochCount T)=>(E j).completePerRound rationalModel integerModel projectionCost gradientCost)

theorem complete_anytime_charge (b : ℕ) (rationalModel integerModel : PolynomialArithmeticCharge)
    (projectionCost gradientCost : ℕ) :
    completeAnytimeCharge E b rationalModel integerModel projectionCost gradientCost≤
      doublingRouteBound T integerModel+
      epochCount T*completeAnytimeSetupBound (T:=T) (I:=I) b rationalModel integerModel+
      T*completeAnytimePerRound E rationalModel integerModel projectionCost gradientCost := by
  have hcount : (∑ j : Fin (epochCount T),epochLength T j.val)=T := by
    have hh := sum_epochs (T := T) (fun _ => (1 : ℝ))
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hh
    exact_mod_cast hh
  have hsum : (∑ j : Fin (epochCount T),completeImplementationCharge (I (2^j.val)) (E j) b
      (epochLength T j.val) rationalModel integerModel projectionCost gradientCost)≤
      epochCount T*completeAnytimeSetupBound (T:=T) (I:=I) b rationalModel integerModel+
      T*completeAnytimePerRound E rationalModel integerModel projectionCost gradientCost := by
    calc
      _≤∑ j : Fin (epochCount T),
          (completeAnytimeSetupBound (T:=T) (I:=I) b rationalModel integerModel+
          epochLength T j.val*completeAnytimePerRound E rationalModel integerModel projectionCost gradientCost) := by
        apply Finset.sum_le_sum
        intro j _
        apply (complete_implementation_charge (I (2^j.val)) (E j) b (epochLength T j.val)
          rationalModel integerModel projectionCost gradientCost).trans
        apply Nat.add_le_add
        · exact Finset.le_sup (f:=fun j : Fin (epochCount T)=>(I (2^j.val)).preparationBound b rationalModel integerModel)
            (Finset.mem_univ j)
        · apply Nat.mul_le_mul_left
          exact Finset.le_sup (f:=fun j : Fin (epochCount T)=>(E j).completePerRound rationalModel integerModel projectionCost gradientCost)
            (Finset.mem_univ j)
      _=_ := by simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
          Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,←Finset.sum_mul,hcount]
  simpa only [completeAnytimeCharge,Nat.add_assoc] using Nat.add_le_add (doubling_route_charge_le T integerModel) hsum

end Anytime
end Paper254
#print axioms Paper254.countedDoublingRoute_program
#print axioms Paper254.complete_anytime_charge
#print axioms Paper254.countedDoublingRoute_epoch
#print axioms Paper254.countedDoublingRoute_operand_bits




