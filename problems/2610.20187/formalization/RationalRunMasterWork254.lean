import RationalRunWork254
import MasterBitCertificate254

noncomputable section
open scoped BigOperators
namespace Paper254

@[gcongr] theorem normalizeHeight_mono {N N' b b' : ℕ} (hN : N≤N') (hb : b≤b') :
    normalizeHeight N b≤normalizeHeight N' b' := by unfold normalizeHeight; gcongr

@[gcongr] theorem taylorWorkHeight_mono {N b b' : ℕ} (hb : b≤b') :
    taylorWorkHeight N b≤taylorWorkHeight N b' := by unfold taylorWorkHeight; gcongr

@[gcongr] theorem softmaxExpHeight_mono {p b b' : ℕ} (hb : b≤b') :
    softmaxExpHeight p b≤softmaxExpHeight p b' := by unfold softmaxExpHeight; gcongr

@[gcongr] theorem softmaxRawHeight_mono {p b b' : ℕ} (hb : b≤b') :
    softmaxRawHeight p b≤softmaxRawHeight p b' := by unfold softmaxRawHeight; gcongr

@[gcongr] theorem softmaxNormalizedHeight_mono {N N' p b b' : ℕ}
    (hN : N≤N') (hb : b≤b') :
    softmaxNormalizedHeight N p b≤softmaxNormalizedHeight N' p b' := by
  unfold softmaxNormalizedHeight; gcongr

@[gcongr] theorem softmaxUpperHeight_mono {N N' p b b' : ℕ}
    (hN : N≤N') (hb : b≤b') :
    softmaxUpperHeight N p b≤softmaxUpperHeight N' p b' := by
  unfold softmaxUpperHeight; gcongr

@[gcongr] theorem softmaxOutputHeight_mono {N N' p b b' : ℕ}
    (hN : N≤N') (hb : b≤b') :
    softmaxOutputHeight N p b≤softmaxOutputHeight N' p b' := by
  unfold softmaxOutputHeight; gcongr

@[gcongr] theorem softmaxWorkHeight_mono {N N' p b b' : ℕ}
    (hN : N≤N') (hb : b≤b') :
    softmaxWorkHeight N p b≤softmaxWorkHeight N' p b' := by
  unfold softmaxWorkHeight; gcongr

@[gcongr] theorem shareRawHeight_mono {w w' b b' : ℕ} (hw : w≤w') (hb : b≤b') :
    shareRawHeight w b≤shareRawHeight w' b' := by unfold shareRawHeight; gcongr

@[gcongr] theorem shareOutputHeight_mono {N N' w w' b b' : ℕ}
    (hN : N≤N') (hw : w≤w') (hb : b≤b') :
    shareOutputHeight N w b≤shareOutputHeight N' w' b' := by unfold shareOutputHeight; gcongr

@[gcongr] theorem shareWorkHeight_mono {N N' w w' b b' : ℕ}
    (hN : N≤N') (hw : w≤w') (hb : b≤b') :
    shareWorkHeight N w b≤shareWorkHeight N' w' b' := by unfold shareWorkHeight; gcongr

theorem masterWorkHeight_mono_counts {N M N' M' p b : ℕ} (hN : N≤N') (hM : M≤M') :
    masterWorkHeight N M p b≤masterWorkHeight N' M' p b := by
  unfold masterWorkHeight masterOutputHeight
  gcongr

theorem masterArithmeticBound_mono {N M N' M' p : ℕ} (hN : N≤N') (hM : M≤M') :
    masterArithmeticBound N M p≤masterArithmeticBound N' M' p := by
  unfold masterArithmeticBound
  gcongr

namespace RationalRunEncodingSetup
variable {d T K : ℕ} {D G eta : ℝ} {W : Domain d D}
variable {C : RationalSparseConstruction d T K D G eta W} (E : RationalRunEncodingSetup C)

def exponentHeight := 3*(d*(E.L0+E.meanBits+E.predictionBits+3))+2*E.parameterBits+5
def shareHeight (_E : RationalRunEncodingSetup C) := Nat.log 2 (T+2)+1
def masterInputHeight := E.weightBits+E.exponentHeight+E.liveLog+E.shareHeight
def uniformMasterHeight := masterWorkHeight (standardLiveCap T K) (standardLiveCap T K)
  C.master_precision E.masterInputHeight
def uniformMasterBits := masterPrimitiveBits (standardLiveCap T K) (standardLiveCap T K)
  C.master_precision E.uniformMasterHeight

theorem exponent_height (t : ℕ) (hresponse : t<E.responseHorizon) (e : Fin ((T+1)*(K+1))) :
    RationalHeight (rationalSparseExponents C.lam (C.run t) (C.gradient t) e) E.exponentHeight := by
  apply rationalExponent_height _ _ _ _ E.L0 E.predictionBits E.meanBits E.parameterBits
  · intro j
    have hh := E.gradient_encoding t hresponse j
    exact RationalHeight.of_bits _ _ hh.1 hh.2
  · intro j
    have hh := E.prediction_bits t j
    exact RationalHeight.of_bits _ _ hh.1 hh.2
  · intro j
    have hh := (E.history_bits t e).2 j
    exact RationalHeight.of_bits _ _ hh.1 hh.2
  · exact E.rate_height

theorem master_prior_height (t : ℕ) (e : Fin ((T+1)*(K+1))) :
    RationalHeight ((standardRationalSchedule T K).prior t e) E.liveLog := by
  have hK : (K+1:ℤ)≤(2:ℤ)^E.liveLog := by
    have hc : K+1≤standardLiveCap T K := by unfold standardLiveCap; nlinarith
    exact (Int.ofNat_le.mpr hc).trans E.live_bound
  have hp := numberedBirthPrior_height T K E.liveLog ⟨min (t+1) T,by omega⟩ hK
  exact hp.submatrix (fun _ : Fin 1=>e) (fun j : Fin 1=>j)

theorem master_share_height (t : ℕ) (ht : t<T) :
    RationalHeight ((standardRationalSchedule T K).share t) E.shareHeight := by
  have ht2 : t+2≤2^(Nat.log 2 (T+2)+1) :=
    (show t+2≤T+2 by omega).trans (Nat.lt_pow_succ_log_self (by norm_num : 1<2) (T+2)).le
  have hh := RationalHeight.of_int (t+2) E.shareHeight (by
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast ht2)
  simpa [standardRationalSchedule,one_div] using hh.inv

/-- The full cached master's uniform work bound follows from initial/oracle
encoding assumptions; no evolved-state bit bound is an input. -/
theorem master_work_heights (t : ℕ) (ht : t<T) (hresponse : t<E.responseHorizon) :
    MasterWorkHeights C.master_precision ((standardRationalSchedule T K).live t)
      ((standardRationalSchedule T K).live (t+1)) (C.run t).weights
      (rationalSparseExponents C.lam (C.run t) (C.gradient t))
      ((standardRationalSchedule T K).prior t) ((standardRationalSchedule T K).share t)
      E.uniformMasterHeight := by
  have hw : ∀ e,RationalHeight ((C.run t).weights e) E.masterInputHeight := by
    intro e
    have hh := E.weight_bits t e
    exact (RationalHeight.of_bits _ _ hh.1 hh.2).mono (by dsimp [masterInputHeight]; omega)
  have hz : ∀ e,RationalHeight (rationalSparseExponents C.lam (C.run t) (C.gradient t) e)
      E.masterInputHeight := fun e=>(E.exponent_height t hresponse e).mono (by dsimp [masterInputHeight]; omega)
  have hp : ∀ e,RationalHeight ((standardRationalSchedule T K).prior t e) E.masterInputHeight :=
    fun e=>(E.master_prior_height t e).mono (by dsimp [masterInputHeight]; omega)
  have ha := (E.master_share_height t ht).mono (show E.shareHeight≤E.masterInputHeight by
    dsimp [masterInputHeight]; omega)
  have hh := Paper254.master_work_heights C.master_precision
    ((standardRationalSchedule T K).live t) ((standardRationalSchedule T K).live (t+1))
    (C.run t).weights (rationalSparseExponents C.lam (C.run t) (C.gradient t))
    ((standardRationalSchedule T K).prior t) ((standardRationalSchedule T K).share t)
    (fun e _=>hw e) (fun e _=>hz e) (fun e _=>hp e) ha
  exact hh.mono (masterWorkHeight_mono_counts (standardRationalSchedule_uniform_card T K t)
    (standardRationalSchedule_uniform_card T K (t+1)))

def masterRun (model : PolynomialArithmeticCharge) (t : ℕ) :=
  chargedMasterUpdate model E.uniformMasterBits C.master_precision
    ((standardRationalSchedule T K).live t) ((standardRationalSchedule T K).live (t+1))
    (C.run t).weights (rationalSparseExponents C.lam (C.run t) (C.gradient t))
    ((standardRationalSchedule T K).prior t) ((standardRationalSchedule T K).share t)

def masterChargeBound (model : PolynomialArithmeticCharge) :=
  masterArithmeticBound (standardLiveCap T K) (standardLiveCap T K) C.master_precision*
    model.coefficient*(E.uniformMasterBits+1)^model.degree

theorem master_run_charge (model : PolynomialArithmeticCharge) (t : ℕ) :
    (E.masterRun model t).2≤E.masterChargeBound model := by
  apply (chargedMasterUpdate_bound model E.uniformMasterBits C.master_precision
    ((standardRationalSchedule T K).live t) ((standardRationalSchedule T K).live (t+1))
    (C.run t).weights (rationalSparseExponents C.lam (C.run t) (C.gradient t))
    ((standardRationalSchedule T K).prior t) ((standardRationalSchedule T K).share t)).trans
  apply Nat.mul_le_mul_right
  apply Nat.mul_le_mul_right
  exact masterArithmeticBound_mono (standardRationalSchedule_uniform_card T K t)
    (standardRationalSchedule_uniform_card T K (t+1))

set_option maxHeartbeats 2000000 in
theorem master_run_certificate (model : PolynomialArithmeticCharge) (t : ℕ) (ht : t<T)
    (hresponse : t<E.responseHorizon) :
    rationalLookup (E.masterRun model t).1=(C.run (t+1)).weights ∧
    MasterWorkHeights C.master_precision ((standardRationalSchedule T K).live t)
      ((standardRationalSchedule T K).live (t+1)) (C.run t).weights
      (rationalSparseExponents C.lam (C.run t) (C.gradient t))
      ((standardRationalSchedule T K).prior t) ((standardRationalSchedule T K).share t)
      E.uniformMasterHeight ∧
    (E.masterRun model t).2≤E.masterChargeBound model := by
  refine ⟨?_,E.master_work_heights t ht hresponse,E.master_run_charge model t⟩
  · exact countedMasterUpdate_value C.master_precision 1
      ((standardRationalSchedule T K).live t) ((standardRationalSchedule T K).live (t+1))
      (C.run t).weights (rationalSparseExponents C.lam (C.run t) (C.gradient t))
      ((standardRationalSchedule T K).prior t) ((standardRationalSchedule T K).share t) (C.invariant t).support

theorem total_master_charge (model : PolynomialArithmeticCharge) :
    (∑ t : Fin T,(E.masterRun model t).2)≤T*E.masterChargeBound model := by
  calc
    _ ≤ ∑ _t : Fin T,E.masterChargeBound model := Finset.sum_le_sum (fun t _=>
      E.master_run_charge model t)
    _ = _ := by simp

end RationalRunEncodingSetup
end Paper254
#print axioms Paper254.RationalRunEncodingSetup.master_run_certificate
#print axioms Paper254.RationalRunEncodingSetup.total_master_charge
