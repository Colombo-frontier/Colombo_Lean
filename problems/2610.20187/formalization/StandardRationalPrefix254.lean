import StandardRationalSchedule254
import RationalSparseBirth254

noncomputable section
namespace Paper254

def standardLiveCap (T K : ℕ) : ℕ := 5*(Nat.log 2 (T+1)+1)*(K+1)

def standardBirthMass (T K p : ℕ) : ℝ :=
  1/((K+1:ℝ)*(1+3*standardLiveCap T K*((2:ℝ)^p)⁻¹))

def standardMasterError (T K p : ℕ) : ℝ :=
  6*standardLiveCap T K*((2:ℝ)^p)⁻¹

theorem standardRationalSchedule_uniform_card (T K t : ℕ) :
    ((standardRationalSchedule T K).live t).card≤standardLiveCap T K := by
  apply (standardRationalSchedule_card T K t).trans
  unfold standardLiveCap
  have hh := Nat.log_mono_right (b:=2) (Nat.add_le_add_right (Nat.min_le_right t T) 1)
  nlinarith

theorem standardBirthMass_pos (T K p : ℕ) : 0<standardBirthMass T K p := by
  unfold standardBirthMass
  positivity

theorem standardBirthMass_le (T K p : ℕ) : standardBirthMass T K p≤1/(K+1:ℝ) := by
  unfold standardBirthMass
  apply one_div_le_one_div_of_le (by positivity)
  have h : 0≤3*(standardLiveCap T K:ℝ)*((2:ℝ)^p)⁻¹ := by positivity
  nlinarith [show (0:ℝ)≤K by positivity]

theorem standardRationalSchedule_master_error (T K p t : ℕ) :
    rationalSparseMasterError p (standardRationalSchedule T K) t≤standardMasterError T K p := by
  have h₁ : (((standardRationalSchedule T K).live t).card:ℝ)≤standardLiveCap T K :=
    Nat.cast_le.mpr (standardRationalSchedule_uniform_card T K t)
  have h₂ : (((standardRationalSchedule T K).live (t+1)).card:ℝ)≤standardLiveCap T K :=
    Nat.cast_le.mpr (standardRationalSchedule_uniform_card T K (t+1))
  unfold rationalSparseMasterError standardMasterError
  push_cast
  have hp : 0≤((2:ℝ)^p)⁻¹ := by positivity
  nlinarith

theorem standardRationalRun_birth_weight {d T K : ℕ} {D G eta : ℝ} (W : Domain d D)
    (hD : 0<D) (hG : 0<G) (heta : 0<eta)
    (oracle : RationalProjectionProcedure d) (cfg : Fin ((T+1)*(K+1))→RationalHistoryParameters)
    (p : ℕ) (lam : ℚ) (hlam : 2*(lam:ℝ)=curvature D G eta)
    (lo : Fin ((T+1)*(K+1))→ℝ) (hi : ℝ)
    (initial : RationalSparseData d ((T+1)*(K+1)))
    (hinit : initial.weights=numberedBirthPrior T K ⟨0,by omega⟩)
    (query : ℕ→RationalGradientQuery d)
    (hstate : ∀ t,RationalSparseInvariant W lo hi ((standardRationalSchedule T K).live t)
      (rationalSparseRun oracle cfg p lam (standardRationalSchedule T K) initial query t))
    (hg : ∀ t w,WithLp.toLp 2 (fun j=>(w j:ℝ))∈W.carrier →
      ‖WithLp.toLp 2 (fun j=>(query t w j:ℝ))‖≤G)
    (i : Fin (T+1)) (k : Fin (K+1)) :
    standardBirthMass T K p/(i.val+1:ℝ)≤
      ((rationalSparseRun oracle cfg p lam (standardRationalSchedule T K) initial query i.val).weights
        (numberedExpertEquiv T K (i,k)):ℝ) := by
  rcases i with ⟨i,hiT⟩
  cases i with
  | zero =>
    simpa [rationalSparseRun,hinit,numberedBirthPrior] using standardBirthMass_le T K p
  | succ i =>
    have hbirth := rationalSparseRun_birth_weight W hD hG heta oracle cfg p lam hlam lo hi
      (standardRationalSchedule T K) (standardRationalSchedule_spec T K) initial query hstate hg i
      (numberedExpertEquiv T K (⟨i+1,hiT⟩,k))
      ((standardRationalSchedule_live (by omega : i+1≤T) _).mpr
        (by simpa [expertBirth] using historyActive_birth (i+2) (by omega)))
    have hprior := standardRationalSchedule_birth (by omega : i<T) k
    rw [hprior] at hbirth
    have hshare : ((standardRationalSchedule T K).share i:ℝ)=1/(i+2:ℝ) := by
      simp [standardRationalSchedule]
    rw [hshare] at hbirth
    push_cast at hbirth
    apply le_trans _ hbirth
    have hcap : (((standardRationalSchedule T K).live (i+1)).card:ℝ)≤standardLiveCap T K :=
      Nat.cast_le.mpr (standardRationalSchedule_uniform_card T K (i+1))
    have hden : 1+3*(((standardRationalSchedule T K).live (i+1)).card:ℝ)*((2:ℝ)^p)⁻¹≤
      1+3*(standardLiveCap T K:ℝ)*((2:ℝ)^p)⁻¹ := by gcongr
    have hcmp := one_div_le_one_div_of_le (by positivity :
      0<1+3*(((standardRationalSchedule T K).live (i+1)).card:ℝ)*((2:ℝ)^p)⁻¹) hden
    have hm := mul_le_mul_of_nonneg_left hcmp
      (by positivity : 0≤1/((i+2:ℝ)*(K+1:ℝ)))
    simpa [standardBirthMass,Nat.cast_add,Nat.cast_one,div_eq_mul_inv,
      mul_assoc,mul_left_comm,mul_comm,add_assoc,show (1:ℝ)+1=2 by norm_num] using hm

theorem standardRationalRun_prefix {d T K : ℕ} {D G eta : ℝ} (W : Domain d D)
    (hD : 0<D) (hG : 0<G) (heta : 0<eta)
    (oracle : RationalProjectionProcedure d) (cfg : Fin ((T+1)*(K+1))→RationalHistoryParameters)
    (p : ℕ) (lam : ℚ) (hlam : 2*(lam:ℝ)=curvature D G eta)
    (lo : Fin ((T+1)*(K+1))→ℝ) (hi : ℝ)
    (initial : RationalSparseData d ((T+1)*(K+1)))
    (hinit : initial.weights=numberedBirthPrior T K ⟨0,by omega⟩)
    (query : ℕ→RationalGradientQuery d)
    (hstate : ∀ t,RationalSparseInvariant W lo hi ((standardRationalSchedule T K).live t)
      (rationalSparseRun oracle cfg p lam (standardRationalSchedule T K) initial query t))
    (hg : ∀ t w,WithLp.toLp 2 (fun j=>(w j:ℝ))∈W.carrier →
      ‖WithLp.toLp 2 (fun j=>(query t w j:ℝ))‖≤G)
    (i length : ℕ) (horizon : i+length<T) (k : Fin (K+1))
    (halive : HistoryActive (i+length+1) (i+1)) :
    cumulative (fun j=>
      let S := rationalSparseRun oracle cfg p lam (standardRationalSchedule T K) initial query (i+j)
      rationalSparseDifference lam S (query (i+j) (rationalSparsePrediction S))
        (numberedExpertEquiv T K (⟨i,by omega⟩,k))) (length+1)≤
      Real.log ((T:ℝ)/standardBirthMass T K p)/(lam:ℝ)+
        (length+1:ℝ)*standardMasterError T K p/(lam:ℝ) := by
  have hlam0 : 0<(lam:ℝ) := by have h := curvature_pos D G eta hD hG heta; linarith
  have hq := standardBirthMass_pos T K p
  have hb := standardRationalRun_birth_weight W hD hG heta oracle cfg p lam hlam lo hi
    initial hinit query hstate hg ⟨i,by omega⟩ k
  have hh := rationalSparseRun_prefix W hD hG heta oracle cfg p lam hlam lo hi
    (standardRationalSchedule T K) (standardRationalSchedule_spec T K) initial query hstate hg
    i length (numberedExpertEquiv T K (⟨i,by omega⟩,k)) (standardBirthMass T K p) hq hb
    (fun j hj=>(standardRationalSchedule_live (by omega : i+j≤T) _).mpr
      (by simpa [expertBirth] using (historyActive_prefix halive (by omega : i+1 ≤ i+j+1)
        (by omega : i+j+1 ≤ i+length+1))))
    (by intro j hj; simp [standardRationalSchedule,Nat.cast_add])
  apply hh.trans
  apply add_le_add
  · apply div_le_div_of_nonneg_right _ (le_of_lt hlam0)
    apply Real.log_le_log (div_pos (by positivity) hq)
    apply div_le_div_of_nonneg_right _ (le_of_lt hq)
    exact_mod_cast (show i+1+length≤T by omega)
  · apply div_le_div_of_nonneg_right _ (le_of_lt hlam0)
    calc
      cumulative (fun j=>rationalSparseMasterError p (standardRationalSchedule T K) (i+j))
          (length+1)≤
        ∑ j∈Finset.range (length+1),standardMasterError T K p := by
          exact Finset.sum_le_sum (fun j hj=>standardRationalSchedule_master_error T K p (i+j))
      _=(length+1:ℝ)*standardMasterError T K p := by simp

end Paper254
#print axioms Paper254.standardRationalRun_birth_weight
#print axioms Paper254.standardRationalRun_prefix
