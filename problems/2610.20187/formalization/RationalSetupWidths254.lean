import RationalParameterSetup254
import RationalParameterEncoding254

noncomputable section
namespace Paper254

def parameterSetupWorkHeight (d K s v b : ℕ) : ℕ :=
  b+2*K+4*v+2*explicitSparseHistoryPrecision d s v+20

/-- Intermediate rational values in the cached configuration constructor.
The power clauses cover each recursive partial power, not only its result. -/
structure ParameterSetupWorkHeights (d K s v : ℕ) (hi : ℚ) (B : ℕ) : Prop where
  input : RationalHeight hi B
  smoothPowers : ∀ j≤4*v+explicitSparseHistoryPrecision d s v+6,
    RationalHeight (countedRatPow 2 j).1 B
  guardPowers : ∀ j≤explicitSparseHistoryPrecision d s v+2,
    RationalHeight (countedRatPow 2 j).1 B
  scalePowers : ∀ j≤K,RationalHeight (countedRatPow 2 j).1 B
  smoothing : RationalHeight ((countedRatPow 2 (4*v+explicitSparseHistoryPrecision d s v+6)).1⁻¹) B
  guard : RationalHeight ((countedRatPow 2 (explicitSparseHistoryPrecision d s v+2)).1⁻¹) B
  cap : RationalHeight (hi/4) B
  upper : RationalHeight (hi-(countedRatPow 2 (explicitSparseHistoryPrecision d s v+2)).1⁻¹) B
  scales : ∀ k : Fin (K+1),
    RationalHeight ((countedRatPow 2 k.val).1*(countedRatPow 2 k.val).1) B ∧
    RationalHeight (hi/((countedRatPow 2 k.val).1*(countedRatPow 2 k.val).1)) B ∧
    RationalHeight (min (hi/((countedRatPow 2 k.val).1*(countedRatPow 2 k.val).1)) (hi/4)) B ∧
    RationalHeight (min (hi/((countedRatPow 2 k.val).1*(countedRatPow 2 k.val).1)) (hi/4)+
      (countedRatPow 2 (explicitSparseHistoryPrecision d s v+2)).1⁻¹) B
  output : ∀ k : Fin (K+1),
    RationalHeight ((countedParameterSetup d K s v hi).1.1.get k).smoothing B ∧
    RationalHeight ((countedParameterSetup d K s v hi).1.1.get k).lowerThreshold B ∧
    RationalHeight ((countedParameterSetup d K s v hi).1.1.get k).upperThreshold B

theorem countedParameterSetup_work_heights (d K s v b : ℕ) (hi : ℚ)
    (hhi : RationalHeight hi b) :
    ParameterSetupWorkHeights d K s v hi (parameterSetupWorkHeight d K s v b) := by
  let r := explicitSparseHistoryPrecision d s v
  let n := 4*v+r+6
  let B := parameterSetupWorkHeight d K s v b
  let B0 := b+2*(K+1)+1
  have hcap : RationalHeight (hi/4) (b+3) := by
    have hh := hhi.mul (rationalTwoPow_height 2).inv
    norm_num only [pow_two] at hh
    simpa only [div_eq_mul_inv,one_mul] using hh
  have hguard : RationalHeight ((2:ℚ)^(r+2))⁻¹ (r+2) := (rationalTwoPow_height (r+2)).inv
  have hlo (k : Fin (K+1)) : RationalHeight (rationalCappedVariance hi k.val) B0 :=
    rationalCappedVariance_height hi b K k.val hhi (by omega)
  have hhB : RationalHeight hi B0 := hhi.mono (by dsimp [B0]; omega)
  refine ⟨hhi.mono ?_,?_,?_,?_,?_,?_,hcap.mono ?_,?_,?_,?_⟩
  · dsimp [parameterSetupWorkHeight]; omega
  · intro j hj
    rw [countedRatPow_spec]
    exact (rationalTwoPow_height j).mono (by dsimp [parameterSetupWorkHeight]; omega)
  · intro j hj
    rw [countedRatPow_spec]
    exact (rationalTwoPow_height j).mono (by dsimp [parameterSetupWorkHeight]; omega)
  · intro j hj
    rw [countedRatPow_spec]
    exact (rationalTwoPow_height j).mono (by dsimp [parameterSetupWorkHeight]; omega)
  · rw [countedRatPow_spec]
    exact (rationalTwoPow_height (4*v+r+6)).inv.mono (by dsimp [parameterSetupWorkHeight,r]; omega)
  · rw [countedRatPow_spec]
    exact hguard.mono (by dsimp [parameterSetupWorkHeight,r]; omega)
  · dsimp [parameterSetupWorkHeight]; omega
  · rw [countedRatPow_spec]
    exact (hhi.sub hguard).mono (by dsimp [parameterSetupWorkHeight,r]; omega)
  · intro k
    simp only [countedRatPow_spec]
    have hsquare : RationalHeight ((2:ℚ)^k.val*(2:ℚ)^k.val) (2*k.val) := by
      rw [←pow_add,←two_mul]
      exact rationalTwoPow_height (2*k.val)
    have hdivide : RationalHeight (hi/((2:ℚ)^k.val*(2:ℚ)^k.val)) (b+2*k.val+1) := by
      rw [div_eq_mul_inv]
      exact hhi.mul hsquare.inv
    have hmin : RationalHeight (min (hi/((2:ℚ)^k.val*(2:ℚ)^k.val)) (hi/4)) B0 := by
      simpa only [rationalCappedVariance,pow_two] using hlo k
    have hk := k.isLt
    refine ⟨hsquare.mono ?_,hdivide.mono ?_,hmin.mono ?_,(hmin.add hguard).mono ?_⟩
    all_goals dsimp [parameterSetupWorkHeight,B0,r]; omega
  · intro k
    rw [countedParameterSetup_value]
    have hh := uniformHistoryParameters_height v v r r B0 (rationalCappedVariance hi k.val) hi (hlo k) hhB
    exact ⟨hh.1.mono (by dsimp [parameterSetupWorkHeight,B0,r]; omega),
      hh.2.1.mono (by dsimp [parameterSetupWorkHeight,B0,r]; omega),
      hh.2.2.mono (by dsimp [parameterSetupWorkHeight,B0,r]; omega)⟩

def initialMassHeight (K : ℕ) : ℕ := Nat.log 2 (K+1)+1
def shareMassHeight (T : ℕ) : ℕ := Nat.log 2 (T+2)+1

theorem rational_initial_mass_height (K : ℕ) :
    RationalHeight (1/(K+1:ℚ)) (initialMassHeight K) := by
  have hb : K+1≤2^(initialMassHeight K) :=
    (Nat.lt_pow_succ_log_self (by norm_num : 1<2) (K+1)).le
  have hi : |(K+1:ℤ)|≤(2:ℤ)^(initialMassHeight K) := by
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast hb
  have hh : RationalHeight (K+1:ℚ) (initialMassHeight K) := by
    simpa only [Int.cast_add,Int.cast_natCast,Int.cast_one] using
      RationalHeight.of_int (K+1:ℤ) (initialMassHeight K) hi
  simpa only [one_div] using hh.inv

theorem rational_share_mass_height (T t : ℕ) (ht : t≤T) :
    RationalHeight (1/(t+2:ℚ)) (shareMassHeight T) := by
  have hb : t+2≤2^(shareMassHeight T) :=
    (show t+2≤T+2 by omega).trans
      (Nat.lt_pow_succ_log_self (by norm_num : 1<2) (T+2)).le
  have hi : |(t+2:ℤ)|≤(2:ℤ)^(shareMassHeight T) := by
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast hb
  have hh : RationalHeight (t+2:ℚ) (shareMassHeight T) := by
    simpa only [Int.cast_add,Int.cast_natCast,Int.cast_ofNat] using
      RationalHeight.of_int (t+2:ℤ) (shareMassHeight T) hi
  simpa only [one_div] using hh.inv

end Paper254
#print axioms Paper254.countedParameterSetup_work_heights
#print axioms Paper254.rational_initial_mass_height
#print axioms Paper254.rational_share_mass_height
