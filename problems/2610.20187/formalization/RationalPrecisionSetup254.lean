import RationalEncodedInput254
import IntegerMetadata254

namespace Paper254

structure RationalPrecisionParameters where
  scaleCount : ℕ
  magnitude : ℕ
  errorExponent : ℕ
  masterPrecision : ℕ
  historyPrecision : ℕ
  accuracy : ℕ
  spectralLog : ℕ
  deriving DecidableEq

/-- Two binary logarithms are evaluated once and reused. The remaining
25 charged additions/multiplications construct all integer tuning data.
The supplied error exponent z is an input, not a precision-search oracle. -/
def countedPrecisionSetup (d T b z : ℕ) : RationalPrecisionParameters × ℕ :=
  let kt := countedLogTwo T
  let jt := countedLogTwo (T+1)
  let k := kt.1
  let v := b+d+2*(k+1)+(jt.1+1)+4
  let s := b+z+k+2
  let p := s+v+3
  let r := 2*s+4*((5*d+60)*v)+4
  let n := 4*v+r+6
  let ell := n+v+2
  (⟨k,v,s,p,r,n,ell⟩,kt.2+jt.2+25)

theorem countedPrecisionSetup_program (d T b z : ℕ) :
    (countedPrecisionSetup d T b z).1=
      ⟨scaleCount T,workingMagnitude d T b,b+z+Nat.log 2 T+2,
        b+z+Nat.log 2 T+2+workingMagnitude d T b+3,
        explicitSparseHistoryPrecision d (b+z+Nat.log 2 T+2) (workingMagnitude d T b),
        4*workingMagnitude d T b+
          explicitSparseHistoryPrecision d (b+z+Nat.log 2 T+2) (workingMagnitude d T b)+6,
        4*workingMagnitude d T b+
          explicitSparseHistoryPrecision d (b+z+Nat.log 2 T+2) (workingMagnitude d T b)+6+
          workingMagnitude d T b+2⟩ := by
  simp [countedPrecisionSetup,countedLogTwo_spec,scaleCount,workingMagnitude,
    explicitSparseHistoryPrecision]

theorem countedPrecisionSetup_cost (d T b z : ℕ) :
    (countedPrecisionSetup d T b z).2=
      3*Nat.log 2 T+3*Nat.log 2 (T+1)+27 := by
  simp [countedPrecisionSetup,countedLogTwo_spec]
  omega

theorem countedPrecisionSetup_cost_bound (d T b z : ℕ) :
    (countedPrecisionSetup d T b z).2≤6*Nat.log 2 (T+1)+27 := by
  rw [countedPrecisionSetup_cost]
  have h := Nat.log_mono_right (show T≤T+1 by omega) (b:=2)
  omega

/-- Values of every straight-line arithmetic intermediate. Logarithm
recursion uses separate logarithmic word bounds below. -/
def precisionSetupArithmeticWords (d T b z : ℕ) : List ℕ :=
  let k := Nat.log 2 T
  let j := Nat.log 2 (T+1)
  let v := workingMagnitude d T b
  let s := b+z+k+2
  let r := explicitSparseHistoryPrecision d s v
  let n := 4*v+r+6
  [0,1,2,3,4,5,6,25,60,d,b,z,k,j,k+1,2*(k+1),j+1,
    b+d,b+d+2*(k+1),b+d+2*(k+1)+(j+1),v,
    b+z,b+z+k,s,s+v,s+v+3,2*s,5*d,5*d+60,(5*d+60)*v,
    4*((5*d+60)*v),2*s+4*((5*d+60)*v),r,4*v,4*v+r,n,n+v,n+v+2]

/-- An explicit polynomial in d,b,z,log(T+1); the fixed-length sum is
expanded only when a concrete bit-complexity polynomial is required. -/
def precisionSetupWordBits (d T b z : ℕ) : ℕ :=
  (precisionSetupArithmeticWords d T b z).sum+Nat.log 2 (T+1)+3

theorem precision_setup_arithmetic_operand_bits (d T b z x : ℕ)
    (hx : x∈precisionSetupArithmeticWords d T b z) :
    x.size≤precisionSetupWordBits d T b z := by
  have hxsum : x≤(precisionSetupArithmeticWords d T b z).sum :=
    List.single_le_sum (by intro a ha; exact Nat.zero_le a) x hx
  apply Nat.size_le.mpr
  exact (Nat.lt_two_pow_self (n:=x)).trans_le
    (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by
      unfold precisionSetupWordBits
      omega))

theorem precision_setup_log_operand_bits (d T b z n : ℕ) (hn : n≤T+1) :
    n.size≤precisionSetupWordBits d T b z ∧
    (n/2).size≤precisionSetupWordBits d T b z ∧
    (Nat.log 2 n+1).size≤precisionSetupWordBits d T b z := by
  have hnlt : n<2^(Nat.log 2 (T+1)+1) :=
    hn.trans_lt (Nat.lt_pow_succ_log_self (by decide : 1<(2:ℕ)) (T+1))
  have he : Nat.log 2 (T+1)+1≤precisionSetupWordBits d T b z := by
    unfold precisionSetupWordBits
    omega
  have hl : Nat.log 2 n+1≤precisionSetupWordBits d T b z :=
    (Nat.add_le_add_right (Nat.log_mono_right hn) 1).trans he
  refine ⟨Nat.size_le.mpr (hnlt.trans_le (Nat.pow_le_pow_right (by decide) he)),
    Nat.size_le.mpr (((Nat.div_le_self n 2).trans_lt hnlt).trans_le
      (Nat.pow_le_pow_right (by decide) he)),?_⟩
  exact Nat.size_le.mpr ((Nat.lt_two_pow_self (n:=Nat.log 2 n+1)).trans_le
    (Nat.pow_le_pow_right (by decide) hl))

end Paper254

#print axioms Paper254.countedPrecisionSetup_program
#print axioms Paper254.countedPrecisionSetup_cost_bound
#print axioms Paper254.precision_setup_arithmetic_operand_bits
#print axioms Paper254.precision_setup_log_operand_bits
