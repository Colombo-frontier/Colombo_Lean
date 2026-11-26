import MasterIntermediateHeight254

noncomputable section
namespace Paper254

theorem RationalHeight.of_bits (x : ℚ) (b : ℕ)
    (hn : x.num.natAbs.size≤b) (hd : x.den.size≤b) : RationalHeight x b := by
  have hn' : x.num.natAbs≤2^b := (Nat.size_le.mp hn).le
  have hd' : x.den≤2^b := (Nat.size_le.mp hd).le
  refine ⟨fun _ _=>x.num,(x.den:ℤ),by exact_mod_cast x.den_ne_zero,?_,?_,?_⟩
  · rw [abs_of_nonneg (by positivity)]
    exact_mod_cast hd'
  · intro i j
    have hnz : (x.num.natAbs:ℤ)≤(2:ℤ)^b := by exact_mod_cast hn'
    simpa only [Int.natCast_natAbs] using hnz
  · intro i j
    simpa using x.num_div_den.symm

def masterArithmeticBound (N M p : ℕ) :=
  N*(3*(p+7)+7)+M*(3*(p+7)+13)+2*p+4

def masterPrimitiveBits (N M p H : ℕ) := 4*H+N+M+p+10

/-- This runs the same cached master program, with a uniform per-primitive
upper charge justified by its actual intermediate encoding certificate. -/
def chargedMasterUpdate {n : ℕ} (model : PolynomialArithmeticCharge) (workBits p : ℕ)
    (live next : Finset (Fin n)) (w z prior : Fin n→ℚ) (alpha : ℚ) : List (Fin n×ℚ)×ℕ :=
  let run := countedMasterUpdate p 1 live next w z prior alpha
  (run.1,run.2*model.cost workBits)

theorem chargedMasterUpdate_bound {n : ℕ} (model : PolynomialArithmeticCharge) (workBits p : ℕ)
    (live next : Finset (Fin n)) (w z prior : Fin n→ℚ) (alpha : ℚ) :
    (chargedMasterUpdate model workBits p live next w z prior alpha).2≤
      masterArithmeticBound live.card next.card p*model.coefficient*(workBits+1)^model.degree := by
  have hc := countedMasterUpdate_cost p 1 live next w z prior alpha
  have hb := model.bound workBits
  change (countedMasterUpdate p 1 live next w z prior alpha).2*model.cost workBits≤_
  rw [hc]
  simpa only [masterArithmeticBound,Nat.mul_assoc,Nat.add_assoc] using
    Nat.mul_le_mul_left (masterArithmeticBound live.card next.card p) hb

/-- The value, the full live-only execution's intermediate encodings, its
returned weights, and its bit charge are certified for one actual program. -/
theorem chargedMasterUpdate_certificate {n b : ℕ} (model : PolynomialArithmeticCharge)
    (p : ℕ) (live next : Finset (Fin n)) (w z prior : Fin n→ℚ) (alpha : ℚ)
    (hsupport : ∀ j,j∉live→w j=0)
    (hw : ∀ j∈live,RationalHeight (w j) b) (hz : ∀ j∈live,RationalHeight (z j) b)
    (hp : ∀ j∈next,RationalHeight (prior j) b) (ha : RationalHeight alpha b) :
    let H := masterWorkHeight live.card next.card p b
    let run := chargedMasterUpdate model (masterPrimitiveBits live.card next.card p H) p live next w z prior alpha
    rationalLookup run.1=rationalMasterUpdate p live next w z prior alpha ∧
    MasterWorkHeights p live next w z prior alpha H ∧
    (∀ j,(rationalLookup run.1 j).num.natAbs.size≤H+1 ∧ (rationalLookup run.1 j).den.size≤H+1) ∧
    run.2≤masterArithmeticBound live.card next.card p*model.coefficient*
      (masterPrimitiveBits live.card next.card p H+1)^model.degree := by
  have hh := master_work_heights p live next w z prior alpha hw hz hp ha
  refine ⟨countedMasterUpdate_value p 1 live next w z prior alpha hsupport,hh,?_,?_⟩
  · intro j
    exact (rationalLookup_height _ hh.2.2.2 j).reduced_bits
  · exact chargedMasterUpdate_bound model _ p live next w z prior alpha

end Paper254
#print axioms Paper254.chargedMasterUpdate_certificate
