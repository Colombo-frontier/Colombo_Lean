import RationalWeights254

open scoped BigOperators
namespace Paper254

def rationalLiveMass {n : ℕ} (p : ℕ) (live : Finset (Fin n))
    (w z : Fin n→ℚ) (j : Fin n) : ℚ :=
  if j∈live then rationalUpperMass p w z j else 0

def rationalLiveSoftmax {n : ℕ} (p : ℕ) (live : Finset (Fin n))
    (w z : Fin n→ℚ) (j : Fin n) : ℚ :=
  rationalLiveMass p live w z j/(∑ k,rationalLiveMass p live w z k)

theorem rationalLiveMass_bounds {n : ℕ} (p : ℕ) (live : Finset (Fin n))
    (w z : Fin n→ℚ) (hw : ∀ j,0≤w j) (hsum : ∑ j,w j=1)
    (hsupport : ∀ j,j∉live → w j=0) (hz : ∀ j,|(z j:ℝ)|≤1/2) :
    let v := (rationalPrior w hw hsum).exponential (-1) (fun j=>(z j:ℝ))
    (∀ j,v.weight j≤(rationalLiveMass p live w z j:ℝ)) ∧
    (∀ j,(rationalLiveMass p live w z j:ℝ)≤v.weight j+
      if j∈live then 3*((2:ℝ)^p)⁻¹ else 0) ∧
    (∀ j,j∈live → ((2:ℝ)^p)⁻¹≤(rationalLiveMass p live w z j:ℝ)) := by
  let v := (rationalPrior w hw hsum).exponential (-1) (fun j=>(z j:ℝ))
  have hb := rationalUpperMass_bounds p w z hw hsum hz
  have hv0 : ∀ j,j∉live → v.weight j=0 := by
    intro j hj
    simp [v,ProbabilityWeights.exponential,exponentialUpdate,rationalPrior,hsupport j hj]
  constructor
  · intro j
    by_cases hj : j∈live
    · simpa only [rationalLiveMass,if_pos hj] using
        (le_add_of_nonneg_right (by positivity : 0≤((2:ℝ)^p)⁻¹)).trans (hb j).1
    · simp only [rationalLiveMass,if_neg hj,Rat.cast_zero]
      exact (hv0 j hj).le
  constructor
  · intro j
    by_cases hj : j∈live
    · simpa only [rationalLiveMass,if_pos hj] using (hb j).2
    · change (rationalLiveMass p live w z j:ℝ)≤v.weight j+_
      simp [rationalLiveMass,hj,hv0 j hj]
  · intro j hj
    have hh := (hb j).1
    change v.weight j+_≤_ at hh
    simpa only [rationalLiveMass,if_pos hj] using
      (le_add_of_nonneg_left (v.nonneg j)).trans hh

/-- Rounding has support only on the live set; its logarithmic cost depends
on the number of live entries, rather than the ambient expert count. -/
theorem rationalLiveSoftmax_spec {n : ℕ} (p : ℕ) (live : Finset (Fin n))
    (w z : Fin n→ℚ) (hw : ∀ j,0≤w j) (hsum : ∑ j,w j=1)
    (hsupport : ∀ j,j∉live → w j=0) (hz : ∀ j,|(z j:ℝ)|≤1/2) :
    let v := (rationalPrior w hw hsum).exponential (-1) (fun j=>(z j:ℝ))
    (∑ j,rationalLiveSoftmax p live w z j)=1 ∧
    (∀ j,0≤rationalLiveSoftmax p live w z j) ∧
    (∀ j,j∉live → rationalLiveSoftmax p live w z j=0) ∧
    (∀ j,v.weight j/(1+3*live.card*((2:ℝ)^p)⁻¹)≤(rationalLiveSoftmax p live w z j:ℝ)) ∧
    (∀ j,j∈live → ((2:ℝ)^p)⁻¹/(1+3*live.card*((2:ℝ)^p)⁻¹)≤
      (rationalLiveSoftmax p live w z j:ℝ)) := by
  let v := (rationalPrior w hw hsum).exponential (-1) (fun j=>(z j:ℝ))
  let Z : ℝ := ∑ j,(rationalLiveMass p live w z j:ℝ)
  let B : ℝ := 1+3*live.card*((2:ℝ)^p)⁻¹
  have hb := rationalLiveMass_bounds p live w z hw hsum hsupport hz
  have hZ1 : 1≤Z := by
    rw [←v.total]
    exact Finset.sum_le_sum (fun j _=>hb.1 j)
  have hZ : 0<Z := by linarith
  have hB : Z≤B := by
    calc
      _ ≤ ∑ j,(v.weight j+if j∈live then 3*((2:ℝ)^p)⁻¹ else 0) :=
        Finset.sum_le_sum (fun j _=>hb.2.1 j)
      _ = B := by rw [Finset.sum_add_distrib,v.total]; simp [B]; ring
  have hmass : ∀ j,0≤(rationalLiveMass p live w z j:ℝ) :=
    fun j=>(v.nonneg j).trans (hb.1 j)
  have hZq : 0<(∑ j,rationalLiveMass p live w z j:ℚ) := by
    dsimp [Z] at hZ
    exact_mod_cast hZ
  have hcast : ∀ j,(rationalLiveSoftmax p live w z j:ℝ)=
      (rationalLiveMass p live w z j:ℝ)/Z := by intro j; simp [rationalLiveSoftmax,Z]
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp only [rationalLiveSoftmax,←Finset.sum_div,div_self hZq.ne']
  · intro j
    have hh : 0≤(rationalLiveSoftmax p live w z j:ℝ) := by
      rw [hcast]
      exact div_nonneg (hmass j) hZ.le
    exact_mod_cast hh
  · intro j hj
    simp [rationalLiveSoftmax,rationalLiveMass,hj]
  · intro j
    rw [hcast]
    exact (div_le_div_of_nonneg_left (v.nonneg j) hZ hB).trans
      (div_le_div_of_nonneg_right (hb.1 j) hZ.le)
  · intro j hj
    rw [hcast]
    exact (div_le_div_of_nonneg_left (by positivity : 0≤((2:ℝ)^p)⁻¹) hZ hB).trans
      (div_le_div_of_nonneg_right (hb.2.2 j hj) hZ.le)

end Paper254
#print axioms Paper254.rationalLiveSoftmax_spec
