import RationalLiveWeights254

open scoped BigOperators
namespace Paper254

def rationalPrunedMass {n : ℕ} (w prior : Fin n→ℚ) (alpha : ℚ)
    (live : Finset (Fin n)) (j : Fin n) : ℚ :=
  if j∈live then (1-alpha)*w j+alpha*prior j else 0

def rationalPruneShare {n : ℕ} (w prior : Fin n→ℚ) (alpha : ℚ)
    (live : Finset (Fin n)) (j : Fin n) : ℚ :=
  rationalPrunedMass w prior alpha live j/(∑ k,rationalPrunedMass w prior alpha live k)

def rationalRoundedPruneShare {n : ℕ} (p : ℕ) (w prior : Fin n→ℚ) (alpha : ℚ)
    (live : Finset (Fin n)) : Fin n→ℚ :=
  rationalLiveSoftmax p live (rationalPruneShare w prior alpha live) (fun _=>0)

theorem rationalPruneShare_spec {n : ℕ} (w prior : Fin n→ℚ) (alpha : ℚ)
    (live : Finset (Fin n)) (hw : ∀ j,0≤w j) (hw1 : ∑ j,w j=1)
    (hp : ∀ j,0≤prior j) (hp1 : ∑ j,prior j=1) (ha : 0<alpha) (ha1 : alpha≤1)
    (hprior : ∀ j,0<prior j → j∈live) :
    (∀ j,0≤rationalPruneShare w prior alpha live j) ∧
    (∑ j,rationalPruneShare w prior alpha live j)=1 ∧
    (∀ j,j∉live → rationalPruneShare w prior alpha live j=0) ∧
    (∀ j,j∈live → (1-alpha)*w j≤rationalPruneShare w prior alpha live j ∧
      alpha*prior j≤rationalPruneShare w prior alpha live j) := by
  let W := rationalPrior w hw hw1
  let P := rationalPrior prior hp hp1
  have har : 0<(alpha:ℝ) := by exact_mod_cast ha
  have ha1r : (alpha:ℝ)≤1 := by exact_mod_cast ha1
  have hpr : ∀ j,0<P.weight j → j∈live := by
    intro j hj
    exact hprior j (Rat.cast_pos.mp hj)
  let Q := W.pruneShare P (alpha:ℝ) har ha1r live hpr
  have hmass : ∀ j,(rationalPrunedMass w prior alpha live j:ℝ)=
      W.prunedMixtureMass P (alpha:ℝ) live j := by
    intro j
    by_cases hj : j∈live <;>
      simp [rationalPrunedMass,ProbabilityWeights.prunedMixtureMass,hj,W,P,rationalPrior]
  have hcast : ∀ j,(rationalPruneShare w prior alpha live j:ℝ)=Q.weight j := by
    intro j
    simp only [rationalPruneShare,Rat.cast_div,Rat.cast_sum,hmass]
    rfl
  refine ⟨?_,?_,?_,?_⟩
  · intro j
    have hh : 0≤(rationalPruneShare w prior alpha live j:ℝ) := by rw [hcast]; exact Q.nonneg j
    exact_mod_cast hh
  · have hh : (∑ j,(rationalPruneShare w prior alpha live j:ℝ))=1 := by
      simp only [hcast,Q.total]
    exact_mod_cast hh
  · intro j hj
    simp [rationalPruneShare,rationalPrunedMass,hj]
  · intro j hj
    have hs := W.pruneShare_survival P (alpha:ℝ) har ha1r live hpr j hj
    have hb := W.pruneShare_birth P (alpha:ℝ) har ha1r live hpr j hj
    change (1-(alpha:ℝ))*(w j:ℝ)≤Q.weight j at hs
    change (alpha:ℝ)*(prior j:ℝ)≤Q.weight j at hb
    rw [←hcast] at hs hb
    exact ⟨by exact_mod_cast hs,by exact_mod_cast hb⟩

theorem rationalLiveSoftmax_zero_lower {n : ℕ} (p : ℕ) (live : Finset (Fin n))
    (w : Fin n→ℚ) (hw : ∀ j,0≤w j) (hw1 : ∑ j,w j=1)
    (hsupport : ∀ j,j∉live → w j=0) (j : Fin n) :
    (w j:ℝ)/(1+3*live.card*((2:ℝ)^p)⁻¹)≤
      (rationalLiveSoftmax p live w (fun _=>0) j:ℝ) := by
  have hh := (rationalLiveSoftmax_spec p live w (fun _=>0) hw hw1 hsupport (by intro j; norm_num)).2.2.2.1 j
  have hn : exponentialNormalizer (-1) (rationalPrior w hw hw1).weight (fun _=>(0:ℝ))=1 := by
    simp only [exponentialNormalizer,mul_zero,Real.exp_zero,mul_one]
    exact (rationalPrior w hw hw1).total
  simp only [ProbabilityWeights.exponential,exponentialUpdate,Rat.cast_zero,mul_zero,neg_zero,
    Real.exp_zero,mul_one] at hh
  change ((w j:ℝ)/exponentialNormalizer (-1) (rationalPrior w hw hw1).weight (fun _=>(0:ℝ)))/
    (1+3*live.card*((2:ℝ)^p)⁻¹)≤_ at hh
  rwa [hn,div_one] at hh

/-- Birth and deletion followed by actual rational rounding preserve a
relative survival bound, with an explicit local logarithmic overhead. -/
theorem rationalRoundedPruneShare_spec {n : ℕ} (p : ℕ) (w prior : Fin n→ℚ) (alpha : ℚ)
    (live : Finset (Fin n)) (hw : ∀ j,0≤w j) (hw1 : ∑ j,w j=1)
    (hp : ∀ j,0≤prior j) (hp1 : ∑ j,prior j=1) (ha : 0<alpha) (ha1 : alpha≤1)
    (hprior : ∀ j,0<prior j → j∈live) :
    (∑ j,rationalRoundedPruneShare p w prior alpha live j)=1 ∧
    (∀ j,0≤rationalRoundedPruneShare p w prior alpha live j) ∧
    (∀ j,j∉live → rationalRoundedPruneShare p w prior alpha live j=0) ∧
    (∀ j,j∈live →
      ((1-(alpha:ℝ))*(w j:ℝ))/(1+3*live.card*((2:ℝ)^p)⁻¹)≤
        (rationalRoundedPruneShare p w prior alpha live j:ℝ) ∧
      ((alpha:ℝ)*(prior j:ℝ))/(1+3*live.card*((2:ℝ)^p)⁻¹)≤
        (rationalRoundedPruneShare p w prior alpha live j:ℝ)) := by
  have hs := rationalPruneShare_spec w prior alpha live hw hw1 hp hp1 ha ha1 hprior
  have hr := rationalLiveSoftmax_spec p live (rationalPruneShare w prior alpha live) (fun _=>0)
    hs.1 hs.2.1 hs.2.2.1 (by intro j; norm_num)
  refine ⟨hr.1,hr.2.1,hr.2.2.1,?_⟩
  intro j hj
  have hl := rationalLiveSoftmax_zero_lower p live (rationalPruneShare w prior alpha live)
    hs.1 hs.2.1 hs.2.2.1 j
  have hden : 0≤1+3*(live.card:ℝ)*((2:ℝ)^p)⁻¹ := by positivity
  have hsurv : (1-(alpha:ℝ))*(w j:ℝ)≤(rationalPruneShare w prior alpha live j:ℝ) :=
    by exact_mod_cast (hs.2.2.2 j hj).1
  have hbirth : (alpha:ℝ)*(prior j:ℝ)≤(rationalPruneShare w prior alpha live j:ℝ) :=
    by exact_mod_cast (hs.2.2.2 j hj).2
  exact ⟨(div_le_div_of_nonneg_right hsurv hden).trans hl,
    (div_le_div_of_nonneg_right hbirth hden).trans hl⟩

end Paper254
#print axioms Paper254.rationalRoundedPruneShare_spec
