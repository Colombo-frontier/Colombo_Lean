import RationalCompactMaster254
import RationalSparseLearner254

open scoped BigOperators
open Matrix
namespace Paper254

def countedSparsePrediction {d n : ℕ} (live : Finset (Fin n)) (S : RationalSparseData d n) :
    (Fin d→ℚ)×ℕ :=
  let rows:=Vector.ofFn (fun j:Fin d=>countedDot ((live.sort (·≤·)).map
    (fun e=>(S.weights e,(S.histories e).mean j))))
  (fun j=>(rows.get j).1,(rows.toList.map Prod.snd).sum)

theorem countedSparsePrediction_value {d n : ℕ} (live : Finset (Fin n))
    (S : RationalSparseData d n) (hsupport : ∀ e,e∉live → S.weights e=0) :
    (countedSparsePrediction live S).1=rationalSparsePrediction S := by
  funext j
  simp only [countedSparsePrediction]
  have hv : ((Vector.ofFn (fun j:Fin d=>countedDot ((live.sort (·≤·)).map
      (fun e=>(S.weights e,(S.histories e).mean j))))).get j).1=
      ∑ e∈live,S.weights e*(S.histories e).mean j := by
    simp [Vector.get,countedDot_spec,List.map_map,Function.comp_def,rational_sum_sort]
  rw [hv]
  exact Finset.sum_subset (Finset.subset_univ _) (by intro e he hn; simp [hsupport e hn])

theorem countedSparsePrediction_cost {d n : ℕ} (live : Finset (Fin n)) (S : RationalSparseData d n) :
    (countedSparsePrediction live S).2=2*d*live.card := by
  simp [countedSparsePrediction,Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn,countedDot_spec]
  ring

def countedSurrogateExponent {d : ℕ} (lam : ℚ) (g w x : Fin d→ℚ) : ℚ×ℕ :=
  let differences:=Vector.ofFn (fun j:Fin d=>((x j-w j,1):ℚ×ℕ))
  let dot:=countedDot (List.ofFn (fun j=>(g j,((differences.get j).1))))
  let out : ℚ×ℕ := (-lam*(dot.1+lam*(dot.1*dot.1)),5)
  (out.1,(differences.toList.map Prod.snd).sum+dot.2+out.2)

theorem countedSurrogateExponent_value {d : ℕ} (lam : ℚ) (g w x : Fin d→ℚ) :
    (countedSurrogateExponent lam g w x).1= -lam*rationalCoordinateSurrogate lam g w x := by
  simp [countedSurrogateExponent,Vector.get,countedDot_spec,List.map_ofFn,List.sum_ofFn,
    rationalCoordinateSurrogate,dotProduct,pow_two]

theorem countedSurrogateExponent_cost {d : ℕ} (lam : ℚ) (g w x : Fin d→ℚ) :
    (countedSurrogateExponent lam g w x).2=3*d+5 := by
  simp [countedSurrogateExponent,Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn,countedDot_spec]
  ring

def countedSparseExponents {d n : ℕ} (live : Finset (Fin n)) (lam : ℚ)
    (S : RationalSparseData d n) (g w : Fin d→ℚ) : List (Fin n×ℚ)×ℕ :=
  mapWithCosts (fun e=>let q:=countedSurrogateExponent lam g w (S.histories e).mean
    ((e,q.1),q.2)) (live.sort (·≤·))

theorem countedSparseExponents_value {d n : ℕ} (live : Finset (Fin n)) (lam : ℚ)
    (S : RationalSparseData d n) (g : Fin d→ℚ) (e : Fin n) (he : e∈live) :
    rationalLookup (countedSparseExponents live lam S g (rationalSparsePrediction S)).1 e=
      rationalSparseExponents lam S g e := by
  simp only [countedSparseExponents,mapWithCosts_values,countedSurrogateExponent_value]
  rw [rationalLookup_map]
  simp [he,rationalSparseExponents]

theorem countedSparseExponents_cost {d n : ℕ} (live : Finset (Fin n)) (lam : ℚ)
    (S : RationalSparseData d n) (g w : Fin d→ℚ) :
    (countedSparseExponents live lam S g w).2=(3*d+5)*live.card := by
  simp only [countedSparseExponents,mapWithCosts_sum,countedSurrogateExponent_cost,
    List.map_const',List.sum_replicate,Finset.length_sort,nsmul_eq_mul]
  norm_cast
  ring

end Paper254
#print axioms Paper254.countedSparsePrediction_value
#print axioms Paper254.countedSparsePrediction_cost
#print axioms Paper254.countedSparseExponents_value
#print axioms Paper254.countedSparseExponents_cost
