import ExactMasterCost254

noncomputable section
open scoped BigOperators
open Matrix
namespace Paper254

def countedRealPrediction {d T K : ℕ} {D : ℝ} {W : Domain d D}
    (live : Finset (HistoryExpert T K)) (S : SparseMasterState W T K) : Coordinates d×ℕ :=
  countedRealVector (fun j=>countedRealDot (live.toList.map
    (fun e=>(S.weights.weight e,(S.histories e).mean j))))

theorem countedRealPrediction_value {d T K : ℕ} {D : ℝ} {W : Domain d D}
    (live : Finset (HistoryExpert T K)) (S : SparseMasterState W T K)
    (hsupport : ∀ e,e∉live→S.weights.weight e=0) :
    (countedRealPrediction live S).1=S.prediction.val := by
  funext j
  have hv : (countedRealPrediction live S).1 j=
      ∑ e∈live,S.weights.weight e*(S.histories e).mean j := by
    simp [countedRealPrediction,countedRealVector_value,countedRealDot_spec,
      List.map_map,Function.comp_def,real_sum_toList]
  rw [hv]
  have hp : S.prediction.val j=∑ e,S.weights.weight e*(S.histories e).mean j := by
    have hh (s : Finset (HistoryExpert T K)) :
        (∑ e∈s,S.weights.weight e • WithLp.toLp 2 (S.histories e).mean) j=
          ∑ e∈s,S.weights.weight e*(S.histories e).mean j := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert e s he ih => simp [he,ih]
    exact hh Finset.univ
  rw [hp]
  exact Finset.sum_subset (Finset.subset_univ _) (by intro e he hn; simp [hsupport e hn])

theorem countedRealPrediction_cost {d T K : ℕ} {D : ℝ} {W : Domain d D}
    (live : Finset (HistoryExpert T K)) (S : SparseMasterState W T K) :
    (countedRealPrediction live S).2=2*d*live.card := by
  simp [countedRealPrediction,countedRealVector,Vector.toList_ofFn,List.map_ofFn,
    List.sum_ofFn,countedRealDot_spec]
  ring

def countedRealSurrogate {d : ℕ} (gamma : ℝ) (g w x : Coordinates d) : ℝ×ℕ :=
  let differences := countedRealVector (fun j=>(x j-w j,1))
  let dot := countedRealDot (List.ofFn (fun j=>(g j,differences.1 j)))
  (dot.1+(gamma/2)*(dot.1*dot.1),differences.2+dot.2+4)

theorem countedRealSurrogate_value {d : ℕ} (gamma : ℝ) (g w x : Coordinates d) :
    (countedRealSurrogate gamma g w x).1=coordinateSurrogate gamma g w x := by
  simp [countedRealSurrogate,countedRealVector_value,countedRealDot_spec,
    List.map_ofFn,List.sum_ofFn,coordinateSurrogate,dotProduct,pow_two]

theorem countedRealSurrogate_cost {d : ℕ} (gamma : ℝ) (g w x : Coordinates d) :
    (countedRealSurrogate gamma g w x).2=3*d+4 := by
  simp [countedRealSurrogate,countedRealVector,Vector.toList_ofFn,List.map_ofFn,
    List.sum_ofFn,countedRealDot_spec]
  omega

structure ExactRoundData (d T K : ℕ) where
  prediction : Coordinates d
  gradient : Coordinates d
  histories : List (HistoryExpert T K×PrecisionGaussian d)
  weights : List (HistoryExpert T K×ℝ)

def countedExactRound {d T K : ℕ} {D : ℝ} (W : Domain d D)
    (primitive : ExactRankOneFloorPrimitive d) (projection : ExactProjectionPrimitive W)
    (exponential : ExactExpPrimitive) (gradientCost : ℕ) (S : SparseMasterState W T K)
    (lam : ℝ) (hlam : 0≤lam) (q : Fin (K+1)→ℝ) (hq : ∀ k,0<q k)
    (t : Fin T) (query : Coordinates d→Coordinates d) : ExactRoundData d T K×ℕ :=
  let predicted := countedRealPrediction (liveExperts T K (t.val+1)) S
  let gradientRows := Vector.ofFn (query predicted.1)
  let g := fun j=>gradientRows.get j
  let histories := visitExactHistories W T K (t.val+1) primitive projection
    S.histories lam hlam q hq g predicted.1
  let alpha := 1/(t.val+2:ℝ)
  let prior := birthPrior T K ⟨t.val+1,by omega⟩
  let master := countedRealMaster exponential (liveExperts T K (t.val+1))
    (liveExperts T K (t.val+2)) S.weights.weight prior.weight lam alpha
    (fun e=>countedRealSurrogate (2*lam) g predicted.1 (S.histories e).mean)
  (⟨predicted.1,g,histories.1,master.1⟩,predicted.2+gradientCost+histories.2+master.2+5)

theorem countedExactRound_prediction {d T K : ℕ} {D : ℝ} (W : Domain d D)
    (primitive : ExactRankOneFloorPrimitive d) (projection : ExactProjectionPrimitive W)
    (exponential : ExactExpPrimitive) (gradientCost : ℕ) (S : SparseMasterState W T K)
    (lam : ℝ) (hlam : 0≤lam) (q : Fin (K+1)→ℝ) (hq : ∀ k,0<q k)
    (t : Fin T) (query : Coordinates d→Coordinates d)
    (hsupport : ∀ e,e∉liveExperts T K (t.val+1)→S.weights.weight e=0) :
    (countedExactRound W primitive projection exponential gradientCost S lam hlam q hq t query).1.prediction=
      S.prediction.val := countedRealPrediction_value _ S hsupport

theorem countedExactRound_weights {d T K : ℕ} {D G eta : ℝ} (W : Domain d D)
    (hD : 0<D) (hG : 0<G) (heta : 0<eta)
    (primitive : ExactRankOneFloorPrimitive d) (projection : ExactProjectionPrimitive W)
    (exponential : ExactExpPrimitive) (gradientCost : ℕ) (S : SparseMasterState W T K)
    (q : Fin (K+1)→ℝ) (hq : ∀ k,0<q k) (t : Fin T) (query : Coordinates d→Coordinates d)
    (hsupport : ∀ e,e∉liveExperts T K (t.val+1)→S.weights.weight e=0) :
    realLookup (countedExactRound W primitive projection exponential gradientCost S
      (curvature D G eta/2) ((div_pos (curvature_pos D G eta hD hG heta) (by norm_num)).le)
      q hq t query).1.weights=
      (S.stepWithGradient hG heta hD q hq t (WithLp.toLp 2 (query S.prediction.val))).weights.weight := by
  have ha : (0:ℝ)<1/(t.val+2:ℝ) := by positivity
  have hb : (1:ℝ)/(t.val+2:ℝ)≤1 := by
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg t.val (α:=ℝ)]
  simp only [countedExactRound,countedRealPrediction_value _ S hsupport]
  have hg : (fun j=>(Vector.ofFn (query S.prediction.val)).get j)=query S.prediction.val := by
    funext j; simp [Vector.get]
  rw [hg,countedRealMaster_value exponential _ _ S.weights _ _ _ _ ha hb
    (fun j hj=>birthPrior_live ⟨t.val+1,by omega⟩ j hj) hsupport]
  simp only [countedRealSurrogate_value]
  have he : 2*(curvature D G eta/2)=curvature D G eta := by ring
  rw [he]
  rfl

theorem countedExactRound_histories {d T K : ℕ} {D G eta : ℝ} (W : Domain d D)
    (hD : 0<D) (hG : 0<G) (heta : 0<eta)
    (primitive : ExactRankOneFloorPrimitive d) (projection : ExactProjectionPrimitive W)
    (exponential : ExactExpPrimitive) (gradientCost : ℕ) (S : SparseMasterState W T K)
    (q : Fin (K+1)→ℝ) (hq : ∀ k,0<q k) (t : Fin T) (query : Coordinates d→Coordinates d)
    (hsupport : ∀ e,e∉liveExperts T K (t.val+1)→S.weights.weight e=0) :
    (countedExactRound W primitive projection exponential gradientCost S
      (curvature D G eta/2) ((div_pos (curvature_pos D G eta hD hG heta) (by norm_num)).le)
      q hq t query).1.histories=
      (shortLiveList T K (t.val+1)).map (fun e=>(e,
        (S.stepWithGradient hG heta hD q hq t (WithLp.toLp 2 (query S.prediction.val))).histories e)) := by
  simp only [countedExactRound,countedRealPrediction_value _ S hsupport]
  have hg : (fun j=>(Vector.ofFn (query S.prediction.val)).get j)=query S.prediction.val := by
    funext j; simp [Vector.get]
  rw [hg]
  exact visitExactHistories_actual S hD hG heta q hq t (WithLp.toLp 2 (query S.prediction.val)) primitive projection

theorem countedExactRound_cost {d T K : ℕ} {D : ℝ} (W : Domain d D)
    (primitive : ExactRankOneFloorPrimitive d) (projection : ExactProjectionPrimitive W)
    (exponential : ExactExpPrimitive) (gradientCost : ℕ) (S : SparseMasterState W T K)
    (lam : ℝ) (hlam : 0≤lam) (q : Fin (K+1)→ℝ) (hq : ∀ k,0<q k)
    (t : Fin T) (query : Coordinates d→Coordinates d) :
    (countedExactRound W primitive projection exponential gradientCost S lam hlam q hq t query).2≤
      (shortLiveList T K (t.val+1)).length*(6*d^2+7*d+3+primitive.bound+projection.bound)+
      (liveExperts T K (t.val+1)).card*(5*d+exponential.bound+9)+
      6*(liveExperts T K (t.val+2)).card+gradientCost+5 := by
  let pred := (countedRealPrediction (liveExperts T K (t.val+1)) S).1
  let g := fun j=>(Vector.ofFn (query pred)).get j
  have hh := visitExactHistories_cost W T K (t.val+1) primitive projection S.histories
    lam hlam q hq g pred
  have hm := countedRealMaster_cost exponential (liveExperts T K (t.val+1))
    (liveExperts T K (t.val+2)) S.weights.weight (birthPrior T K ⟨t.val+1,by omega⟩).weight
    lam (1/(t.val+2:ℝ)) (fun e=>countedRealSurrogate (2*lam) g pred (S.histories e).mean)
    (3*d+4) (by intro e he; rw [countedRealSurrogate_cost])
  simp only [countedExactRound,countedRealPrediction_cost]
  dsimp [pred,g] at hh hm
  nlinarith

end Paper254
#print axioms Paper254.countedExactRound_weights
#print axioms Paper254.countedExactRound_histories
#print axioms Paper254.countedExactRound_cost
