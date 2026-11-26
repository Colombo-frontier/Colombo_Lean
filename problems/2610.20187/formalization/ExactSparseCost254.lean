import ExactHistoryCost254

noncomputable section
open scoped BigOperators
namespace Paper254

def visitExactHistories {d : ℕ} {D : ℝ} (W : Domain d D)
    (T K t : ℕ) (primitive : ExactRankOneFloorPrimitive d)
    (projection : ExactProjectionPrimitive W) (states : HistoryExpert T K→PrecisionGaussian d)
    (lam : ℝ) (hlam : 0≤lam) (q : Fin (K+1)→ℝ) (hq : ∀ k,0<q k)
    (g w : Coordinates d) : List (HistoryExpert T K×PrecisionGaussian d)×ℕ :=
  mapWithCosts (fun e=>
    let next := countedExactHistory W primitive projection (states e) lam (q e.2) hlam (hq e.2) g w
    ((e,next.1),next.2)) (shortLiveList T K t)

theorem visitExactHistories_value {d : ℕ} {D : ℝ} (W : Domain d D)
    (T K t : ℕ) (primitive : ExactRankOneFloorPrimitive d)
    (projection : ExactProjectionPrimitive W) (states : HistoryExpert T K→PrecisionGaussian d)
    (lam : ℝ) (hlam : 0≤lam) (q : Fin (K+1)→ℝ) (hq : ∀ k,0<q k) (g w : Coordinates d) :
    (visitExactHistories W T K t primitive projection states lam hlam q hq g w).1=
      (shortLiveList T K t).map (fun e=>(e,(states e).historyUpdate W lam (q e.2) hlam (hq e.2) g w)) := by
  rw [visitExactHistories,mapWithCosts_values]
  apply List.map_congr_left
  intro e he
  exact congrArg (fun z=>(e,z)) (countedExactHistory_value W primitive projection
    (states e) lam (q e.2) hlam (hq e.2) g w)

theorem visitExactHistories_cost {d : ℕ} {D : ℝ} (W : Domain d D)
    (T K t : ℕ) (primitive : ExactRankOneFloorPrimitive d)
    (projection : ExactProjectionPrimitive W) (states : HistoryExpert T K→PrecisionGaussian d)
    (lam : ℝ) (hlam : 0≤lam) (q : Fin (K+1)→ℝ) (hq : ∀ k,0<q k) (g w : Coordinates d) :
    (visitExactHistories W T K t primitive projection states lam hlam q hq g w).2≤
      (shortLiveList T K t).length*(6*d^2+7*d+3+primitive.bound+projection.bound) := by
  apply mapWithCosts_bound
  intro e he
  exact countedExactHistory_cost W primitive projection (states e) lam (q e.2) hlam (hq e.2) g w

theorem exact_sparse_history_total_cost {d : ℕ} {D : ℝ} (W : Domain d D)
    (T : ℕ) (hT : 0<T) (primitive : ExactRankOneFloorPrimitive d)
    (projection : ExactProjectionPrimitive W)
    (states : ℕ→HistoryExpert T (scaleCount T)→PrecisionGaussian d)
    (lam : ℝ) (hlam : 0≤lam) (q : Fin (scaleCount T+1)→ℝ) (hq : ∀ k,0<q k)
    (g w : ℕ→Coordinates d) :
    (∑ t∈Finset.range T,
      ((visitExactHistories W T (scaleCount T) (t+1) primitive projection (states t)
        lam hlam q hq (g t) (w t)).2:ℝ))≤
      20*T*logFactor T^2*(6*d^2+7*d+3+primitive.bound+projection.bound) := by
  let B := 6*d^2+7*d+3+primitive.bound+projection.bound
  have hb : (∑ t∈Finset.range T,
      (visitExactHistories W T (scaleCount T) (t+1) primitive projection (states t)
        lam hlam q hq (g t) (w t)).2)≤totalHistoryCalls T*B := by
    calc
      _≤∑ t∈Finset.range T,(shortLiveList T (scaleCount T) (t+1)).length*B :=
        Finset.sum_le_sum (fun t ht=>visitExactHistories_cost W T (scaleCount T) (t+1)
          primitive projection (states t) lam hlam q hq (g t) (w t))
      _=totalHistoryCalls T*B := by rw [←Finset.sum_mul]; rfl
  have hr : (∑ t∈Finset.range T,
      ((visitExactHistories W T (scaleCount T) (t+1) primitive projection (states t)
        lam hlam q hq (g t) (w t)).2:ℝ))≤(totalHistoryCalls T:ℝ)*B := by exact_mod_cast hb
  simpa [B,Nat.cast_add,Nat.cast_mul,Nat.cast_pow] using
    hr.trans (history_oracle_cost_composition T hT B (by positivity))

/-- The values in the counted traversal are the histories used by the
actual gradient-driven master update, for every key updated that round. -/
theorem visitExactHistories_actual {d T K : ℕ} {D G eta : ℝ} {W : Domain d D}
    (S : SparseMasterState W T K) (hD : 0<D) (hG : 0<G) (heta : 0<eta)
    (q : Fin (K+1)→ℝ) (hq : ∀ k,0<q k) (t : Fin T) (g : Space d)
    (primitive : ExactRankOneFloorPrimitive d) (projection : ExactProjectionPrimitive W) :
    (visitExactHistories W T K (t.val+1) primitive projection S.histories
      (curvature D G eta/2) ((div_pos (curvature_pos D G eta hD hG heta) (by norm_num)).le)
      q hq g S.prediction.val).1=
      (shortLiveList T K (t.val+1)).map (fun e=>(e,
        (S.stepWithGradient hG heta hD q hq t g).histories e)) := by
  rw [visitExactHistories_value]
  apply List.map_congr_left
  intro e he
  have he' := (mem_shortLiveList T K (t.val+1) e).mp he
  simp [SparseMasterState.stepWithGradient,he']

end Paper254
#print axioms Paper254.visitExactHistories_actual
#print axioms Paper254.exact_sparse_history_total_cost
