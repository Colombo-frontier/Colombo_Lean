import ShortSchedule254
import AnytimeSchedule254

open scoped BigOperators
namespace Paper254

/-- A materialized list for visiting exactly the current history/scale keys. -/
def shortLiveList (T K t : ℕ) : List (HistoryExpert T K) :=
  ((shortActiveHistories t).sort (· ≤ ·)).flatMap (fun i=>
    if h : 0 < i ∧ i ≤ T+1 then
      (List.finRange (K+1)).map (fun k=>(⟨i-1,by omega⟩,k))
    else [])

theorem mem_shortLiveList (T K t : ℕ) (e : HistoryExpert T K) :
    e∈shortLiveList T K t ↔ e∈liveExperts T K t := by
  rw [←shortLiveExperts_eq]
  simp only [shortLiveList,shortLiveExperts,List.mem_flatMap,Finset.mem_biUnion,
    Finset.mem_sort]
  apply exists_congr
  intro i
  apply and_congr_right
  intro _
  split_ifs with h
  · simp only [List.mem_map,Finset.mem_image,List.mem_finRange,Finset.mem_univ,true_and]
  · simp

theorem flatMap_length_bound {α β : Type*} (f : α→List β) (xs : List α) (N : ℕ)
    (h : ∀ x∈xs,(f x).length≤N) : (xs.flatMap f).length≤xs.length*N := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    have hx := h x (by simp)
    have ht := ih (fun a ha=>h a (by simp [ha]))
    omega

theorem shortLiveList_length (T K t : ℕ) :
    (shortLiveList T K t).length≤5*(Nat.log 2 t+1)*(K+1) := by
  have hh := flatMap_length_bound (fun i=>
    if h : 0 < i ∧ i ≤ T+1 then
      (List.finRange (K+1)).map (fun k : Fin (K+1)=>((⟨i-1,by omega⟩,k) : HistoryExpert T K))
    else []) ((shortActiveHistories t).sort (· ≤ ·)) (K+1) (by
      intro i _
      dsimp only
      split_ifs <;> simp)
  change (shortLiveList T K t).length≤_ at hh
  simp only [Finset.length_sort,shortActiveHistories_eq] at hh
  exact hh.trans (Nat.mul_le_mul_right (K+1) (activeHistories_card t))

/-- Counts the calls actually made by the recursive list traversal.
The internal arithmetic/bit cost of the supplied update is a separate layer. -/
def mapWithCallCount {α β : Type*} (f : α→β) : List α→List β×ℕ
  | [] => ([],0)
  | x::xs => let rest := mapWithCallCount f xs
             (f x::rest.1,rest.2+1)

theorem mapWithCallCount_spec {α β : Type*} (f : α→β) (xs : List α) :
    mapWithCallCount f xs=(xs.map f,xs.length) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [mapWithCallCount,ih]

def visitLiveHistories {α : Type*} (T K t : ℕ)
    (state : HistoryExpert T K→α) (update : HistoryExpert T K→α→α) :
    List (HistoryExpert T K×α)×ℕ :=
  mapWithCallCount (fun e=>(e,update e (state e))) (shortLiveList T K t)

theorem visitLiveHistories_values {α : Type*} (T K t : ℕ)
    (state : HistoryExpert T K→α) (update : HistoryExpert T K→α→α)
    (e : HistoryExpert T K) (v : α) :
    (e,v)∈(visitLiveHistories T K t state update).1 ↔
      e∈liveExperts T K t ∧ v=update e (state e) := by
  rw [visitLiveHistories,mapWithCallCount_spec]
  simp only [List.mem_map,Prod.mk.injEq]
  constructor
  · rintro ⟨j,hj,hje,hv⟩
    subst j
    exact ⟨(mem_shortLiveList T K t e).mp hj,hv.symm⟩
  · rintro ⟨he,hv⟩
    exact ⟨e,(mem_shortLiveList T K t e).mpr he,rfl,hv.symm⟩

theorem visitLiveHistories_calls {α : Type*} (T K t : ℕ)
    (state : HistoryExpert T K→α) (update : HistoryExpert T K→α→α) :
    (visitLiveHistories T K t state update).2≤5*(Nat.log 2 t+1)*(K+1) := by
  rw [visitLiveHistories,mapWithCallCount_spec]
  exact shortLiveList_length T K t

theorem shortLiveList_log_bound (T t : ℕ) (hT : 0<T) (ht : t≤T) :
    ((shortLiveList T (scaleCount T) t).length:ℝ)≤20*logFactor T^2 := by
  have hh := shortLiveList_length T (scaleCount T) t
  have hm : Nat.log 2 t≤Nat.log 2 T := Nat.log_mono_right ht
  have hn : (shortLiveList T (scaleCount T) t).length≤5*(scaleCount T+1)^2 := by
    dsimp [scaleCount] at *
    nlinarith
  have hr : ((shortLiveList T (scaleCount T) t).length:ℝ)≤5*(scaleCount T+1:ℝ)^2 :=
    by exact_mod_cast hn
  have hl := scaleDepth_log_bound T hT
  have hz := logFactor_ge_one T hT
  nlinarith [show (0:ℝ)≤scaleCount T+1 by positivity]

def totalHistoryCalls (T : ℕ) : ℕ :=
  ∑ t∈Finset.range T,(shortLiveList T (scaleCount T) (t+1)).length

theorem totalHistoryCalls_bound (T : ℕ) (hT : 0<T) :
    (totalHistoryCalls T:ℝ)≤20*T*logFactor T^2 := by
  have hh := Finset.sum_le_sum (s:=Finset.range T)
    (f:=fun t=>((shortLiveList T (scaleCount T) (t+1)).length:ℝ))
    (g:=fun _=>20*logFactor T^2)
    (fun t ht=>shortLiveList_log_bound T (t+1) hT (by have := Finset.mem_range.mp ht; omega))
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hh
  push_cast [totalHistoryCalls]
  nlinarith

/-- Cost composition at the update-oracle boundary, not a bit-complexity
claim about an unanalysed implementation of that oracle. -/
theorem history_oracle_cost_composition (T : ℕ) (hT : 0<T) (C : ℝ) (hC : 0≤C) :
    (totalHistoryCalls T:ℝ)*C≤20*T*logFactor T^2*C :=
  mul_le_mul_of_nonneg_right (totalHistoryCalls_bound T hT) hC

theorem logFactor_mono_cost {H T : ℕ} (hH : 0<H) (hHT : H≤T) : logFactor H≤logFactor T := by
  unfold logFactor
  apply add_le_add_left
  apply Real.log_le_log (by positivity)
  exact_mod_cast (Nat.mul_le_mul_left 2 hHT)

theorem anytimeHistoryCalls_bound (T : ℕ) (hT : 0<T) :
    (∑ j∈Finset.range (Nat.log 2 T+1),(totalHistoryCalls (2^j):ℝ))≤
      40*T*logFactor T^2 := by
  have hh : ∀ j∈Finset.range (Nat.log 2 T+1),
      (totalHistoryCalls (2^j):ℝ)≤20*(2:ℝ)^j*logFactor T^2 := by
    intro j hj
    have hjle : j≤Nat.log 2 T := by have := Finset.mem_range.mp hj; omega
    have hpow : (2:ℕ)^j≤T :=
      (Nat.pow_le_pow_right (by norm_num) hjle).trans (Nat.pow_log_le_self 2 hT.ne')
    have hl := logFactor_mono_cost (by positivity : 0<(2:ℕ)^j) hpow
    have hl0 := logFactor_ge_one (2^j) (by positivity)
    have hb := totalHistoryCalls_bound (2^j) (by positivity)
    push_cast at hb
    have hsq : logFactor (2^j)^2≤logFactor T^2 := by nlinarith
    exact hb.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
  have hs := Finset.sum_le_sum hh
  have hp := doubling_planned_time T hT
  have he : (∑ j∈Finset.range (Nat.log 2 T+1),20*(2:ℝ)^j*logFactor T^2)=
      20*(∑ j∈Finset.range (Nat.log 2 T+1),(2:ℝ)^j)*logFactor T^2 := by
    rw [←Finset.sum_mul,←Finset.mul_sum]
  rw [he] at hs
  have hb := mul_le_mul_of_nonneg_right hp (sq_nonneg (logFactor T))
  nlinarith

end Paper254
#print axioms Paper254.visitLiveHistories_values
#print axioms Paper254.totalHistoryCalls_bound
#print axioms Paper254.anytimeHistoryCalls_bound
#eval (Paper254.visitLiveHistories 1000 9 1000 (fun _=>0) (fun _ s=>s+1)).2
